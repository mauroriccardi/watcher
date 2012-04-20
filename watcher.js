/*
    Watcher, an program to convert to PGN on the fly a game played on xboard/winboard and send it via ftp
    Copyright (C) 2012  Mauro Riccardi

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    as published by the Free Software Foundation; either version 2
    of the License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.

*/

var debug = false;

var parser;

var http = require('http');
var fs = require('fs');
var FTPClient = require('./node-ftp');
var tty = require('tty');

var hostname;
var username;
var password;
var filename;
var remotefilename;
var delay = 1;
var oldlen = 0;
var oldlenbuf = 0;

var cumulative_results = {};

var square = {};
var i = 0;

var upcase = {'q': 'Q', 'n': 'N', 'r': 'R', 'b': 'B', '': '', 'k': 'K', 'Q': 'Q', 'N': 'N', 'R': 'R', 'B': 'B', 'K': 'K'};
var invert_result = {'1-0': '0-1', '1/2-1/2': '1/2-1/2', '0-1': '1-0', '*': '*'};

var knightjumps = [10,-6,6,-10,17,-15,15,-17];
var knightjumps88 = [18,-14,14,-18,33,-31,31,-33];
var knightshifts = {file: [-32,-16,16,31], rank: [-4,-2,2,4]};

var files = ['a','b','c','d','e','f','g','h'];

console.log('Watcher version 0.1, Copyright (C) 2012 Mauro Riccardi');
console.log('Watcher comes with ABSOLUTELY NO WARRANTY.');
console.log('This is free software, and you are welcome');
console.log('to redistribute it under certain conditions.\nSee file COPYING and/or license details in the source for details.');

// function show_board(board) {
    // var res = '';
    // var d;
    
    // for(var j = 7; j>=0; j--) {
        // for(var i = 0;i<8;i++) {
            // if(board[i+8*j] == null) d = ' ';
            // else if(board[i+8*j] == '') d = 'P';
            // else d = board[i+8*j];
            // res += d+' ';
        // }
        // res += '\n';
    // }
    
    // return res;
// }

for(var rank = 1; rank<=8; rank++) {
    files.forEach(function(file) {
        square[file+rank] = i++;
    });
};

function pgn_date(date) {
    return date.getUTCFullYear()+'.'+(date.getUTCMonth()+1)+'.'+date.getUTCDate();
};

function Game(tags, moves) {
    this.tags = tags || {};
    this.moves = moves || '';
};
Game.prototype.toString =
    function () {
        var res = '';
        
        res += '[White "'+(this.tags.white || '?')+'"]\n';
        res += '[Black "'+(this.tags.black || '?')+'"]\n';
        res += '[Date "'+pgn_date(new Date())+'"]\n';
        res += '[Result "'+(this.tags.result || '*')+'"]\n\n';
        res += this.moves;
        res += '\n\n'+(this.tags.result || '*')+' '+(this.tags.motivation || '')+'\n\n';
        
        return res;
    };
Game.prototype.pushTag = 
    function(key,value) {
        this.tags[key] = value;
    };
Game.prototype.pullTag =
    function(key) {
        return this.tags.key;
    };
Game.prototype.refresh =
    function(keeptags) {
        if(!keeptags) this.tags = {};
        else {
            for(key in this.tags) {
                if(key in keeptags) continue;
                else delete this.tags[key];
            }
        }
        this.moves = '';
    };
Game.prototype.firstis =
    function(player) {
        this.first = player;
        if(this.tags.whitefirst) this.tags.white = player;
        else if(this.tags.blackfirst) this.tags.black = player;
    };
Game.prototype.secondis =
    function(player) {
        this.second = player;
        if(this.tags.whitefirst) this.tags.black = player;
        else if(this.tags.blackfirst) this.tags.white = player;
    };
Game.prototype.firstiswhite =
    function() {
        if(this.first) this.tags.white = this.tags.white || this.first;
        if(this.second) this.tags.black = this.tags.black || this.second;
        this.tags.whitefirst = 1;
    };
Game.prototype.firstisblack =
    function() {
        if(this.first) this.tags.black = this.tags.black || this.first;
        if(this.second) this.tags.white = this.tags.white || this.second;
        this.tags.blackfirst = 1;
    };    
    
var options;
var parsedopts = {};

try {
    options = fs.readFileSync('watcher.ini','utf8');
} catch(e) {
    throw e;
}

var optre = /([a-z_]+)\s*:\s*([\w\/\\][\w:\\\/ .\-]+)/g;
var admittedtokens = ['username','password','movesfilename','remotefilename','hostname','delay'];
var option;
while(option = optre.exec(options)) {
    var str = option[1] || 'invalid';
    var found = false;
    
    admittedtokens.forEach(function(token) {
        if(str === token) found = true;
    });
    
    if(found)
        parsedopts[str] = option[2] || '';
}

password = parsedopts.password || '';
username = parsedopts.username || 'anonymous';
filename = parsedopts.movesfilename || '';
remotefilename = parsedopts.remotefilename || 'live.pgn';
delay = parsedopts.delay || 1;
hostname = parsedopts.hostname || '127.0.0.1';

function strtime(time) {
    var s = time % 60;
    time = (time - s)/60;
    var m = time % 60;
    time = (time - m)/60;
    return(time+':'+(m<10?'0'+m:m)+':'+(s<10?'0'+s:s));
}

function parsexboard(buffer) {
    var board0 = [
                  'r', 'n', 'b', 'q', 'k', 'b', 'n', 'r',
                  '', '', '', '', '', '', '', '',
                  null, null, null, null, null, null, null, null, 
                  null, null, null, null, null, null, null, null, 
                  null, null, null, null, null, null, null, null, 
                  null, null, null, null, null, null, null, null, 
                  '', '', '', '', '', '', '', '',
                  'R', 'N', 'B', 'Q', 'K', 'B', 'N', 'R',
                ];
    var board;
    var epsquare = null;
    var lastwasengine = null;
    
    var r = /\n?(\d+)\s*(<|>)(first|second)\s*:[ ]*([^\r\n]+)\r?\n/g; // 1: timestamp, 
                                                          // 2: direction (<=from eng|>=to eng), 
                                                          // 3: which engine, 
                                                          // 4: command passed to/from
    var m;
    var n;
    var tomove = 0;
    var ply = 0;
    var timestamp, elapsed_time;
    var res = {s: '', list: {byplayer: {}, bycols: {}}, pending: true};
    
    var game = new Game();
    
    board = [];
    for(var i=0;i<board0.length;i++) board[i] = board0[i];
    
    timestamp = 0;
    elapsed_time = null;
    
    while( m = r.exec(buffer) ) {
        
        timestamp = m[1];
        //console.log('match: '+m[0]);

        if(m[2]==='<') { // engine is sending something: extract only the move, as engine authors take liberties with the protocol...
            
            // match move in winboard format
            n = /move\s+([a-h][1-8])([a-h][1-8])([qrnb]?)/.exec(m[4]); // 1: from square (like d2), 
                                                                       // 2: to square (like d4), 
                                                                       // 3: promotion to what piece [qrnb] (only in case of promotion)
            if(n) {
                if(m[3][0]=='s') continue;
                if(lastwasengine!=null && lastwasengine) {
                    // console.log('error, engine sent two moves in a row');
                    // console.log(n);
                    // console.log('**************');
                    continue;  // engine has sent two moves in a row: skip this line
                }
                lastwasengine = true;
                if(ply==0) game.firstiswhite();
                else if(ply==1) game.firstisblack();
            } else if(n = /myname=[^\w\d\r\n]([\w\d\-. ]+)/.exec(m[4])) {
                if(m[3][0]=='f') game.firstis(n[1]);
                else game.secondis(n[1]);
                continue;
            }
        } else if(m[2]==='>') {
            var s;
            
            if(m[4].match(/new/)) { 
                if(m[3][0] == 's') continue;
                if(ply>0 && res.pending) {
                    var player = game.tags.white;
                    if(player) {
                        res.list.byplayer[player] = res.list.byplayer[player] || {'1-0': 0, '0-1': 0, '1/2-1/2': 0, '*': 0};
                        res.list.byplayer[player][game.tags.result]++;
                    }
                    player = game.tags.black
                    if(player) {
                        res.list.byplayer[player] = res.list.byplayer[player] || {'1-0': 0, '0-1': 0, '1/2-1/2': 0, '*': 0};
                        res.list.byplayer[player][invert_result[game.tags.result]]++;
                    }
                    if(game.tags.result in res.list.bycols) res.list.bycols[game.tags.result]++;
                    else res.list.bycols[game.tags.result] = 1;
                    res.s += game.toString();
                };
                res.pending = true;
                game.refresh({first: 1, second: 1});
                for(var i=0;i<board0.length;i++) board[i] = board0[i];
                epsquare = null;
                ply = 0;
                tomove = 0;
                lastwasengine = null;
                continue;
            } else if(s = /name\s+([\w\d\-. ]+)/.exec(m[4])) {
                if(m[3][0]=='f') game.secondis(s[1]);
                else game.firstis(s[1]);
                continue;
            } else if(s = /result\s+(1-0|0-1|1\/2-1\/2|\*)[ ]*({[\w\d \-._]*})/.exec(m[4])) {
                if(m[3][0] == 's') continue;
                game.tags.result = s[1];
                game.tags.motivation = s[2] || '';
                
                if(ply>0 && res.pending) {
                    var player = game.tags.white;
                    if(player) {
                        res.list.byplayer[player] = res.list.byplayer[player] || {'1-0': 0, '0-1': 0, '1/2-1/2': 0, '*': 0};
                        res.list.byplayer[player][game.tags.result]++;
                    }
                    player = game.tags.black
                    if(player) {
                        res.list.byplayer[player] = res.list.byplayer[player] || {'1-0': 0, '0-1': 0, '1/2-1/2': 0, '*': 0};
                        res.list.byplayer[player][invert_result[game.tags.result]]++;
                    }
                    if(game.tags.result in res.list.bycols) res.list.bycols[game.tags.result]++;
                    else res.list.bycols[game.tags.result] = 1;

                    res.s += game.toString();
                    res.pending = false;
                };
                continue;
            }
            if(m[3][0]=='s') continue;
            n = /usermove\s+([a-h][1-8])([a-h][1-8])([qrnb]?)/.exec(m[4]);
            if(n) {
                lastwasengine = true;
                if(ply==0) game.firstiswhite();
                else if(ply==1) game.firstisblack();
            } else if(n = /([a-h][1-8])([a-h][1-8])([qrnb]?)/.exec(m[4])) {
                if(lastwasengine!=null && !lastwasengine) {
                    // console.log('error, gui sent two moves in a row');
                    // console.log(n);
                    // console.log('**************');
                    continue;
                }
                lastwasengine = false;
            }
        } else continue;

        if(!n) { // not a move
            continue;
        } else {
            var from = square[n[1]];
            var fromn = n[1];
            var to = square[n[2]];
            var ton = n[2];
            var piece = upcase[board[from]];
            var casedpiece = board[from];
            var promotion;
            var enpassant = false;
            var capture;
            var castle = false;
            var depth;
            var score;
            var time;
            
            // console.log(show_board(board));
            // console.log(n);
            
            if(board[to]!=null) capture = true;
            else capture = false;
            
            if(piece=='' && epsquare && ton === epsquare) enpassant = true;
            else enpassant = false;

            if(n[3]) promotion = true;
            else promotion = false;

            if(ply%2==0) game.moves += ' '+(ply/2+1)+'. ';
            else game.moves += ' ';
            
            
            if(piece=='K' && /e[18][gc][18]/.exec(fromn+ton)) castle = true;
            else castle = false;
            
            if(promotion) {
                game.moves += (capture?(fromn[0]+'x'):'') + ton + '=' + upcase[n[3]];
                board[from] = null;
                board[to] = tomove==1?n[3]:upcase[n[3]];
                continue;
            } else if(castle) {
                var ft = ton[1];
                if(ton[0]=='g') {
                    game.moves += 'O-O';
                    board[square['h'+ft]] = null;
                    board[square['f'+ft]] = (tomove==0?'r':'R');
                } else {
                    game.moves += 'O-O-O';
                    board[square['a'+ft]] = null;
                    board[square['d'+ft]] = (tomove==0?'r':'R');
                }
            } else if(enpassant) {
                game.moves += fromn[0]+'x'+ton;
                board[square[ton[0]+fromn[1]]] = null;
                board[to] = '';
            } else {
                var total = 0;
                var same_file = 0;
                var same_rank = 0;
                
                game.moves += (piece=='' && capture)?fromn[0]:piece;
                
                if(piece=='') {
                    var fr = fromn[1];
                    var tr = ton[1];
                    if(fr=='2' && tr=='4') epsquare = ton[0]+'3';
                    else if(fr=='7' && tr=='5') epsquare = ton[0]+'6';
                    else epsquare = null;
                } else if(piece=='N') {
                    var to88 = to + (to & 56);
                    knightjumps88.forEach(function(jump) {
                        var dum = to88 + jump;
                        
                        if(dum>=0 && dum<128 && (dum & 0x88)==0) {
                            if(board[((dum >> 1) & 56)+(dum & 7)] == casedpiece) {
                                if((dum&7)==(from&7)) same_file++;
                                if((dum>>4)&7==((from>>3)&7)) same_rank++;
                                total++;
                            }
                        }
                    });
                }
                if(piece=='R' || piece=='Q') {
                    var to88 = to + (to & 56);
                    var dum;
                    
                    for(x=to88+1; x<128 && !(x & 0x88); x++) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            same_rank++;
                            total++;
                        }
                        if(dum!=null) break;
                    }
                    for(x=to88-1; x>=0 && !(x & 0x88); x--) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            same_rank++;
                            total++;
                        }
                        if(dum!=null) break;
                    }
                    for(x=to88+16; x<128 && !(x & 0x88); x+=16) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            same_file++;
                            total++;
                        }
                        if(dum!=null) break;
                    }
                    for(x=to88-16; x>=0 && !(x & 0x88); x-=16) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            same_file++;
                            total++;
                        }
                        if(dum!=null) break;
                    }                   
                }
                if(piece=='B' || piece=='Q') {
                    var to88 = to + (to & 56);
                    var dum;
                    
                    for(x=to88+17; x<128 && !(x & 0x88); x+=17) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            if((dum & 7) == (from & 7)) same_file++;
                            if(((dum>>4) & 7) == ((from>>3) & 7)) same_rank++;
                            total++;
                        }
                        if(dum!=null) break;
                    }
                    for(x=to88-17; x>=0 && !(x & 0x88); x-=17) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            if((dum & 7) == (from & 7)) same_file++;
                            if(((dum>>4) & 7) == ((from>>3) & 7)) same_rank++;
                            total++;
                        }
                        if(dum!=null) break;
                    }
                    for(x=to88+15; x<128 && !(x & 0x88); x+=15) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            if((dum & 7) == (from & 7)) same_file++;
                            if(((dum>>4) & 7) == ((from>>3) & 7)) same_rank++;
                            total++;
                        }
                        if(dum!=null) break;
                    }
                    for(x=to88-15; x>=0 && !(x & 0x88); x-=15) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            if((dum & 7) == (from & 7)) same_file++;
                            if(((dum>>4) & 7) == ((from>>3) & 7)) same_rank++;
                            total++;
                        }
                        if(dum!=null) break;
                    }                   
                }
                if(total>1) {
                    if(same_file<=1) game.moves += fromn[0];
                    else if(same_rank<=1) game.moves += fromn[1];
                    else game.moves += fromn;
                    
                }
                game.moves += (capture?'x'+ton:ton);
            }
            
            //res += ' {[%emt '+strtime(time)+'] [%eval '+score+'] [%depth '+depth+'] }';
            
            board[from] = null;
            board[to] = casedpiece;
        }
        
        ply++;
        tomove = 1-tomove;
    }
    
    if(ply>0 && res.pending) res.s += game.toString();
    
    cumulative_results = res.list;
    
    return res.s;
};


function parseservermoves(buffer) {
    var board = [
                  'r', 'n', 'b', 'q', 'k', 'b', 'n', 'r',
                  '', '', '', '', '', '', '', '',
                  null, null, null, null, null, null, null, null, 
                  null, null, null, null, null, null, null, null, 
                  null, null, null, null, null, null, null, null, 
                  null, null, null, null, null, null, null, null, 
                  '', '', '', '', '', '', '', '',
                  'R', 'N', 'B', 'Q', 'K', 'B', 'N', 'R',
                ];

    var r = /([\w\d:\/+\-=\*]*);/g;
    var m;
    var player = {};
    var n;
    var res = "";
    var tomove = 0;
    var ply = 0;
    
    m = r.exec(buffer);
    player.white = (m!=null)?m[1]:'?';
    if(player.white==='') {
        player.white = '?';
        player.black = '?';
    } else {
        m = r.exec(buffer);
        player.black = (m!=null)?m[1]:'?';
        if(player.black==='') player.black = '?';
    }
    
    res += '[White "'+player.white+'"]\n[Black "'+player.black+'"]\n[Result "*"]\n\n';
    
    while( m = r.exec(buffer) ) {
        n = /([a-h][1-8]):([a-h][1-8])(?::([qrnb]|[a-h][1-8]):([a-h][1-8]))?\/(\d+)\/(-?\d+)\/(\d+)/.exec(m[1]);

        if(!n) {
            n = /([+\-=\*])/.exec(m[1]);
            if(n=='+') res+=' 1-0\n\n';
            else if(n=='-') res+=' 0-1\n\n';
            else if(n=='=') res+=' 1/2-1/2\n\n';
            else res+=' *\n\n';
        } else {
            var from = square[n[1]];
            var fromn = n[1];
            var to = square[n[2]];
            var ton = n[2];
            var piece = upcase[board[from]];
            var casedpiece = board[from];
            var promotion;
            var enpassant;
            var capture;
            var castle;
            var depth = n[5];
            var score = n[6]/100;
            var time = n[7];
            
            
            
            if(board[to]!=null) capture = true;
            else capture = false;

            if(n[3]==null) {
                promotion = false;
                enpassant = false;
                castle = false;
            } else if(n[3].length>1) {
                promotion = false;
                if(piece=='K') {
                    castle = true;
                    enpassant = false;
                } else {
                    castle = false;
                    enpassant = true;
                }
            } else {
                promotion = true;
                castle = false;
                enpassant = false;
            }
            
            if(ply%2==0) res += ' '+(ply/2+1)+'. ';
            else res += ' ';
            
            if(promotion) {
                res += ton + '=' + upcase[n[3]];
                board[square[n[4]]] = tomove==0?n[3]:upcase[n[3]];
            } else if(castle) {
                res += ton[0]=='g'?'O-O':'O-O-O';
                board[square[n[3]]] = null;
                board[square[n[4]]] = (tomove==0?'r':'R');
            } else if(enpassant) {
                res += fromn[0]+'x'+ton;
                board[square[n[3]]] = null;
                board[square[n[4]]] = '';
            } else {
                var total = 0;
                var same_file = 0;
                var same_rank = 0;
                res += (piece=='' && capture)?fromn[0]:piece;
                if(piece=='N') {
                    var to88 = to + (to & 56);
                    knightjumps88.forEach(function(jump) {
                        var dum = to88 + jump;
                        
                        if(dum>=0 && dum<128 && (dum & 0x88)==0) {
                            if(board[((dum >> 1) & 56)+(dum & 7)] == casedpiece) {
                                if((dum&7)==(from&7)) same_file++;
                                if((dum>>4)&7==((from>>3)&7)) same_rank++;
                                total++;
                            }
                        }
                    });
                }
                if(piece=='R' || piece=='Q') {
                    var to88 = to + (to & 56);
                    var dum;
                    
                    for(x=to88+1; x<128 && !(x & 0x88); x++) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            same_rank++;
                            total++;
                        }
                        if(dum!=null) break;
                    }
                    for(x=to88-1; x>=0 && !(x & 0x88); x--) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            same_rank++;
                            total++;
                        }
                        if(dum!=null) break;
                    }
                    for(x=to88+16; x<128 && !(x & 0x88); x+=16) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            same_file++;
                            total++;
                        }
                        if(dum!=null) break;
                    }
                    for(x=to88-16; x>=0 && !(x & 0x88); x-=16) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            same_file++;
                            total++;
                        }
                        if(dum!=null) break;
                    }                   
                }
                if(piece=='B' || piece=='Q') {
                    var to88 = to + (to & 56);
                    var dum;
                    
                    for(x=to88+17; x<128 && !(x & 0x88); x+=17) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            if((dum & 7) == (from & 7)) same_file++;
                            if(((dum>>4) & 7) == ((from>>3) & 7)) same_rank++;
                            total++;
                        }
                        if(dum!=null) break;
                    }
                    for(x=to88-17; x>=0 && !(x & 0x88); x-=17) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            if((dum & 7) == (from & 7)) same_file++;
                            if(((dum>>4) & 7) == ((from>>3) & 7)) same_rank++;
                            total++;
                        }
                        if(dum!=null) break;
                    }
                    for(x=to88+15; x<128 && !(x & 0x88); x+=15) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            if((dum & 7) == (from & 7)) same_file++;
                            if(((dum>>4) & 7) == ((from>>3) & 7)) same_rank++;
                            total++;
                        }
                        if(dum!=null) break;
                    }
                    for(x=to88-15; x>=0 && !(x & 0x88); x-=15) {
                        dum = board[((x >> 1) & 56)+(x & 7)];
                        if(dum==casedpiece) {
                            if((dum & 7) == (from & 7)) same_file++;
                            if(((dum>>4) & 7) == ((from>>3) & 7)) same_rank++;
                            total++;
                        }
                        if(dum!=null) break;
                    }                   
                }
                if(total>1) {
                    if(same_file<=1) res+=fromn[0];
                    else if(same_rank<=1) res+=fromn[1];
                    else res+=fromn;
                }
                res += (capture?'x'+ton:ton);
            }
            
            res += ' {[%emt '+strtime(time)+'] [%eval '+score+'] [%depth '+depth+'] }';
            
            board[from] = null;
            board[to] = casedpiece;
        }
        
        ply++;
        tomove = 1-tomove;
    }
    
    res += '\n\n*\n\n';
    
    return res;
};

// Use this to test locally

var conn = null;

parser = parseservermoves;

process.argv.forEach(function(arg) {
    if(/debug/.exec(arg)) debug = true;
    else if(/xboard/.exec(arg)) parser = parsexboard;
    else if(/arena/.exec(arg)) parser = function(buffer) { return buffer; };
});

process.on('quit',function() {
    var res = (new Date()).toString() + '\n';
    var count = 0;
    var maxlen = 0;
    
    for(var player in cumulative_results.byplayer) {
        if(player.length>maxlen) maxlen = player.length;
    }
    
    maxlen += 4;
    
    res += 'No.\tName';
    for(var i = 4; i<maxlen; i++) res += ' ';
    res += 'Win\tDraw\tLoss\tUnf.\tScore\t%\n'
    res += '----------------------------------------------------------------------\n'
    
    for(var player in cumulative_results.byplayer) {
        var wins = cumulative_results.byplayer[player]['1-0'];
        var draws = cumulative_results.byplayer[player]['1/2-1/2'];
        var losses = cumulative_results.byplayer[player]['0-1'];
        var unfinished = cumulative_results.byplayer[player]['*'];
        var score = (2 * wins + draws)/2;
        var total = wins + draws + losses + unfinished;
        
        res += (++count) + '\t' + player;
        for(var i = player.length; i<maxlen; i++) res += ' ';
        res +=   wins       + '\t' 
               + draws      + '\t'
               + losses     + '\t'
               + unfinished + '\t'
               + score      + '\t'
               + (((100*score)/total)/100) + '%\n';
    }
    
    res += '\n';
    res += 'Total Games:\t' + ((cumulative_results.bycols['1-0'] || 0)
                            + (cumulative_results.bycols['1/2-1/2'] || 0)
                            + (cumulative_results.bycols['0-1'] || 0)
                            + (cumulative_results.bycols['*'] || 0)) + '\n';
    res += 'White Wins: \t' + (cumulative_results.bycols['1-0'] || 0) + '\n';
    res += 'Black Wins: \t' + (cumulative_results.bycols['0-1'] || 0) + '\n';
    res += 'Draws:      \t' + (cumulative_results.bycols['1/2-1/2'] || 0) + '\n';
    res += 'Unfinished: \t' + (cumulative_results.bycols['*'] || 0) + '\n';
    
    res += '----------------------------------------------------------------------\n';
    
    if(debug) {
        console.log('\n');
        console.log(res);
        try {
            fs.writeFileSync('tmp.txt',res);
        } catch(e) {
            console.log(e);
        }
        process.exit();
    } else if(conn) {
        console.log('\n');
        console.log(res);
        try {
            fs.writeFileSync('tmp.txt',res);
            var stream_table = fs.createReadStream('tmp.txt');
            stream_table.setEncoding('utf8');
            conn.put(stream_table,'EventoT.txt',function(errftp) {
                if(errftp) throw errftp;
                var stream_pgn = fs.createReadStream('tmp.pgn');
                stream_pgn.setEncoding('utf8');
                conn.put(stream_pgn,'Evento.pgn',function(errftp1) {
                    if(errftp1) throw errftp1;
                    conn.end();    
                });
            });
        } catch(e) {
            console.log(e);
            conn.end();
        }
    } else {
        console.log('FTP connection broken');
        process.exit();
    }
});

if(debug) {
    setInterval(function() {
        var buf;
        var len;
        try {
            len = fs.statSync(filename).size;
            if(len>oldlen) {
                console.log('*');
                oldlen = len;
                buf = fs.readFileSync(filename,'utf8');
                fs.writeFileSync(remotefilename,parser(buf));
            }
        } catch(e) {
            console.log(e);
        }
    }, delay * 1000);
} else {

    conn = new FTPClient({host: hostname});

    process.on('exit',function() {
        console.log('Stopping process');        
    });
    
    conn.on('end',function() {
        console.log('FTP connection to '+hostname+' closed');
        process.exit();
    });
    
    conn.on('connect', function() {
        conn.auth(username,password,function(err) {
            if(err) throw err;
            setInterval(function() {
                var len;
                var buf;
                try {
                    len = fs.statSync(filename).size;
                    if(len!=oldlen) {
                        var tmpbuf;
                        
                        oldlen = len;
                        buf = fs.readFileSync(filename,'utf8');
                        tmpbuf = parser(buf);
                        fs.writeFileSync('tmp.pgn',tmpbuf);
                        if(tmpbuf.length!=oldlenbuf) {
                            oldlenbuf = tmpbuf.length;
                            var stream = fs.createReadStream('tmp.pgn');
                            stream.setEncoding('utf8');
                            conn.put(stream,remotefilename,function(errftp) {
                                if(errftp) throw errftp;
                                console.log('.'+tmpbuf.length+'B sent');
                            });
                        }
                    }
                } catch(e) {
                }
            }, 1000*delay);
        })
    });
    
    conn.connect();
};

console.log('Hit Ctrl-C to exit.');
process.stdin.resume();
tty.setRawMode(true);
process.stdin.on('keypress', function(chr, key) {
    if(key && key.ctrl && key.name == 'c') {
        process.emit('quit');
    }
});
