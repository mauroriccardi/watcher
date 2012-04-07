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

var http = require('http');
var fs = require('fs');
var FTPClient = require('./node-ftp');

var hostname;
var username;
var password;
var filename;
var remotefilename;
var delay = 1;
var oldlen = 0;

var square = {};
var i = 0;

var upcase = {'q': 'Q', 'n': 'N', 'r': 'R', 'b': 'B', '': '', 'k': 'K', 'Q': 'Q', 'N': 'N', 'R': 'R', 'B': 'B', 'K': 'K'};

var knightjumps = [10,-6,6,-10,17,-15,15,-17];
var knightjumps88 = [18,-14,14,-18,33,-31,31,-33];
var knightshifts = {file: [-32,-16,16,31], rank: [-4,-2,2,4]};

var files = ['a','b','c','d','e','f','g','h'];

console.log('Watcher version 0.1, Copyright (C) 2012 Mauro Riccardi');
console.log('Watcher comes with ABSOLUTELY NO WARRANTY.');
console.log('This is free software, and you are welcome');
console.log('to redistribute it under certain conditions.\nSee file COPYING and/or license details in the source for details.');

for(var rank = 1; rank<=8; rank++) {
    files.forEach(function(file) {
        square[file+rank] = i++;
    });
};

var options;
var parsedopts = {};

try {
    options = fs.readFileSync('watcher.ini','utf8');
} catch(e) {
    throw e;
}

var optre = /([a-z_]+)\s*:\s*(\w[\w:\\ .\-]+)/g;
var admittedtokens = ['username','password','movesfilename','remotefilename','hostname','delay'];
var option;
while(option = optre.exec(options)) {
    var str = option[1] || 'invalid';
    if(str in admittedtokens)
        parsedopts[str] = option[2] || '';
}

password = options.password || '';
username = options.username || 'anonymous';
filename = options.movesfilename || '';
remotefilename = options.remotefilename || 'live.pgn';
delay = options.delay || 1;
hostname = options.hostname || '127.0.0.1';

function strtime(time) {
    var s = time % 60;
    time = (time - s)/60;
    var m = time % 60;
    time = (time - m)/60;
    return(time+':'+(m<10?'0'+m:m)+':'+(s<10?'0'+s:s));
}

function parse(buffer) {
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

    var r = /([\w\d:\/+\-=\*]+);/g;
    var m;
    var player = {};
    var n;
    var res = "";
    var tomove = 0;
    var ply = 0;
    
    player.white = r.exec(buffer)[1];
    player.black = r.exec(buffer)[1];
    
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
                res += ton + '=' + n[3];
                board[square[n[4]]] = upcase[n[3]];
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
            
            res += ' {[%emt '+strtime(time)+'] [%eval '+score+'] depth '+depth+' }';
            
            board[from] = null;
            board[to] = casedpiece;
        }
        
        ply++;
        tomove = 1-tomove;
    }
    
    return res;
};

setInterval(function() {
    var buf;
    var len;
    try {
        len = fs.statSync(filename).size;
        if(len>oldlen) {
            oldlen = len;
            buf = fs.readFileSync(filename,'utf8');
            fs.writeFileSync(remotefilename,parse(buf));
        }
    } catch(e) {
    }
}, delay * 1000);

// var conn = new FTPClient({host: hostname});

// conn.on('connect', function() {
    // conn.auth(username,password,function(err) {
        // if(err) throw err;
        // setInterval(function() {
            // var buf = fs.readFileSync(filename,'utf8');
            // fs.writeFileSync('tmp.txt',parse(buf));
            // var stream = fs.createReadStream('tmp.txt');
            // stream.setEncoding('utf8');
            // conn.put(stream,remotefilename,function(err) {
                // if(err) throw err;
            // });
        // }, 1000*delay);
    // })
// });

// conn.connect();
