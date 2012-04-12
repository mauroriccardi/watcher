var http = require('http');
var fs = require('fs');

http.createServer(
    function(req,res) {
        
        if(req.method=='GET') {
            fs.readFile('C:\\Programmi\\WinBoard-4.4.1\\WinBoard\\provarelay.txt','utf8',
                        function(err,data) {
                            if(err) throw err;
                            res.writeHead(200,{"Content-type": "text/plain"});
                            res.write(data);
                            res.end();
                            
                            
                        }
            );
        } 
        
    }).listen(8000);    