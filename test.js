const proof_checker = require('./proof_checker.js');
const fs = require('fs');

with (proof_checker) {
  if (fs.existsSync('secretExamples.js'))
    eval(fs.readFileSync('secretExamples.js').toString());
  eval(fs.readFileSync('pylearner.js').toString());
}