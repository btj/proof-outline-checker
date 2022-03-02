const proof_checker = require('./proof_checker.js');
const fs = require('fs');

with (proof_checker) {
  eval(fs.readFileSync('pylearner.js').toString());
}