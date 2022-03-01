set -x -e
coq_makefile -R . proofchecker *.v -o Makefile
