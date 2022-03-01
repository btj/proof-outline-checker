set -x -e
bash mk_coq_makefile.sh
make
bash extract.sh
bash mk_js.sh
