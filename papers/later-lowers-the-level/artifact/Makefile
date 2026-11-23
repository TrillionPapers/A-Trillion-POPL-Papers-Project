# Type-checks the three Agda files of the paper and compares the list of checked claims and
# the numbers that the paper quotes with the files in expected/.  `make check` fails if Agda
# rejects a file, if a claim marked in the paper has no definition, or if a file differs.
# Needs agda (2.8.0 was used; no library is needed) and python3.
.PHONY: all check clean

FILES = check.txt numbers.tex

all: check

check:
	mkdir -p out
	python3 claims.py out
	for f in $(FILES); do diff -u expected/$$f out/$$f || exit 1; done

clean:
	rm -rf out _build *.agdai
