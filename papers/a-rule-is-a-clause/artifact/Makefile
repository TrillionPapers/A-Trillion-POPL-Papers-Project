# Runs the analyses of the paper on random permission lists, compares each of them with brute
# force over the actions that Lemma 3.1 says are enough, and regenerates the numbers and the
# table rows that the paper quotes.  `make check` fails if any of them differs from the files in
# expected/, which the paper reads.  Needs python3 and nothing else.
.PHONY: all check clean

FILES = check.txt numbers.tex example.tex growth.tex

all: check

check:
	mkdir -p out
	python3 rules.py out > /dev/null
	for f in $(FILES); do diff -u expected/$$f out/$$f || exit 1; done

clean:
	rm -rf out __pycache__
