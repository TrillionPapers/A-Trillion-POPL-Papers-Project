# Runs the analyses of the paper on small texts and random batches of edits, compares each of
# them with what a harness does when it makes the edits one at a time, and regenerates the
# numbers and the table rows that the paper quotes.  `make check` fails if any of them differs
# from the files in expected/, which the paper reads.  Needs python3 and nothing else.
.PHONY: all check clean

FILES = check.txt numbers.tex orders.tex stale.tex

all: check

check:
	mkdir -p out
	python3 edits.py out > /dev/null
	for f in $(FILES); do diff -u expected/$$f out/$$f || exit 1; done

clean:
	rm -rf out __pycache__
