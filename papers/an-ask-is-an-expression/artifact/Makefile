# Runs the analyses of the paper on random programs and on three workflows, compares the
# placements they give with every other placement of small programs, and regenerates the
# numbers and the table rows that the paper quotes.  `make check` fails if any of them differs
# from the files in expected/, which the paper reads.  Needs python3 and nothing else.
.PHONY: all check clean

FILES = check.txt numbers.tex costs.tex loop.tex cases.tex

all: check

check:
	mkdir -p out
	python3 place.py out > /dev/null
	for f in $(FILES); do diff -u expected/$$f out/$$f || exit 1; done

clean:
	rm -rf out __pycache__
