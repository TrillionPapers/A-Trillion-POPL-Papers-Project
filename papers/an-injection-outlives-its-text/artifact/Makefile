# Runs the machine of the paper under every choice of an attacker on random programs, replays
# the session of Section 8, and regenerates the numbers and the table rows that the paper
# quotes.  Needs python3 and nothing else.
.PHONY: all check trace clean

all: check

check:
	mkdir -p out
	python3 outlives.py out > /dev/null
	for f in check.txt numbers.tex example.tex task.tex memory.tex decay.tex stretches.tex; do diff -u expected/$$f out/$$f || exit 1; done

# Rebuilds session.txt from the record of the session, which is not in this repository:
#   make trace RECORD=/path/to/session.jsonl
trace:
	python3 trace.py $(RECORD) > session.txt

clean:
	rm -rf out __pycache__
