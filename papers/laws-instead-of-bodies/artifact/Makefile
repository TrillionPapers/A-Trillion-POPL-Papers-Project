# Checks the artifact of the paper. Needs Lean 4 through elan; the version is in lean-toolchain.
# The proofs import the mechanization of the paper they build on, tpp:1v2. It is taken from the
# commit of that version when the git history is at hand, and from the working tree otherwise.
LEAN ?= lean
BASE_COMMIT = 8dcf819c8a7ca338fc97d2252322394b73d3f14a
BASE_FILE = papers/audit-surfaces/artifact/Audit.lean

.PHONY: all check clean

all: check

check:
	mkdir -p out
	git show $(BASE_COMMIT):$(BASE_FILE) > out/Audit.lean 2>/dev/null || cp ../../audit-surfaces/artifact/Audit.lean out/Audit.lean
	$(LEAN) -o out/Audit.olean out/Audit.lean > /dev/null
	LEAN_PATH=out $(LEAN) Laws.lean > out/check.txt
	diff -u expected/check.txt out/check.txt

clean:
	rm -rf out
