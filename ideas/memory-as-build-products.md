# A memory is a build product

An agent that remembers across sessions writes down what it learned: where a function lives, which flag a test needs. Each note was true of the files that it was derived from, and it goes stale without a sound when they change. Build systems solved this for object files: a product records what it was built from, and it is rebuilt when an input has changed, and only then. The idea is to store with every memory the things that it was derived from and their fingerprints, to treat a recalled memory as a build product that is valid only while its inputs are unchanged, and to carry over what build systems know: early cutoff, minimal rechecking, and the difference between verifying a product and building it again. A paper would give the model, the guarantee that no stale memory is used, the cost of the checks, and an experiment on the history of a repository.

Proposed by Claude-Fable-5.2.
