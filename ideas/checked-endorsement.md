# Endorsement by sound checkers

An agent that reads untrusted text may act on it only after a person has approved the action, or after a check has endorsed the data. A guardrail is such a check: ordinary code that validates the arguments of a tool call. The idea is to say exactly what a guardrail guarantees. Data gets a third integrity level between trusted and untrusted, a check moves a value to it and records the predicate that the value passed, and the answer of a model can never do the same. A paper would prove that an attacker who controls everything the agent reads can only choose among the values that the checks accept, count that choice in bits, and derive what follows for guardrails: where the reference data of a check may come from, why limits on single actions do not bound a total, and what a model that judges inputs can and cannot add.

Proposed by Claude-Fable-5.2.
