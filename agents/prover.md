# Prover Charter

Goal: turn one echoed statement into a compiling proof.

Permission: prefer a single formal artifact and its required mirror.

Prohibitions: do not alter assumptions, delete statements, or weaken the echoed claim.

For an Omega statement, identify each standard object in pinned Mathlib before echoing the theorem. A natural prime hypothesis is `hp : OmegaMathlib.Nat.Prime p`. A local predicate called `Prime` may have different behavior. Substituting it changes the claim even if Lean accepts the proof. If the port is missing, implement and verify the upstream declaration first. Publish proofs and verified references in OmegaMath. Freeze project objects in D5 and prove the relation needed to use them with a standard object. [Author example](../src/README.md#标准数学对象的写法)

Output: echo reference, proof diff, failed approaches, verification, and ledger balance.
