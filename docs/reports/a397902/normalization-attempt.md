# Normalization and construction experiments

The checked source now lives in
`D5/S1/Recurrence/SquareRows/SquareExponentDyadicSupport.lean`.
The earlier experimental source is preserved in git history, not duplicated here.

The coefficient-divisibility and exact-normalization experiments first passed
`lake env lean /tmp/A397902Normalization.lean` with EXIT=0 on the preheated tree.
Subsequent successful experiments established the binary diagonal vanishing
lemma and the unit multiplier of the normalized residual.

The integer existence/uniqueness construction was then checked in the D5 file:
`lake env lean D5/S1/Recurrence/SquareRows/SquareExponentDyadicSupport.lean`, EXIT=0.
No axiom beyond propext, Classical.choice, Quot.sound was reported for
`integer_exists_unique`. This constructs F with constant coefficient one;
A=1-F is the target's zero-constant integer series. Parity is still pending.
No freeze or coverage is claimed by these file-level checks.
