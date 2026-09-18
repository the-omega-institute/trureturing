# Perrier ECA 6:4 (2026), §5 — isolated probe

FALSIFIABLE PREDICTION (before checks): for every d and all parameters the two identities hold; a single failing (d, m, a) refutes the conjecture.

Scope: preregistered issue #8627; exact rational checks, source fidelity, pinned-library search, and kernel proof probe. No other seat output is an input. Verdict is pending verification.

## Source fidelity and rational check

Source visually inspected: printed pp. 14–15 (general recurrence/formulas), p. 12 (shifted definition and proved 3×3 formulas); text inspected for the 2×2 shifted definition. The issue's p. 7 locator for that definition is off by one: it occurs on printed p. 8. This is a locator error, not a change of statement.

Clause checks: k=d+1; source coordinate j+1 maps to Fin coordinate j; source time n−1 maps to natural index n. Initial coordinate zero is 1 and successor coordinates are a_j. Both recurrence equations agree after these shifts. D has m_j at exponent d−j and terminal term −X^(d+1); P has a_j−m_j at d−j; Q has leading X^d and a_j at d−1−j. All agree with the displayed formulas. Arbitrary fields/parameters and d=0 strengthen the real/integer k≥2 instance; no source case is lost. General-k shifted R is the explicit contextual reading already disclosed in the issue, not independently restated on p. 15. The follow-on conjecture about equation (7) is excluded. No statement-fidelity defect found.

Independent exact Fraction computation: 2,867 parameter cases, d=1..8; coefficients 0..47 for both identities (275,232 coefficient equalities), zero failures. Exhaustive {-1,0,1} parameters for d≤3 plus 256 seeded rational cases per d (numerators −8..8, denominators 1..7). Per-d counts and seed are in python-result.json. Controls: all 337 d=2 cases also match the independently printed middle-coordinate formula; d=0 checked separately. Finite checks do not prove the universal claim.
