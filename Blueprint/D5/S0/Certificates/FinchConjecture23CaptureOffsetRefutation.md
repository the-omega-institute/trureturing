# Finch Conjecture 23 fails at the purely periodic boundary

## Abstract

The k = 2 recurrence has least period 4, least preperiod 0 and least capture endpoint 9.

**Definition 1.1 (Recurrence A on positive indices).**

$$\forall k \in \mathrm{Nat},\; \forall x \in \mathrm{Nat} \to \operatorname{ZMod}\left(3\right),\; (\operatorname{IsSourceSequence}\left(k, x\right)) \Leftrightarrow ((\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow ((n < k) \Rightarrow (\operatorname{x}\left(n\right) = 0))) \land \left((\operatorname{x}\left(k\right) = 1) \land (\forall n \in \mathrm{Nat},\; (k + 1 \le n) \Rightarrow (\operatorname{x}\left(n\right) = \operatorname{x}\left(n - 1\right) + \operatorname{x}\left(n - k\right)^{2}))\right))$$

*Formalization.* `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.IsSourceSequence` (`✓ std3`).

*Citation.* Steven Finch (2026). *Three Quadratic Recurrences Modulo 3: What We Can Prove and What We Can Guess*. URL: <https://arxiv.org/abs/2610.34300v1>.

*Commentary.*

Finch, arXiv:2610.34300v1, pp. 1 and 9, recurrence (A) and the final Addendum. All values lie in ZMod 3. Initial indices satisfy 1 ≤ n < k; x(k)=1; the recurrence applies for n ≥ k+1. Index zero is unconstrained and unused for k ≥ 2.

**Definition 1.2 (Positive eventual periods).**

$$\forall x \in \mathrm{Nat} \to \operatorname{ZMod}\left(3\right),\; \forall p \in \mathrm{Nat},\; (\operatorname{IsEventualPeriod}\left(x, p\right)) \Leftrightarrow ((0 < p) \land (\exists m \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; (m < n) \Rightarrow (\operatorname{x}\left(n + p\right) = \operatorname{x}\left(n\right))))$$

*Formalization.* `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.IsEventualPeriod` (`✓ std3`).

*Citation.* Steven Finch (2026). *Three Quadratic Recurrences Modulo 3: What We Can Prove and What We Can Guess*. URL: <https://arxiv.org/abs/2610.34300v1>.

*Commentary.*

Finch, p. 1. A positive period holds after some natural threshold, with the strict inequality n > m.

**Definition 1.3 (The least positive eventual period).**

$$\forall x \in \mathrm{Nat} \to \operatorname{ZMod}\left(3\right),\; \forall p \in \mathrm{Nat},\; (\operatorname{HasLeastEventualPeriod}\left(x, p\right)) \Leftrightarrow ((\operatorname{IsEventualPeriod}\left(x, p\right)) \land (\forall q \in \mathrm{Nat},\; (\operatorname{IsEventualPeriod}\left(x, q\right)) \Rightarrow (p \le q)))$$

*Formalization.* `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.HasLeastEventualPeriod` (`✓ std3`).

*Citation.* Steven Finch (2026). *Three Quadratic Recurrences Modulo 3: What We Can Prove and What We Can Guess*. URL: <https://arxiv.org/abs/2610.34300v1>.

*Commentary.*

IsLeast means membership and a lower bound on every other member. No default minimum is assigned to an empty set.

**Definition 1.4 (The capture gap count).**

$$\forall k \in \mathrm{Nat},\; \operatorname{gaps}\left(k\right) = \operatorname{NatDiv}\left(k - 1 + 3, 4\right)$$

*Formalization.* `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.gaps` (`✓ std3`).

*Citation.* Steven Finch (2026). *Three Quadratic Recurrences Modulo 3: What We Can Prove and What We Can Guess*. URL: <https://arxiv.org/abs/2610.34300v1>.

*Commentary.*

Finch, p. 9. For k ≥ 2, this natural-number division equals ceil((k-1)/4). NatDiv denotes floor division, and subtraction here is natural subtraction.

**Definition 1.5 (A run with g four-spaced gaps).**

$$\forall k \in \mathrm{Nat},\; \forall x \in \mathrm{Nat} \to \operatorname{ZMod}\left(3\right),\; \forall r \in \mathrm{Nat},\; \forall g \in \mathrm{Nat},\; (\operatorname{IsRun}\left(k, x, r, g\right)) \Leftrightarrow ((k + 1 \le r) \land \left((1 \le g) \land \left((\forall i \in \mathrm{Nat},\; (i \le g) \Rightarrow (\operatorname{x}\left(r + 4 \cdot i\right) = 0)) \land (\forall n \in \mathrm{Nat},\; (r < n) \Rightarrow ((n < r + 4 \cdot g) \Rightarrow ((\neg \operatorname{NatMod}\left(n - r, 4\right) = 0) \Rightarrow (\neg \operatorname{x}\left(n\right) = 0))))\right)\right))$$

*Formalization.* `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.IsRun` (`✓ std3`).

*Citation.* Steven Finch (2026). *Three Quadratic Recurrences Modulo 3: What We Can Prove and What We Can Guess*. URL: <https://arxiv.org/abs/2610.34300v1>.

*Commentary.*

Finch, Definition 15, p. 6, reused in the final Addendum, p. 9. The start is at least k+1, g is positive, all g+1 listed positions are zero, and every other interior position is nonzero. The run need not be maximal. NatMod is natural remainder.

**Definition 1.6 (The least capturing endpoint).**

$$\forall k \in \mathrm{Nat},\; \forall x \in \mathrm{Nat} \to \operatorname{ZMod}\left(3\right),\; \forall z \in \mathrm{Nat},\; (\operatorname{IsCapturePoint}\left(k, x, z\right)) \Leftrightarrow ((\exists r \in \mathrm{Nat},\; (\operatorname{IsRun}\left(k, x, r, \operatorname{gaps}\left(k\right)\right)) \land (z = r + 4 \cdot \operatorname{gaps}\left(k\right))) \land (\forall t \in \mathrm{Nat},\; (\exists r \in \mathrm{Nat},\; (\operatorname{IsRun}\left(k, x, r, \operatorname{gaps}\left(k\right)\right)) \land (t = r + 4 \cdot \operatorname{gaps}\left(k\right))) \Rightarrow (z \le t)))$$

*Formalization.* `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.IsCapturePoint` (`✓ std3`).

*Citation.* Steven Finch (2026). *Three Quadratic Recurrences Modulo 3: What We Can Prove and What We Can Guess*. URL: <https://arxiv.org/abs/2610.34300v1>.

*Commentary.*

Finch, Definition 21, p. 9. An endpoint belongs exactly when a qualifying run with gaps(k) gaps ends there; it is a capture point exactly when it is the least such endpoint.

**Definition 1.7 (The least four-preperiod).**

$$\forall x \in \mathrm{Nat} \to \operatorname{ZMod}\left(3\right),\; \forall m \in \mathrm{Nat},\; (\operatorname{IsPreperiod}\left(x, m\right)) \Leftrightarrow ((\forall n \in \mathrm{Nat},\; (m < n) \Rightarrow (\operatorname{x}\left(n + 4\right) = \operatorname{x}\left(n\right))) \land (\forall t \in \mathrm{Nat},\; (\forall n \in \mathrm{Nat},\; (t < n) \Rightarrow (\operatorname{x}\left(n + 4\right) = \operatorname{x}\left(n\right))) \Rightarrow (m \le t)))$$

*Formalization.* `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.IsPreperiod` (`✓ std3`).

*Citation.* Steven Finch (2026). *Three Quadratic Recurrences Modulo 3: What We Can Prove and What We Can Guess*. URL: <https://arxiv.org/abs/2610.34300v1>.

*Commentary.*

Finch, Definition 22, p. 9. The least natural m satisfies x(n+4)=x(n) for all n>m. The source's accompanying last-disagreement equivalence needs a separate convention in the purely periodic case; the explicit least-m definition is used here.

**Definition 1.8 (Conjecture 23 on the full original domain).**

$$(claim) \Leftrightarrow ((\forall k \in \mathrm{Nat},\; (2 \le k) \Rightarrow (\exists x \in \mathrm{Nat} \to \operatorname{ZMod}\left(3\right),\; \operatorname{IsSourceSequence}\left(k, x\right))) \land (\forall k \in \mathrm{Nat},\; \forall x \in \mathrm{Nat} \to \operatorname{ZMod}\left(3\right),\; (2 \le k) \Rightarrow ((\operatorname{IsSourceSequence}\left(k, x\right)) \Rightarrow (((\operatorname{NatMod}\left(k, 4\right) = 2) \lor (\operatorname{NatMod}\left(k, 4\right) = 3)) \Rightarrow ((\operatorname{HasLeastEventualPeriod}\left(x, 4\right)) \Rightarrow (\exists z \in \mathrm{Nat},\; \exists m \in \mathrm{Nat},\; (\operatorname{IsCapturePoint}\left(k, x, z\right)) \land \left((\operatorname{IsPreperiod}\left(x, m\right)) \land ((z: \mathrm{Int}) - (m: \mathrm{Int}) = 6)\right)))))))$$

*Formalization.* `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.claim` (`✓ std3`).

*Citation.* Steven Finch (2026). *Three Quadratic Recurrences Modulo 3: What We Can Prove and What We Can Guess*. URL: <https://arxiv.org/abs/2610.34300v1>.

*Commentary.*

Finch, Conjecture 23, p. 9. The domain includes k=2 and preperiod zero. The first conjunct explicitly requires source-sequence existence for each k ≥ 2; the second quantifies every such sequence, requires k mod 4 equal to 2 or 3 and least eventual period 4, and asserts existence of least capture and preperiod indices with integer difference 6.

**Theorem 1.9 (The original universal offset identity is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/finch-2026-conjecture-23-capture-offset` (refuted) by `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"finch-2026-conjecture-23-capture-offset","declaration_gid":"D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Steven Finch (2026). *Three Quadratic Recurrences Modulo 3: What We Can Prove and What We Can Guess*. URL: <https://arxiv.org/abs/2610.34300v1>.

*Commentary.*

For k=2 the explicit positive-index sequence repeats (0,1,1,2). A four-residue argument verifies the recurrence at every n≥3. Periods 1, 2 and 3 fail arbitrarily far out, while period 4 holds from the first term, so the least positive eventual period is 4 and the least four-preperiod is 0. Here gaps(2)=1. The run from 5 to 9 has no extra interior zeros; any allowed earlier start would be 3 or 4, whose values are nonzero. Thus the least capture endpoint is 9, and 9-0 is not 6. This is completion of the existing #23615 hand route, without a discovery or priority claim. It proves neither an infinite exceptional family nor a corrected k≥3 or positive-preperiod law.

## References

- Truth anchor: `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.HasLeastEventualPeriod`
- Truth anchor: `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.IsCapturePoint`
- Truth anchor: `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.IsEventualPeriod`
- Truth anchor: `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.IsPreperiod`
- Truth anchor: `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.IsRun`
- Truth anchor: `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.IsSourceSequence`
- Truth anchor: `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.claim`
- Truth anchor: `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.gaps`
- Truth anchor: `D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.result`
