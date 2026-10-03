# Greatest Pell indices dividing initial partial sums

## Abstract

Pell partial sums have greatest dividing indices in four residue classes.

The Pell sequence has P(0)=0, P(1)=1 and P(n+2)=2P(n+1)+P(n). Its companion has Q(0)=Q(1)=1 and Q(n+2)=2Q(n+1)+Q(n). Write S(n)=P(1)+...+P(n). The formal sum ranges from zero through n; P(0)=0 makes this the same sum. Let G(n,m) mean that m is the greatest positive index j for which P(j) divides S(n). Thus G(n,m) includes m>=1 and P(m)|S(n), and asserts j<=m for every j>=1 satisfying P(j)|S(n).

**Theorem 1.1 (Four greatest-index classes).**

$$(\forall k \in \mathrm{Nat},\; \operatorname{G}\left(4 \cdot k + 1, 1\right)) \land \left((\forall k \in \mathrm{Nat},\; \operatorname{G}\left(4 \cdot k + 2, 1\right)) \land \left((\forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow (\operatorname{G}\left(4 \cdot k - 1, 2 \cdot k\right))) \land (\forall k \in \mathrm{Nat},\; (1 \le k) \Rightarrow (\operatorname{G}\left(4 \cdot k, 2 \cdot k + 1\right)))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/PellPartialSumMaxIndex.result` (`✓ std3`). ∎

*Resolves.* `Problems/byrapuram-pell-partial-sum-max-index` (proved) by `D5/S1/Recurrence/PellPartialSumMaxIndex.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"byrapuram-pell-partial-sum-max-index","declaration_gid":"D5/S1/Recurrence/PellPartialSumMaxIndex.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nikhil Byrapuram; Adam Ge; Selena Ge; Tanya Khovanova; Sylvia Zia Lee; Rajarshi Mandal; Gordon Redwine; Soham Samanta; Daniel Wu; Danyang Xu; Ray Zhao (2024). *Fibonacci Partial Sums Tricks*. DOI: [10.1080/00150517.2025.2556152](https://doi.org/10.1080/00150517.2025.2556152). URL: <https://arxiv.org/html/2409.01296v1>.

*Commentary.*

The addition formulas yield P(2r)=2P(r)Q(r) and Q(2r)=Q(r)^2+2P(r)^2. Together with Q(r)^2-2P(r)^2=(-1)^r, they give S(4k+1)=Q(2k+1)^2 and S(4k+2)=Q(2k+1)Q(2k+2), and, for k>=1, S(4k-1)=2P(2k)^2 and S(4k)=2P(2k)P(2k+1). Strong divisibility gives gcd(P(a),P(b))=P(gcd(a,b)). For odd m, P(m) is coprime to every Q(j); consequently the first two odd sums admit only the index one. For the other sums, a dividing P(m) also divides 2 gcd(P(m),P(r)) gcd(P(m),P(s)). Proper divisor indices and strict growth place this positive product below P(m) whenever m exceeds the claimed maximum. In the equal-index case, Q(d)>P(d) for d>=2 handles the possible equality 2d=m. In the consecutive case, gcd(m,r) and gcd(m,r+1) are coprime, so their sum is strictly below m. Both latter classes exclude k=0.

## References

- Truth anchor: `D5/S1/Recurrence/PellPartialSumMaxIndex.result`
- Dependency: [D5/S1/Recurrence/PellCompanionGcd](PellCompanionGcd.md)
