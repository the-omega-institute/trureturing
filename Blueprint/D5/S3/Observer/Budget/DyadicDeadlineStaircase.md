# Exceptional Dyadic Deadline Prefixes

## Abstract

Binary prefix weights determine the exact second-parity deadline thresholds.

Fix d>=0, P=2^(d+1), and W=sharpWait(d+1). The earliest final-query time for prefix t is E(t)=P-1+P wt(t)-2t. Every t<2^d has at most d one-bits. The unique prefix with d one-bits is 2^d-1, and each prefix with d-1 one-bits is 2^d-1-2^k for some k<d.

**Theorem 1.1 (Exact exceptional-prefix timing).**

$$\forall d: \mathbb{N}, \left(\left(\operatorname{earliestTime}\left(d, \operatorname{pow}\left(2, d\right) - 1\right) + \operatorname{pow}\left(2, d + 1\right) = \operatorname{sharpWait}\left(d + 1\right) + \operatorname{pow}\left(2, d + 1\right)\right) \land \left(\left(\forall k: \mathbb{N}, \left(\left(k < d\right) \implies \left(\operatorname{earliestTime}\left(d, \operatorname{pow}\left(2, d\right) - 1 - \operatorname{pow}\left(2, k\right)\right) + \operatorname{pow}\left(2, d + 1\right) = \operatorname{sharpWait}\left(d + 1\right) + \operatorname{pow}\left(2, k + 1\right)\right)\right)\right) \land \left(\left(\forall t: \mathbb{N}, \left(\left(\left(t < \operatorname{pow}\left(2, d\right)\right) \land \left(\operatorname{length}\left(\operatorname{bitIndices}\left(t\right)\right) + 2 \le d\right)\right) \implies \left(\operatorname{earliestTime}\left(d, t\right) + \operatorname{pow}\left(2, d + 1\right) \le \operatorname{sharpWait}\left(d + 1\right)\right)\right)\right) \land \left(\forall t: \mathbb{N}, \left(\left(t < \operatorname{pow}\left(2, d\right)\right) \implies \left(\left(\operatorname{length}\left(\operatorname{bitIndices}\left(t\right)\right) \le d\right) \land \left(\left(\left(\operatorname{length}\left(\operatorname{bitIndices}\left(t\right)\right) = d\right) \implies \left(t = \operatorname{pow}\left(2, d\right) - 1\right)\right) \land \left(\left(\operatorname{length}\left(\operatorname{bitIndices}\left(t\right)\right) + 1 = d\right) \implies \left(\exists k: \mathbb{N}, \left(\left(k < d\right) \land \left(t + \operatorname{pow}\left(2, k\right) = \operatorname{pow}\left(2, d\right) - 1\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/DyadicDeadlineStaircase.exceptional_prefix_timing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The all-ones prefix needs slack P for a second terminal parity. Removing bit k gives exact slack 2^(k+1). A prefix with at least two missing one-bits already permits the extra period at W. The binary classification covers d=0 and all k<d. This result classifies threshold prefixes but does not itself count labels of the deadline family.

**Theorem 1.2 (Closed operational deadline staircase).**

$$\forall d: \mathbb{N}, \left(\forall h: \mathbb{N}, \left(\forall b: \operatorname{Fin}\left(2\right), \left(\left(\forall Z: Type, \left(\forall phi: \mathbb{N} \to Z, \left(\forall recover: Z \to \operatorname{Fin}\left(2\right) \to \mathbb{N}, \left(\left(\forall p: \operatorname{Protocol}\left(d + 1\right), \left(\left(\operatorname{deadlineFamily}\left(d, b, \operatorname{sharpWait}\left(d + 1\right) + h, p\right)\right) \implies \left(\forall r: \mathbb{N}, \left(\left(r < \operatorname{pow}\left(2, d + 1\right)\right) \implies \left(\operatorname{recover}\left(\operatorname{phi}\left(\operatorname{terminalTime}\left(\operatorname{pow}\left(2, d + 1\right), b, p, r\right)\right), \operatorname{snd}\left(\operatorname{terminalRecord}\left(\operatorname{pow}\left(2, d + 1\right), b, p, r\right)\right)\right) = r\right)\right)\right)\right)\right) \implies \left(\operatorname{pow}\left(2, d + 1\right) - \left(d + 1\right) + \left(Finset.Icc\left(1, d + 1\right)\right).filter\left(\lambda i: \mathbb{N} \mapsto \left(\operatorname{pow}\left(2, i\right) \le h\right)\right).card \le \operatorname{card}\left(\operatorname{familyClockLabels}\left(d, b, \operatorname{sharpWait}\left(d + 1\right) + h, phi\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall p: \operatorname{Protocol}\left(d + 1\right), \left(\left(\operatorname{deadlineFamily}\left(d, b, \operatorname{sharpWait}\left(d + 1\right) + h, p\right)\right) \implies \left(\forall r: \mathbb{N}, \left(\left(r < \operatorname{pow}\left(2, d + 1\right)\right) \implies \left(\operatorname{tagDecode}\left(d, b, \operatorname{clockTag}\left(d, \operatorname{terminalTime}\left(\operatorname{pow}\left(2, d + 1\right), b, p, r\right)\right), \operatorname{snd}\left(\operatorname{terminalRecord}\left(\operatorname{pow}\left(2, d + 1\right), b, p, r\right)\right)\right) = r\right)\right)\right)\right)\right) \land \left(\operatorname{card}\left(\operatorname{familyClockLabels}\left(d, b, \operatorname{sharpWait}\left(d + 1\right) + h, \operatorname{clockTag}\left(d\right)\right)\right) = \operatorname{pow}\left(2, d + 1\right) - \left(d + 1\right) + \left(Finset.Icc\left(1, d + 1\right)\right).filter\left(\lambda i: \mathbb{N} \mapsto \left(\operatorname{pow}\left(2, i\right) \le h\right)\right).card\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/DyadicDeadlineStaircase.deadline_family_closed_staircase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d and nonnegative slack h, D is sharpWait(d+1)+h and q counts indices 1<=i<=d+1 with 2^i<=h. The family consists of actual successful raw-bit protocols under D. A single decoder works for every protocol and source; clockTag and tagDecode attain the exact count on realized terminal times. The formula includes d=0, h=0, and h>=2^(d+1). It concerns receiver clock labels, not acquisition workspace or average description length.

## References

- Truth anchor: `D5/S3/Observer/Budget/DyadicDeadlineStaircase.deadline_family_closed_staircase`
- Truth anchor: `D5/S3/Observer/Budget/DyadicDeadlineStaircase.exceptional_prefix_timing`
- Dependency: [D5/S3/Observer/Budget/DyadicPrefixDelayRange](DyadicPrefixDelayRange.md)
