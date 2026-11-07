# ProductMarginEntropyCertificate

## Abstract

A uniform high-reliability entropy certificate

**Theorem 1.1 (A uniform high-reliability entropy certificate).**

$$\forall s:\mathbb{R},\ {\frac{2}{3}\le s\land s\le 1}\implies (\frac{(1)-(s)}{(2)\times (s)})\times (\operatorname{log}(\frac{4096}{3125}))\le ((\operatorname{log}(2))-(\operatorname{h}(\frac{(1)-(s)}{(1)+(s)})))-(((3)-(\frac{2}{s}))\times ((\operatorname{log}(2))-(\operatorname{h}(\frac{(1)+(s)}{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ProductMarginEntropyCertificate.binary_entropy_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

In both formulas h denotes Real.binEntropy with natural logarithms. For every s in the closed interval [2/3,1], the binary-entropy expression in the statement is bounded below by (1-s)/(2s) times log(4096/3125). The proof applies binary entropy concavity to b=(1-s)/2 and b/(1-b), and then uses monotonicity up to 1/5. The endpoints use the actual continuous binary entropy values; no logarithm of a zero probability is differentiated.

**Theorem 1.2 (Combining the three information estimates).**

$$\forall a,b,k,j,c,d:\mathbb{R},\ {0\le a\land a\le 1\land 0\le b\land b\le 1\land 0\le k\land 0\le c\land 0\le d\land 0\le j\land k\le \frac{(1)-(\sqrt{(a)\times (b)})}{(1)+(\sqrt{(a)\times (b)})}\land j\le (b)\times (c)\land j\le (a)\times (d)\land j\le (\operatorname{log}(2))-(\operatorname{h}(\frac{(1)+(\sqrt{(a)\times (b)})}{2}))}\implies 0\le ((((\operatorname{log}(2))-(\operatorname{h}(k)))+(c))+(d))-((3)\times (j))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ProductMarginEntropyCertificate.information_budget_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

The two independent reliabilities a and b range over the entire unit interval. The conclusion combines a common trace bound with the two cross-contraction bounds and the classical absolute information bound. At a or b equal to zero, nonnegativity forces j=0. Otherwise reciprocal reliabilities split the proof into the low and high cases. This is a sufficient scalar budget: a quantum application must derive every input bound from its actual state and entropy; this statement alone does not assert that application.

## References

- Truth anchor: `D5/S3/Quantum/Information/ProductMarginEntropyCertificate.binary_entropy_certificate`
- Truth anchor: `D5/S3/Quantum/Information/ProductMarginEntropyCertificate.information_budget_nonneg`
