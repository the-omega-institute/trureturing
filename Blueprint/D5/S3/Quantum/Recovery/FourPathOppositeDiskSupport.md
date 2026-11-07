# Opposite four-disk support

## Abstract

A uniform complex disk support estimate for the opposite four-path coefficients.

**Theorem 1.1 (Uniform support at every scale at least two).**

$$\forall l \in \mathbb{R},\; \forall h \in \mathbb{R},\; \forall c \in \mathbb{R},\; \forall a \in \mathbb{C},\; \forall b \in \mathbb{C},\; \forall d \in \mathbb{C},\; \forall e \in \mathbb{C},\; \left(2 \le l \land \left(h^{2} = \frac{1}{2} \land \left(\frac{5}{6} \le c^{2} \land \left(c^{2} \le 1 \land \left(\operatorname{norm}\left(a\right) \le 1 \land \left(\operatorname{norm}\left(b\right) \le 1 \land \left(\operatorname{norm}\left(d\right) \le 1 \land \operatorname{norm}\left(e\right) \le 1\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{norm}\left(h \cdot \left(a - b\right) - i \cdot c \cdot \left(d - e\right)\right) + l \cdot \operatorname{Re}\left(a + b + d + e\right) \le 2 \cdot \operatorname{sqrt}\left(l^{2} + c^{2}\right) + 2 \cdot l$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathOppositeDiskSupport.four_disk_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All four complex coordinates vary independently in their closed unit disks. The three real coefficients satisfy l at least two, h squared equal to one half, and c squared between five sixths and one. No phase restriction is imposed on the coordinates.

Align the complex amplitude by one common unit scalar. The disk support inequality then bounds the expression by the sum of the norms of l plus or minus h times that scalar, and l plus or minus i c times that scalar. Write x and y for its real and imaginary parts, so that x squared plus y squared equals one.

For the real pair a,b, the product identity (ab) squared equals (l squared minus h squared) squared plus four l squared h squared y squared. Nonnegativity of (ab-(l squared-h squared)) squared and (a+b-2l) squared bounds the gain a+b-2l by l h squared y squared divided by l squared minus h squared. This is at most four y squared divided by seven l.

Put L=sqrt(l squared+c squared). The complementary pair has deficit at least l squared c squared y squared divided by L cubed, using the paired deficit estimate. Since L is at most nine l eighths and L squared is at most five l squared fourths, L cubed is at most forty-five l cubed over thirty-two. The deficit coefficient is therefore at least four divided by seven l and pays the complete real-pair gain.

The four-path coefficients h=1/sqrt(2) and c=cos(pi/8) satisfy these hypotheses: h squared equals one half and c squared equals (2+sqrt(2))/4. The displayed theorem therefore gives the uniform disk support inequality for those coefficients. Further amplitude envelopes and producer matrix inequalities require additional arguments.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FourPathOppositeDiskSupport.four_disk_support`
- Dependency: [D5/S3/Quantum/Recovery/FourPathQuadraticMajorant](FourPathQuadraticMajorant.md)
