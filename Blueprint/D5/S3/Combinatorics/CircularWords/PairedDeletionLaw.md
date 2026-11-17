# Law Identification from Two Overlapping Paired Deletions

## Abstract

Two overlapping paired deletion channels from the same original cycle determine every finite signed law, and therefore every probability law, on the complete fixed-support carrier.

Fix a finite support A with at least four labels and distinct supported labels a, b, c. The two channels are F(C)=(D_a(C),D_b(C)) and G(C)=(D_b(C),D_c(C)); each pair is produced by the same source cycle. Rotations are identified and reversal remains distinct. In the displayed formulas, Weights(I) denotes I -> Real, pairedPushforward(a,b,X,w) is the pushforward of w through i -> (D_a(X(i)),D_b(X(i))). Probability weights are nonnegative and have total mass one.

**Theorem 1.1 (Signed law identification on every finite legal realization).**

$$\forall T \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(T\right)] \forall A \in \mathrm{Finset}\left(T\right),\; \forall a \in T,\; \forall b \in T,\; \forall c \in T,\; \forall I \in \mathrm{Type},\; [\mathrm{Fintype}\left(I\right)] \forall X \in \mathrm{Function}\left(I, \mathrm{Cycle}\left(T\right)\right),\; \forall mu \in \mathrm{Weights}\left(I\right),\; \forall nu \in \mathrm{Weights}\left(I\right),\; (((4 \le \mathrm{card}\left(A\right)) \land ((a \in A) \land ((b \in A) \land ((c \in A) \land ((\neg (a = b)) \land ((\neg (b = c)) \land (\neg (a = c)))))))) \land ((\mathrm{Injective}\left(X\right)) \land ((\forall i \in I,\; (\mathrm{Nodup}\left(\mathrm{X}\left(i\right)\right)) \land (\mathrm{toFinset}\left(\mathrm{X}\left(i\right)\right) = A)) \land ((\mathrm{pairedPushforward}\left(a, b, X, mu\right) = \mathrm{pairedPushforward}\left(a, b, X, nu\right)) \land (\mathrm{pairedPushforward}\left(b, c, X, mu\right) = \mathrm{pairedPushforward}\left(b, c, X, nu\right)))))) \Rightarrow (mu = nu)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/PairedDeletionLaw.signed_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite injective legal realization of the fixed-support cycles, equality of the two F pushforwards and equality of the two G pushforwards imply equality of the real signed weights. The proof uses the exact two-element R1 fibre classification: a non-singleton F fibre has a G-leaf, and the analogous statement holds with F and G exchanged.

FixedCycles(A) is the subtype of all nodup directed cycles C with toFinset(C)=A, modulo rotation only. The declarations fixedCycles_finite and fixedCyclesFintype supply its finite enumeration, and fixedCycles_nonempty supplies an actual legal original. In signed_injective take I=FixedCycles(A), X=Subtype.val, hi=Subtype.val_injective, hn(C)=C.property.1 and hs(C)=C.property.2. Its two channel hypotheses are exactly equality of the separate F and G pushforwards on this complete carrier. Thus all real signed source weights are identified, including nonnegative weights with total mass one. This is a direct application of the displayed theorem.

For native probability laws mu and nu on FixedCycles(A), use the discrete measurable structures and give each readout its finite range. The range-valued maps actualF(C) and actualG(C) contain the actual pairs F(C) and G(C), respectively; their value maps are injective, so restricting the codomains to these ranges preserves equality of the native readout laws. By massVector_map, equality of mu.map(actualF) and nu.map(actualF), and separately of mu.map(actualG) and nu.map(actualG), gives equality of the corresponding pushMass coordinates. A range coordinate is exactly the signed pushforward fibre sum, and every output outside the range has zero mass. Applying signed_injective with the same subtype parameters identifies massVector(mu) and massVector(nu); massVector_injective then gives mu=nu. The two pair laws are supplied separately; no joint (F,G) law is assumed. This derivation applies for arbitrary ambient DecidableEq labels and includes support size four.

A single paired channel can retain the adjacent-swap ambiguity classified in PairedDeletionFiber. The overlap through b supplies the singleton leaf that removes that ambiguity. No reversal quotient, abstract forest hypothesis, or three independent marginal law assumption is used.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/PairedDeletionLaw.signed_injective`
- Dependency: [D5/S3/Combinatorics/CircularWords/PairedDeletionFiber](PairedDeletionFiber.md)
