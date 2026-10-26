# ResponseProper

## Abstract

The domain is all triples (r,b,ε) satisfying 0<r<1, b>0 and the literal full parent equation

The domain is all triples (r,b,ε) satisfying 0<r<1, b>0 and the literal full parent equation. Its response is the actual chronological pair (P₅,P₆). ParentOverOpen restricts only by P₅≠24 and by the explicit escape barrier being nonzero. No chart, compact-source restriction, nonzero drift assumption or nonzero gain sample enters this domain.

For a compact K⊆O, bounded fifth responses give bounds for the drift, original gain and whole scaled gain. The polynomial closure over K lies in the product of the compact source box, these three bounded coordinate boxes, and K. It is closed, hence compact.

The boundary theorem forces any closure point with r=0, r=1, x=0 or x=1 onto the displayed barrier, contradicting K⊆O. The remaining source has 0<r,x,k<1. The finite lift recovers b=x/(1-x), the parent equation, the entire original gain and the actual label. Conversely every original parent over K embeds in this compact closure. Its continuous image is therefore exactly the full parent preimage of K.

The response is continuous at every strict parent, with only positive b,j,n,T as denominators. Mathlib’s compact-preimage characterization of IsProperMap is then applied directly. Properness is relative to O; no statement of properness into the full response plane is made.

OriginalWorld constructs a homeomorphism from this parent domain to literal worlds in ordinary polynomial coefficient topology. The original response commutes with this homeomorphism. Thus IsProperMap originalResponseOverOpen follows by composing full_parent_response_proper with originalParentHomeomorph.symm.isProperMap.

**Theorem 1.1 (full parent response proper).**

Lean statement: `D5/S3/Observer/CubicGain/ResponseProper.full_parent_response_proper`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/ResponseProper.full_parent_response_proper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual responseOverOpen from all strict parents over O to O is proper: the preimage of every compact K⊆O is compact. The domain includes Λ=0, zero drift, zero gain samples, lower degrees and unrestricted positive offdiagonals.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/ResponseProper.full_parent_response_proper`
- Dependency: [D5/S3/Observer/CubicGain/CompactWorld](CompactWorld.md)
