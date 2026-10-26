# Drift and rank for short literal words

## Abstract

Drift and rank for short literal words

**Theorem 1.1 (A nonzero identity needs more reads than gain coordinates).**

Lean statement: `D5/S3/Observer/Linear/GainRayShortWord.scalar_identity_read_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayShortWord.scalar_identity_read_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d, word w, fixed Readout d w C, auxiliary real matrix S and nonzero real s, suppose C annihilates the vector of ones and response(d,w,C)(S)=s times the identity of size d+1. Then d+2 is at most length(w)+1. The identity makes C surjective onto all d+1 coefficient coordinates. The nonzero vector of ones lies in its kernel, so rank-nullity requires one additional input coordinate.

**Theorem 1.2 (All rank-deficient short words are excluded).**

Lean statement: `D5/S3/Observer/Linear/GainRayShortWord.short_word_no_universal_success`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayShortWord.short_word_no_universal_success` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least one, every word w with length(w)+1 at most d+1, and every fixed C universally collinear on all World d, C succeeds at no World d. The statement includes mixed words, pure M words, pure J words and the empty action word, with the initial read included. This rank argument applies through d+1 reads.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayShortWord.scalar_identity_read_bound`
- Truth anchor: `D5/S3/Observer/Linear/GainRayShortWord.short_word_no_universal_success`
- Dependency: [D5/S3/Observer/Linear/GainRayScalarIdentity](GainRayScalarIdentity.md)
