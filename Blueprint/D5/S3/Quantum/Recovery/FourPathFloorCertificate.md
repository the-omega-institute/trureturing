# Four-path Section 71 finite floor certificate

## Abstract

The seven rational majorants displayed in equation (71.8) of the repository's
Continuation VI theory volume all lie strictly below the common floor
`49359/40000`.

**Theorem 1.1 (Finite segment majorants).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segment_majorants_lt_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segment_majorants_lt_floor` (`✓ scoped`). ∎

*Source.* Repository theory atom `acfcfc07fe1e777c32123381853546d4bff848daa59bcaaa6e3655fa262024f1`, with chained declaration atom `5e80eb27f247f3f09a117a2dd0261302715131db6cd34a7ac7a97413f871856a`.

*Commentary.*

`segmentNonroot` and `segmentRadical` record the seven non-radical and radical
upper bounds in (71.8).  The theorem verifies by exact rational arithmetic
that their rowwise sums are below `49359/40000`.  This is a finite arithmetic
certificate for the last comparison in Section 71.  It does not define or
bound `G_-`, establish the seven geometric support bounds, or prove the energy
threshold bridge needed for Theorem 71.1; those obligations remain open.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segmentNonroot`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segmentRadical`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathFloorCertificate.segment_majorants_lt_floor`
- Source atom: `acfcfc07fe1e777c32123381853546d4bff848daa59bcaaa6e3655fa262024f1`
- Chained atom: `5e80eb27f247f3f09a117a2dd0261302715131db6cd34a7ac7a97413f871856a`
