# Coordinates of the H-family transversals

## Abstract

The cap and bulk columns and symbols of the H-family profiles have no repetitions within either region.

**Theorem 1.1 (Bulk column injectivity).**

$$\forall k \in \mathrm{Nat},\; 9 \le k \Rightarrow \left(\forall j \in \operatorname{Fin}\left(3\right),\; \forall p \in \operatorname{Prod}\left(\operatorname{Fin}\left(k - 9\right), \operatorname{Fin}\left(4\right)\right),\; \forall q \in \operatorname{Prod}\left(\operatorname{Fin}\left(k - 9\right), \operatorname{Fin}\left(4\right)\right),\; \operatorname{column}\left(k, j, \operatorname{bulkRow}\left(k, \operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right)\right) = \operatorname{column}\left(k, j, \operatorname{bulkRow}\left(k, \operatorname{fst}\left(q\right), \operatorname{snd}\left(q\right)\right)\right) \Rightarrow p = q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinHTransversals.bulk_column_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Afsane Ghafari, Ian M. Wanless (2026). *Latin Squares whose transversals intersect in unusual ways*. DOI: [10.48550/arXiv.2607.17547](https://doi.org/10.48550/arXiv.2607.17547). URL: <https://arxiv.org/abs/2607.17547v1>.

*Commentary.*

For every permitted order and profile, the four unbounded bulk classes use different column residues on distinct bulk rows, including the empty bulk at order thirty-six.

**Theorem 1.2 (Bulk symbol injectivity).**

$$\forall k \in \mathrm{Nat},\; 9 \le k \Rightarrow \left(\forall j \in \operatorname{Fin}\left(3\right),\; \forall p \in \operatorname{Prod}\left(\operatorname{Fin}\left(k - 9\right), \operatorname{Fin}\left(4\right)\right),\; \forall q \in \operatorname{Prod}\left(\operatorname{Fin}\left(k - 9\right), \operatorname{Fin}\left(4\right)\right),\; \operatorname{symbol}\left(k, j, \operatorname{bulkRow}\left(k, \operatorname{fst}\left(p\right), \operatorname{snd}\left(p\right)\right)\right) = \operatorname{symbol}\left(k, j, \operatorname{bulkRow}\left(k, \operatorname{fst}\left(q\right), \operatorname{snd}\left(q\right)\right)\right) \Rightarrow p = q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinHTransversals.bulk_symbol_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Afsane Ghafari, Ian M. Wanless (2026). *Latin Squares whose transversals intersect in unusual ways*. DOI: [10.48550/arXiv.2607.17547](https://doi.org/10.48550/arXiv.2607.17547). URL: <https://arxiv.org/abs/2607.17547v1>.

*Commentary.*

The four bulk symbol progressions likewise have no repeated residue, after the possible wrap at the order is resolved uniformly.

**Theorem 1.3 (Cap column injectivity).**

$$\forall k \in \mathrm{Nat},\; 9 \le k \Rightarrow \left(\forall j \in \operatorname{Fin}\left(3\right),\; \forall i \in \operatorname{Fin}\left(36\right),\; \forall l \in \operatorname{Fin}\left(36\right),\; \operatorname{column}\left(k, j, \operatorname{capRow}\left(k, i\right)\right) = \operatorname{column}\left(k, j, \operatorname{capRow}\left(k, l\right)\right) \Rightarrow i = l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinHTransversals.cap_column_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Afsane Ghafari, Ian M. Wanless (2026). *Latin Squares whose transversals intersect in unusual ways*. DOI: [10.48550/arXiv.2607.17547](https://doi.org/10.48550/arXiv.2607.17547). URL: <https://arxiv.org/abs/2607.17547v1>.

*Commentary.*

The thirty-six cap column pairs are distinct after modular reduction for every permitted order. The four affine complement blocks remain disjoint even near the smallest order.

**Theorem 1.4 (Cap symbol injectivity).**

$$\forall k \in \mathrm{Nat},\; 9 \le k \Rightarrow \left(\forall j \in \operatorname{Fin}\left(3\right),\; \forall i \in \operatorname{Fin}\left(36\right),\; \forall l \in \operatorname{Fin}\left(36\right),\; \operatorname{symbol}\left(k, j, \operatorname{capRow}\left(k, i\right)\right) = \operatorname{symbol}\left(k, j, \operatorname{capRow}\left(k, l\right)\right) \Rightarrow i = l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LatinHTransversals.cap_symbol_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Afsane Ghafari, Ian M. Wanless (2026). *Latin Squares whose transversals intersect in unusual ways*. DOI: [10.48550/arXiv.2607.17547](https://doi.org/10.48550/arXiv.2607.17547). URL: <https://arxiv.org/abs/2607.17547v1>.

*Commentary.*

The thirty-six cap symbol pairs are likewise distinct after modular reduction, using their exact four-block affine complement certificate.

## References

- Truth anchor: `D5/S3/Combinatorics/LatinHTransversals.bulk_column_injective`
- Truth anchor: `D5/S3/Combinatorics/LatinHTransversals.bulk_symbol_injective`
- Truth anchor: `D5/S3/Combinatorics/LatinHTransversals.cap_column_injective`
- Truth anchor: `D5/S3/Combinatorics/LatinHTransversals.cap_symbol_injective`
- Dependency: [D5/S3/Combinatorics/LatinEulerianDefs](LatinEulerianDefs.md)
