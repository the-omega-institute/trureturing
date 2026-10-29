---
bibkey: aliabadi2025matchabilityii
authors: Mohsen Aliabadi
year: 2025
title: Conditions for matchability in groups and field extensions II
doi: 10.7151/dmgaa.1461
url: https://www.dmgaa.uz.zgora.pl/publish/pdf.php?doi=1461
claim: "Conjecture 38 proposes an uncapped lower bound for all subspace products under a premise concerning proper finite intermediate fields."
strata_touched:
  - D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation
license: citation-only
triage: anchor
---

# Subspace-product lower bound

Discussiones Mathematicae General Algebra and Applications 45 (2025),
135–157, section 5.1, Conjecture 38, printed page 154 / PDF page 20.
The same statement is Conjecture 5.1 in arXiv:2309.14664v1, section 5.1,
PDF page 14, and versions v2 and v3, PDF page 15.

> Let K ⊂ L be a field extension and A,B ⊂ L be a K-subspace of L of
> finite positive dimensions. Assume further that for every a,b ∈ L and
> every nontrivial proper finite intermediate subfield K ⊂ M ⊊ L, we have
> dim_K(aM ∩ A) + dim_K(bM ∩ B) ≤ [M:K] + 1.
> Then for all K-subspaces S ⊂ A and T ⊂ B, the following holds
> dim_K⟨ST⟩ ≥ dim_K S + dim_K T − 1.

Section 2.2 defines ⟨ST⟩ as the K-linear span of the actual product set in L.
A linear translate aM consists of the products am with m in M. Nontrivial
means M properly contains K; proper means M differs from L. There is no
restriction excluding finite ambient extensions or imposing a bound on
the sum of the two subspace dimensions. Section 5.2 concerns a separate
conjecture on Chowla subspaces.

In the quotient Q[X]/(X^7−2), Eisenstein's criterion gives a field of
degree seven. Prime degree excludes every intermediate field strictly
between Q and the quotient. Take A=B=span(alpha,...,alpha^6) and
S=T=span(alpha,...,alpha^5), where alpha is the class of X. The dimensions
are six and five respectively, and these are proper subspaces with 1
absent. The intermediate-field premise is therefore vacuous, whereas
any product span has dimension at most seven. The proposed lower bound
would require dimension at least nine. Exact equality of the product
span with the whole field is unnecessary for this contradiction.

The formal statement retains all field extensions, both finite positive
dimensions, every scalar pair, every proper nontrivial finite intermediate
field, and all pairs of contained subspaces. The selected proper subspaces
also satisfy the strict reading of the source's ordinary subset symbols.

## Source identities

- https://arxiv.org/pdf/2309.14664v3 : SHA-256
  3ffa83206a74c3f3584b3014f558255004dd126f1ed61824aaa8359910aaf957.
- Journal PDF: SHA-256
  7fdcdac53bf5fb7c6ffd685ef2ef0dc70c726d43f3836f5d92be7f4a7eca4be5.

This is a citation-only note. Project and Mathlib source retain their
existing licenses. No exhaustive literature or priority claim is made.
