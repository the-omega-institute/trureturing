# Johnson–Wakefield Question 6.19

## Abstract

No finite rank-three nonmodular matroid has zero J-Möbius evaluation at minus one.

**Definition 1.1 (Flats).**

$$\forall (A: Type), \forall (M: Matroid\left(A\right)), Flats\left(M\right) = Subtype\left((F: Set\left(A\right) \mapsto \operatorname{M}.\operatorname{IsFlat}\left(F\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.Flats` (`✓ std3`).

*Citation.* John Johnson; Max Wakefield (2024). *A non-associative incidence near-ring with a generalized Möbius function*. DOI: [10.26493/1855-3974.2894.b07](https://doi.org/10.26493/1855-3974.2894.b07). URL: <https://arxiv.org/abs/2204.07158v1>.

*Commentary.*

The lattice L(M) consists of the flats of M, ordered by inclusion. A flat is Mathlib's Matroid.IsFlat; the subtype retains this predicate.

**Definition 1.2 (rk).**

$$\forall (A: Type), \forall (M: Matroid\left(A\right)), \forall (F: Set\left(A\right)), rk\left(M, F\right) = \operatorname{ENat}.\operatorname{toNat}\left(\operatorname{M}.\operatorname{eRk}\left(F\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.rk` (`✓ std3`).

*Citation.* John Johnson; Max Wakefield (2024). *A non-associative incidence near-ring with a generalized Möbius function*. DOI: [10.26493/1855-3974.2894.b07](https://doi.org/10.26493/1855-3974.2894.b07). URL: <https://arxiv.org/abs/2204.07158v1>.

*Commentary.*

The natural-number rank is ENat.toNat of Matroid.eRk. The theorem concerns finite carriers, so all these extended ranks are finite.

**Definition 1.3 (IsJFunction).**

$$\forall (A: Type), \forall (M: Matroid\left(A\right)), \forall (J: Flats\left(M\right) \to \left(Flats\left(M\right) \to \left(Flats\left(M\right) \to \mathbb{Z}\right)\right)), (IsJFunction\left(M, J\right)) \Leftrightarrow (\forall (x: Flats\left(M\right)), \forall (y: Flats\left(M\right)), \forall (z: Flats\left(M\right)), (x \le y) \Rightarrow ((y \le z) \Rightarrow (\left(\sum^{f}\right)_{(a: Flats\left(M\right))} (\left(\sum^{f}\right)_{((x \le a) \land (a \le y))} (\left(\sum^{f}\right)_{(b: Flats\left(M\right))} (\left(\sum^{f}\right)_{((y \le b) \land (b \le z))} (J\left(a, y, b\right))))) = ite\left((x = y) \land (y = z), 1, 0\right))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.IsJFunction` (`✓ std3`).

*Citation.* John Johnson; Max Wakefield (2024). *A non-associative incidence near-ring with a generalized Möbius function*. DOI: [10.26493/1855-3974.2894.b07](https://doi.org/10.26493/1855-3974.2894.b07). URL: <https://arxiv.org/abs/2204.07158v1>.

*Commentary.*

Page 11, Definition 5.1: “Define J : Fl_3(P) → Z for all fixed (x, y, z) ∈ Fl_3(P) by Σ_{(a,b)⊴(x,y,z)} J(a, y, b) = δ_3(x, y, z).” Section 3 states: “(a, b) ⊴ (x, y, z) means x ≤ a ≤ y ≤ b ≤ z in P.” The proof-indexed finsums impose precisely these inequalities; ite is one at x = y = z and zero otherwise. Values away from partial flags are irrelevant.

**Definition 1.4 (MoebiusPoly).**

$$\forall (A: Type), \forall (M: Matroid\left(A\right)), \forall (J: Flats\left(M\right) \to \left(Flats\left(M\right) \to \left(Flats\left(M\right) \to \mathbb{Z}\right)\right)), MoebiusPoly\left(M, J\right) = \left(\sum^{f}\right)_{(x: Flats\left(M\right))} (\left(\sum^{f}\right)_{(y: Flats\left(M\right))} (\left(\sum^{f}\right)_{(z: Flats\left(M\right))} (\left(\sum^{f}\right)_{((x \le y) \land (y \le z))} (\operatorname{Polynomial}.\operatorname{C}\left(J\left(x, y, z\right)\right) \cdot \operatorname{Polynomial}.\operatorname{X}^{3 \cdot rk\left(M, \operatorname{M}.\operatorname{E}\right) - rk\left(M, val\left(x\right)\right) - rk\left(M, val\left(y\right)\right) - rk\left(M, val\left(z\right)\right)}))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.MoebiusPoly` (`✓ std3`).

*Citation.* John Johnson; Max Wakefield (2024). *A non-associative incidence near-ring with a generalized Möbius function*. DOI: [10.26493/1855-3974.2894.b07](https://doi.org/10.26493/1855-3974.2894.b07). URL: <https://arxiv.org/abs/2204.07158v1>.

*Commentary.*

Page 14, Definition 6.2: “Let P be a ranked finite poset and for (x, y, z) ∈ Fl_3(P) let ρ(x, y, z) = 3rk(P) − rk(x) − rk(y) − rk(z). The J-Möbius polynomial of P is M(P, t) = Σ_{(x,y,z)∈Fl_3(P)} J(x, y, z)t^{ρ(x,y,z)}.” Here P is Flats M, its top rank is rk M M.E, and the coefficient ring is ℤ. Subtractions in the exponent are natural-number subtractions; for the finite matroids in the theorem, rank bounds prevent truncation on flags.

**Definition 1.5 (Connected).**

$$\forall (A: Type), \forall (M: Matroid\left(A\right)), (Connected\left(M\right)) \Leftrightarrow (\forall (e: A), (e \in \operatorname{M}.\operatorname{E}) \Rightarrow (\forall (f: A), (f \in \operatorname{M}.\operatorname{E}) \Rightarrow ((e \ne f) \Rightarrow (\exists (C: Set\left(A\right)), (\operatorname{M}.\operatorname{IsCircuit}\left(C\right)) \land ((e \in C) \land (f \in C))))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.Connected` (`✓ std3`).

*Citation.* John Johnson; Max Wakefield (2024). *A non-associative incidence near-ring with a generalized Möbius function*. DOI: [10.26493/1855-3974.2894.b07](https://doi.org/10.26493/1855-3974.2894.b07). URL: <https://arxiv.org/abs/2204.07158v1>.

*Commentary.*

Every two distinct ground elements belong to a common circuit. This is the connectedness hypothesis of Question 6.19; the nonvanishing argument also applies when this hypothesis is omitted.

**Definition 1.6 (Modular).**

$$\forall (A: Type), \forall (M: Matroid\left(A\right)), (Modular\left(M\right)) \Leftrightarrow (\forall (F: Set\left(A\right)), \forall (G: Set\left(A\right)), (\operatorname{M}.\operatorname{IsFlat}\left(F\right)) \Rightarrow ((\operatorname{M}.\operatorname{IsFlat}\left(G\right)) \Rightarrow (\operatorname{M}.\operatorname{eRk}\left(F\right) + \operatorname{M}.\operatorname{eRk}\left(G\right) = \operatorname{M}.\operatorname{eRk}\left(\operatorname{Set}.\operatorname{union}\left(F, G\right)\right) + \operatorname{M}.\operatorname{eRk}\left(\operatorname{Set}.\operatorname{inter}\left(F, G\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.Modular` (`✓ std3`).

*Citation.* John Johnson; Max Wakefield (2024). *A non-associative incidence near-ring with a generalized Möbius function*. DOI: [10.26493/1855-3974.2894.b07](https://doi.org/10.26493/1855-3974.2894.b07). URL: <https://arxiv.org/abs/2204.07158v1>.

*Commentary.*

Every pair of flats satisfies r(F) + r(G) = r(F ∪ G) + r(F ∩ G). Ranks in this equality are the extended natural Matroid.eRk values. Disjoint rank-two flats in the proof have a rank-zero intersection, which may contain loops.

**Definition 1.7 (claim).**

$$(claim) \Leftrightarrow (\forall (A: Type), [Finite\left(A\right)] \forall (M: Matroid\left(A\right)), (\operatorname{M}.\operatorname{eRank} = 3) \Rightarrow ((Connected\left(M\right)) \Rightarrow ((\neg (Modular\left(M\right))) \Rightarrow (\forall (J: Flats\left(M\right) \to \left(Flats\left(M\right) \to \left(Flats\left(M\right) \to \mathbb{Z}\right)\right)), (IsJFunction\left(M, J\right)) \Rightarrow (\operatorname{Polynomial}.\operatorname{eval}\left((-1), MoebiusPoly\left(M, J\right)\right) \ne 0)))))$$

*Formalization.* `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.claim` (`✓ std3`).

*Citation.* John Johnson; Max Wakefield (2024). *A non-associative incidence near-ring with a generalized Möbius function*. DOI: [10.26493/1855-3974.2894.b07](https://doi.org/10.26493/1855-3974.2894.b07). URL: <https://arxiv.org/abs/2204.07158v1>.

*Commentary.*

Page 20, Question 6.19: “Is there a rank 3 non-modular connected matroid M such that M(M, −1) = 0?” The proposition is its negative answer for finite matroids: every function satisfying Definition 5.1 has nonzero evaluation. The carrier is a finite Type, and rank three is M.eRank = 3.

**Theorem 1.8 (result).**

$$\forall (A: Type), [Finite\left(A\right)] \forall (M: Matroid\left(A\right)), (\operatorname{M}.\operatorname{eRank} = 3) \Rightarrow ((Connected\left(M\right)) \Rightarrow ((\neg (Modular\left(M\right))) \Rightarrow (\forall (J: Flats\left(M\right) \to \left(Flats\left(M\right) \to \left(Flats\left(M\right) \to \mathbb{Z}\right)\right)), (IsJFunction\left(M, J\right)) \Rightarrow (\operatorname{Polynomial}.\operatorname{eval}\left((-1), MoebiusPoly\left(M, J\right)\right) \ne 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.result` (`✓ std3`). ∎

*Resolves.* `Problems/johnson-wakefield-2022-rank-three-moebius-question-6-19` (proved) by `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"johnson-wakefield-2022-rank-three-moebius-question-6-19","declaration_gid":"D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* John Johnson; Max Wakefield (2024). *A non-associative incidence near-ring with a generalized Möbius function*. DOI: [10.26493/1855-3974.2894.b07](https://doi.org/10.26493/1855-3974.2894.b07). URL: <https://arxiv.org/abs/2204.07158v1>.

*Commentary.*

The identity at minus one is twice the difference between the numbers of rank-two and rank-one flats. A nonmodular rank-three matroid has two lines whose intersection has rank zero. The finite configuration theorem gives at least as many lines as points. Its equality case forces every pair of distinct lines to meet in a point, contradicting the rank-zero intersection; therefore there are strictly more lines than points. The J function exists as the product of ordinary Möbius values and is unique on flags. Connectedness is unnecessary. No assertion about the classification in arbitrary rank is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.Connected`
- Truth anchor: `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.Flats`
- Truth anchor: `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.IsJFunction`
- Truth anchor: `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.Modular`
- Truth anchor: `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.MoebiusPoly`
- Truth anchor: `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.claim`
- Truth anchor: `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.result`
- Truth anchor: `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.rk`
