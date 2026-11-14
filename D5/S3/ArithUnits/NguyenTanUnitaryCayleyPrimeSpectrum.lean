/- GID: D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum
   generality: I
   mirror-B: D5/B/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Prime connected unitary Cayley graphs can have a zero adjacency eigenvalue. -/

/-
proof_shape: result: content (finite-coordinate reachability and homogeneous-set obstruction).
escape_witness: none; the settling result supplies the open-problem admission basis.
admission_basis: open-problem-resolution (#20113; Refuted)
Direct frozen dependencies (declaration statement_id, not module pins):
F1: D5.S3.Combinatorics.Hamming.HammingMultipartitePartition.graph sha256:487d20c8cf341ee8c48b760a64dcfd05a33c611e52e0566ea64f6963234125c1
F2: D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.F₂ sha256:e975fc48104d0cb1a40271fdfb5ec7fcfe2730a1c600ee81758d5e89253bd60f
F3: D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.complexSign sha256:be75490b6271d1c0ab3bf4b4e1c2705e4087c35ef7d026ab0728ba497a35c462
F4: D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.complexSign_add sha256:165f332c4b0e836706fee2269d7361697b5c57fc9b98de2e37dd32d652f28053
F5: D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_one sha256:0355cd4cbd79b4a5996a70aa7afdcc9bd66287ac5dfa389cafd0b01014d39a89
F6: InducedSubcubes.invariant_of_toggles (private owner before publication)
  declaration statement_id sha256:96d8aadcf63c3cfae8d8a2177c958ed8ade3d4a0a547c982d9fad2f548aa4788.
  The public source owner is reused here; its canonical re-pin belongs to Stage B.
Per-declaration classification; F-keys refer to the identities above.
IsFrobenius: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: claim, group_algebra_counterexample, result.
unitaryCayley: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cayleyIso, cayley_adj_iff, claim, group_algebra_counterexample, result, unitary_cayley_as_add_cayley.
IsHomogeneousSet: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: IsPrimeGraph, prime_of_iso, prime_of_triangle_free_twin_free.
IsPrimeGraph: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: claim, group_algebra_counterexample, prime_of_iso, result.
HasZeroEigenvalue: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: claim, result.
claim: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: result.
zeroEigenvalue_iff: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cube_zero_eigenvalue, result, zero_eigenvalue_of_iso.
cube: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1; consumers: adj_iff_flip, cayleyIso, cayley_adj_iff, character_mulVec, compl_adj_of_two_differences, cube_adj, cube_complement_connected, cube_connected, cube_neighbors, cube_prime, cube_triangle_free, cube_twin_free, cube_zero_eigenvalue, difference_iff, flip_adj, group_algebra_counterexample.
cube_adj: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1; consumers: adj_iff_flip, compl_adj_of_two_differences, cube_triangle_free, cube_twin_free, difference_iff, flip_adj.
bit_step: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: adj_iff_flip, bit_sub_one, bit_third, cube_twin_free.
bit_third: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cube_triangle_free.
flip_adj: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1; consumers: adj_iff_flip, cube_connected, cube_twin_free.
adj_iff_flip: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1; consumers: cube_neighbors.
cube_triangle_free: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1; consumers: cube_prime.
coordinate_connected: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F6; consumers: cube_complement_connected, cube_connected.
cube_connected: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1,F6; consumers: cube_prime, group_algebra_counterexample.
groupAlgebraFintype: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: group_algebra_counterexample, result.
coeffEquiv: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cayleyIso, cayley_adj_iff, difference_iff.
basisSubgroup: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cayleyIso, cayley_adj_iff, group_algebra_counterexample, minus_one_mem, result.
ring_frobenius: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: group_algebra_counterexample.
minus_one_mem: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: group_algebra_counterexample.
prime_of_triangle_free_twin_free: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cube_prime.
two_others: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cube_complement_connected, cube_twin_free.
cube_twin_free: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1; consumers: cube_prime.
cube_prime: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: F1,F6; consumers: group_algebra_counterexample.
compl_adj_of_two_differences: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1; consumers: cube_complement_connected.
cube_complement_connected: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: F1,F6; consumers: group_algebra_counterexample.
bit_sub_one: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: difference_iff.
difference_iff: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1; consumers: cayley_adj_iff.
unitary_cayley_as_add_cayley: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: cayley_adj_iff.
cayley_adj_iff: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1; consumers: cayleyIso.
cayleyIso: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1; consumers: group_algebra_counterexample.
character: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F3; consumers: character_flip, character_mulVec, cube_zero_eigenvalue.
sign_step: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F5,F4,F2,F3; consumers: character_flip.
character_flip: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F5,F4,F2,F3; consumers: character_mulVec.
flip_injective: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: character_mulVec.
cube_neighbors: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1; consumers: character_mulVec.
character_mulVec: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F5,F4,F2,F3,F1; consumers: cube_zero_eigenvalue.
cube_zero_eigenvalue: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F5,F4,F2,F3,F1; consumers: group_algebra_counterexample.
zero_eigenvalue_of_iso: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: group_algebra_counterexample.
prime_of_iso: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: group_algebra_counterexample.
group_algebra_counterexample: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: F5,F4,F2,F3,F1,F6; consumers: even_cyclic_family.
even_cyclic_family: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: F5,F4,F2,F3,F1,F6; consumers: result.
result: proof_shape: content; escape_witness: none;
  Direct frozen dependencies: F5,F4,F2,F3,F1,F6; consumers: terminal settling result.
The graph is the pullback of HammingMultipartitePartition.graph through Fintype.equivFin;
cube_adj supplies its coordinate predicate. The scalar signs use the existing complexSign.
The literal source definitions and the affirmative claim retain their original expressions.
unitary_cayley_as_add_cayley identifies the source graph with SimpleGraph.addCayley;
cayley_adj_iff applies its adjacency theorem. coordinate_connected applies the
published InducedSubcubes.invariant_of_toggles to the connected-component quotient.
HasZeroEigenvalue retains the source expression; zeroEigenvalue_iff connects that
expression to the existing Module.End.HasEigenvalue used throughout the proof.
The group-algebra family is proved for every finite commutative group of even cardinality
at least three; the cyclic instance specializes this family. No polynomial-quotient
isomorphism, complete eigenbasis, or general zero-eigenvalue multiplicity is asserted.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20113.
Utility none: an unbounded family and structural graph arguments settle the question;
the characteristic-two scalar calculations are internal normalization steps.
-/

import D5.S3.Combinatorics.Hamming.HammingMultipartitePartition
import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
import Mathlib.Combinatorics.SimpleGraph.Cayley
import D5.S3.Combinatorics.Hamming.InducedSubcubes

/-! Binding conventions for T. T. Nguyen and N. D. Tân, "Supercharacters of finite abelian groups and applications to
spectra of U-unitary Cayley graphs", arXiv:2508.10348v1 (14 August 2025).

* §3.1: "Let R be a finite commutative ring … we fix a subgroup U of R× such that −1 ∈ U"; `Γ(R, S)` is the Cayley
  graph on `(R, +)`, so `Γ(R, U)` joins `a` and `b` when `a − b ∈ U`.
* §3.2–3.3: "connected and anti-connected (meaning that its complement is connected)".
* §3.3: "A subset X in a graph G is called a homogeneous set if every vertex in V(G) \ X is adjacent to either all or
  none of the vertices in X. … A homogeneous set X with 2 ≤ |X| < |V(G)| is called non-trivial. The graph G is said
  to be prime if it does not contain any non-trivial homogeneous sets."
* §4.1: "being Frobenius means that R is a Z/n algebra equipped with a non-degenerate Z/n linear functional
  ψ : R → Z/n. Here, non-degenerate means that the kernel of ψ does not contain any non-zero ideal in R."
* Question 4.17: "Suppose that Γ(R, U) is both connected and anti-connected. Is it true that Γ(R, U) is prime if and
  only if 0 is not an eigenvalue?" Eigenvalues are those of the adjacency matrix. -/

open Classical

namespace D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum

open SimpleGraph

/-- §4.1: `R` is a `ℤ/n`-algebra with a `ℤ/n`-linear functional whose kernel contains no non-zero ideal. -/
def IsFrobenius (R : Type*) [CommRing R] : Prop :=
  ∃ n : ℕ, (n : R) = 0 ∧ ∃ ψ : R →+ ZMod n, ∀ I : Ideal R, (∀ x ∈ I, ψ x = 0) → I = ⊥

/-- `Γ(R, U)`: the Cayley graph on `(R, +)` with connection set `U`. -/
def unitaryCayley (R : Type*) [CommRing R] (U : Subgroup Rˣ) : SimpleGraph R :=
  SimpleGraph.fromRel fun a b => ∃ u ∈ U, a - b = (u : R)

/-- §3.3: every vertex outside `X` is adjacent to all or to none of `X`. -/
def IsHomogeneousSet {V : Type*} (G : SimpleGraph V) (X : Set V) : Prop :=
  ∀ v ∉ X, (∀ x ∈ X, G.Adj v x) ∨ (∀ x ∈ X, ¬ G.Adj v x)

/-- §3.3: `G` has no homogeneous set `X` with `2 ≤ |X| < |V(G)|`. -/
def IsPrimeGraph {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ X : Finset V, IsHomogeneousSet G (X : Set V) → X.card < 2 ∨ X.card = Fintype.card V

open Classical in
/-- `0` is an eigenvalue of the adjacency matrix of `G`. -/
def HasZeroEigenvalue {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ v : V → ℂ, v ≠ 0 ∧ (G.adjMatrix ℂ).mulVec v = 0

/-- Question 4.17, affirmative form: for a finite commutative Frobenius ring `R` and a subgroup `U ≤ R×` containing
`−1` with `Γ(R, U)` connected and anti-connected, `Γ(R, U)` is prime if and only if `0` is not an eigenvalue. -/
def claim : Prop :=
  ∀ (R : Type) [CommRing R] [Fintype R], IsFrobenius R →
    ∀ U : Subgroup Rˣ, -1 ∈ U → (unitaryCayley R U).Connected → (unitaryCayley R U)ᶜ.Connected →
      (IsPrimeGraph (unitaryCayley R U) ↔ ¬ HasZeroEigenvalue (unitaryCayley R U))

end D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum

namespace D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum
open SimpleGraph

private theorem zeroEigenvalue_iff {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (∃ v : V → ℂ, v ≠ 0 ∧ (G.adjMatrix ℂ).mulVec v = 0) ↔
      Module.End.HasEigenvalue (G.adjMatrix ℂ).mulVecLin (0 : ℂ) := by
  classical
  rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
  simp only [Module.End.mem_eigenspace_iff, zero_smul,
    Matrix.mulVecLin_apply, and_comm]

private noncomputable def cube (ι : Type*) [Fintype ι] : SimpleGraph (ι → ZMod 2) :=
  (D5.S3.Combinatorics.Hamming.HammingMultipartitePartition.graph
    (fun _ : Fin (Fintype.card ι) => 2)).comap
      (fun x i => x ((Fintype.equivFin ι).symm i))

private theorem cube_adj {ι : Type*} [Fintype ι] (x y : ι → ZMod 2) :
    (cube ι).Adj x y ↔ ∃ i, x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j := by
  classical
  let e := Fintype.equivFin ι
  change (∃ i : Fin (Fintype.card ι), x (e.symm i) ≠ y (e.symm i) ∧
    ∀ j, j ≠ i → x (e.symm j) = y (e.symm j)) ↔ _
  constructor
  · rintro ⟨i, hi, h⟩
    refine ⟨e.symm i, hi, ?_⟩
    intro j hj
    have hji : e j ≠ i := fun he => hj (e.injective (by simpa using he))
    simpa using h (e j) hji
  · rintro ⟨i, hi, h⟩
    refine ⟨e i, by simpa using hi, ?_⟩
    intro j hj
    exact h (e.symm j) (fun he => hj (by simpa using congrArg e he))

private lemma bit_step (a b : (ZMod 2)) : a ≠ b ↔ b = a + 1 := (by decide : ∀ a b : ZMod 2, a ≠ b ↔ b = a + 1) a b
private lemma bit_third (a b c : (ZMod 2)) (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
  rw [bit_step] at hab hbc
  simpa [hab, CharTwo.add_cancel_right] using hbc.symm

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

private lemma flip_adj (x : ι → (ZMod 2)) (i : ι) : (cube ι).Adj x ((fun (x : ι → ZMod 2) (i : ι) => Function.update x i (x i + 1)) x i) := by
  rw [cube_adj]
  refine ⟨i, ?_, ?_⟩
  · simp []
  · intro j hj; simp [hj]

private lemma adj_iff_flip (x y : ι → (ZMod 2)) : (cube ι).Adj x y ↔ ∃ i, y = (fun (x : ι → ZMod 2) (i : ι) => Function.update x i (x i + 1)) x i := by
  rw [cube_adj]
  constructor
  · rintro ⟨i, hi, h⟩
    refine ⟨i, ?_⟩
    apply Function.eq_update_iff.mpr
    exact ⟨(bit_step _ _).mp hi, fun j hj => (h j hj).symm⟩
  · rintro ⟨i, rfl⟩; exact (cube_adj _ _).mp (flip_adj x i)

private lemma cube_triangle_free (x y z : ι → (ZMod 2)) (hxy : (cube ι).Adj x y)
    (hyz : (cube ι).Adj y z) : ¬ (cube ι).Adj x z := by
  rw [cube_adj] at hxy hyz ⊢
  rintro ⟨k, hk, hrest⟩
  obtain ⟨i, hi, hxi⟩ := hxy
  obtain ⟨j, hj, hyj⟩ := hyz
  by_cases hij : i = j
  · subst j
    have heq : x = z := by
      funext t
      by_cases ht : t = i
      · subst t; exact bit_third _ _ _ hi hj
      · exact (hxi t ht).trans (hyj t ht)
    exact hk (congrFun heq k)
  · have hne_i : x i ≠ z i := ne_of_ne_of_eq hi (hyj i hij)
    have hne_j : x j ≠ z j := ne_of_eq_of_ne (hxi j (Ne.symm hij)) hj
    have hik : i = k := Decidable.of_not_not (fun h => hne_i (hrest i h))
    have hjk : j = k := Decidable.of_not_not (fun h => hne_j (hrest j h))
    exact hij (hik.trans hjk.symm)

private lemma coordinate_connected (G : SimpleGraph (ι → (ZMod 2)))
    (hstep : ∀ x i, G.Reachable x ((fun (x : ι → ZMod 2) (i : ι) => Function.update x i (x i + 1)) x i)) : G.Connected := by
  classical
  let e : Bool ≃ ZMod 2 := finTwoEquiv.symm.trans (ZMod.finEquiv 2).toEquiv
  let lift : (ι → Bool) → (ι → ZMod 2) := fun u i => e (u i)
  have he : ∀ b : Bool, e (!b) = e b + 1 := by decide
  have ht (u : ι → Bool) (i : ι) :
      lift (Function.update u i (!u i)) = Function.update (lift u) i (lift u i + 1) := by
    simpa only [lift, Function.comp_def, he] using Function.comp_update e u i (!u i)
  let g := fun u : ι → Bool => G.connectedComponentMk (lift u)
  have hg : ∀ u i, g (Function.update u i (!u i)) = g u := by
    intro u i
    change G.connectedComponentMk (lift (Function.update u i (!u i))) = G.connectedComponentMk (lift u)
    rw [ht]
    exact (SimpleGraph.ConnectedComponent.sound (hstep (lift u) i)).symm
  refine { preconnected := fun x y => ?_ }
  apply SimpleGraph.ConnectedComponent.exact
  have hh := D5.S3.Combinatorics.Hamming.InducedSubcubes.invariant_of_toggles g hg (fun i => e.symm (x i)) (fun i => e.symm (y i))
  simpa only [g, lift, Equiv.apply_symm_apply] using hh


private lemma cube_connected : (cube ι).Connected :=
  coordinate_connected _ (fun x i => (flip_adj x i).reachable)

end D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum

namespace D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum
open D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum
variable (G : Type) [CommGroup G]
private noncomputable instance groupAlgebraFintype [Fintype G] : Fintype (MonoidAlgebra (ZMod 2) G) := by
  classical
  exact Fintype.ofEquiv (G →₀ (ZMod 2)) MonoidAlgebra.coeffEquiv.symm
private noncomputable def coeffEquiv [Fintype G] : MonoidAlgebra (ZMod 2) G ≃ (G → (ZMod 2)) :=
  MonoidAlgebra.coeffEquiv.trans Finsupp.equivFunOnFinite

private noncomputable def basisSubgroup : Subgroup (MonoidAlgebra (ZMod 2) G)ˣ := ((MonoidAlgebra.of (ZMod 2) G).toHomUnits).range


private lemma ring_frobenius : IsFrobenius (MonoidAlgebra (ZMod 2) G) := by
  refine ⟨2, ?_, (Finsupp.applyAddHom (1 : G)).comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom, ?_⟩
  · have h : (2 : ZMod 2) = 0 := CharTwo.two_eq_zero
    simpa only [map_ofNat, map_zero, Nat.cast_ofNat] using congrArg (MonoidAlgebra.singleOneRingHom (R := (ZMod 2)) (M := G)) h
  · intro I hI
    apply le_antisymm _ bot_le
    intro a ha
    change a = 0
    ext g
    have h := hI (MonoidAlgebra.single g⁻¹ 1 * a) (I.mul_mem_left _ ha)
    change (MonoidAlgebra.single g⁻¹ (1 : (ZMod 2)) * a).coeff 1 = 0 at h
    rw [MonoidAlgebra.coeff_single_mul_apply] at h
    simpa only [inv_inv, mul_one, one_mul, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h

private lemma minus_one_mem : (-1 : (MonoidAlgebra (ZMod 2) G)ˣ) ∈ basisSubgroup G := by
  have hn : (-1 : MonoidAlgebra (ZMod 2) G) = 1 := ZModModule.neg_eq_self 1
  have hu : (-1 : (MonoidAlgebra (ZMod 2) G)ˣ) = 1 := Units.ext hn
  rw [hu]
  exact (basisSubgroup G).one_mem

end D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum

namespace D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum
open SimpleGraph D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum

private lemma prime_of_triangle_free_twin_free {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj x z)
    (htwin : ∀ x y, (∀ z, G.Adj z x ↔ G.Adj z y) → x = y) : IsPrimeGraph G := by
  classical
  intro X hX
  by_cases hsmall : X.card < 2
  · exact Or.inl hsmall
  right
  have hlarge : 1 < X.card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hlarge
  by_contra hfull
  have independent : ∀ a ∈ X, ∀ b ∈ X, ¬ G.Adj a b := by
    intro a ha b hb hab
    have closed : ∀ u ∈ X, ∀ v, G.Adj u v → v ∈ X := by
      intro u hu v huv
      by_contra hv
      rcases hX v hv with hall | hnone
      · exact htri v a b (hall a ha) hab (hall b hb)
      · exact hnone u hu huv.symm
    have propagation {u v : V} (r : G.Reachable u v) : u ∈ X → v ∈ X := by
      intro hu
      exact r.mem_subgraphVerts (H := (⊤ : G.Subgraph).induce (X : Set V))
        (fun w hw t hwt => ⟨hw, closed w hw t hwt, hwt⟩) hu
    have heq : X = Finset.univ := Finset.eq_univ_iff_forall.mpr
      (fun v => propagation (hconn a v) ha)
    exact hfull (by simp [heq])
  apply hxy
  apply htwin x y
  intro z
  by_cases hz : z ∈ X
  · exact iff_of_false (independent z hz x hx) (independent z hz y hy)
  · rcases hX z hz with hall | hnone
    · exact iff_of_true (hall x hx) (hall y hy)
    · exact iff_of_false (hnone x hx) (hnone y hy)

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
private lemma two_others (hc : 3 ≤ Fintype.card ι) (i : ι) :
    ∃ j k : ι, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
  have hcard : 1 < (Finset.univ.erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    omega
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hcard
  exact ⟨j, k, (Finset.mem_erase.mp hj).1, (Finset.mem_erase.mp hk).1, hjk⟩

private lemma cube_twin_free (hc : 3 ≤ Fintype.card ι) (x y : ι → (ZMod 2))
    (ht : ∀ z, (cube ι).Adj z x ↔ (cube ι).Adj z y) : x = y := by
  by_contra hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  obtain ⟨j, k, hji, hki, hjk⟩ := two_others hc i
  have diff (t : ι) (hti : t ≠ i) : x t ≠ y t := by
    obtain ⟨l, hl, hr⟩ := (cube_adj _ _).mp ((ht ((fun (x : ι → ZMod 2) (i : ι) => Function.update x i (x i + 1)) x t)).mp (flip_adj x t).symm)
    have hil : i = l := by
      by_contra hil
      exact hi (by simpa [(Ne.symm hti)] using hr i hil)
    have htl : t ≠ l := by rwa [← hil]
    have he : x t + 1 = y t := by simpa [] using hr t htl
    intro h
    exact ((bit_step (x t) (x t + 1)).mpr rfl) (h.trans he.symm)
  obtain ⟨l, hl, hr⟩ := (cube_adj _ _).mp ((ht ((fun (x : ι → ZMod 2) (i : ι) => Function.update x i (x i + 1)) x j)).mp (flip_adj x j).symm)
  have hil : i = l := by
    by_contra hil
    exact hi (by simpa [(Ne.symm hji)] using hr i hil)
  exact diff k hki (by simpa [(Ne.symm hjk)] using hr k (by rwa [← hil]))

private lemma cube_prime (hc : 3 ≤ Fintype.card ι) : IsPrimeGraph (cube ι) :=
  prime_of_triangle_free_twin_free _ cube_connected cube_triangle_free (cube_twin_free hc)

end D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum

namespace D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum
open SimpleGraph
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

private lemma compl_adj_of_two_differences {x y : ι → (ZMod 2)} {i j : ι} (hij : i ≠ j)
    (hi : x i ≠ y i) (hj : x j ≠ y j) : (cube ι)ᶜ.Adj x y := by
  simp only [SimpleGraph.compl_adj, cube_adj]
  refine ⟨fun h => hi (congrFun h i), ?_⟩
  rintro ⟨k, hk, hr⟩
  have hik : i = k := Decidable.of_not_not (fun h => hi (hr i h))
  have hjk : j = k := Decidable.of_not_not (fun h => hj (hr j h))
  exact hij (hik.trans hjk.symm)

private lemma cube_complement_connected (hc : 3 ≤ Fintype.card ι) : (cube ι)ᶜ.Connected := by
  apply coordinate_connected
  intro x i
  obtain ⟨j, k, hji, hki, hjk⟩ := two_others hc i
  let w := (fun (x : ι → ZMod 2) (i : ι) => Function.update x i (x i + 1)) ((fun (x : ι → ZMod 2) (i : ι) => Function.update x i (x i + 1)) x j) k
  have hxw : (cube ι)ᶜ.Adj x w := by
    apply compl_adj_of_two_differences hjk
    · simp [w, hjk]
    · simp [w, Ne.symm hjk]
  have hwy : (cube ι)ᶜ.Adj w ((fun (x : ι → ZMod 2) (i : ι) => Function.update x i (x i + 1)) x i) := by
    apply compl_adj_of_two_differences hjk
    · simp [w, hjk, hji]
    · simp [w, Ne.symm hjk, hki]
  exact hxw.reachable.trans hwy.reachable
end D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum

namespace D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum
open SimpleGraph D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum
variable (G : Type) [CommGroup G] [Fintype G] [DecidableEq G]

private lemma bit_sub_one (a b : (ZMod 2)) : a - b = 1 ↔ a ≠ b := by
  constructor
  · intro h hab
    subst b
    simp at h
  · intro h
    rw [(bit_step a b).mp h, CharTwo.sub_eq_add, ← add_assoc,
      CharTwo.add_self_eq_zero, zero_add]

private lemma difference_iff (a b : MonoidAlgebra (ZMod 2) G) :
    (∃ g, a - b = MonoidAlgebra.single g 1) ↔
      (cube G).Adj (coeffEquiv G a) (coeffEquiv G b) := by
  rw [cube_adj]
  constructor
  · rintro ⟨g, h⟩
    have hc (t : G) := congrArg (fun c : MonoidAlgebra (ZMod 2) G => c.coeff t) h
    refine ⟨g, ?_, ?_⟩
    · apply (bit_sub_one _ _).mp
      simpa [coeffEquiv] using hc g
    · intro t ht
      apply sub_eq_zero.mp
      simpa [coeffEquiv, Finsupp.single_apply, ht] using hc t
  · rintro ⟨i, hi, hr⟩
    refine ⟨i, ?_⟩
    ext g
    by_cases hgi : g = i
    · subst g
      simpa [coeffEquiv] using (bit_sub_one _ _).mpr hi
    · have he : a.coeff g = b.coeff g := hr g hgi
      simp [hgi, he]

private lemma unitary_cayley_as_add_cayley (R : Type*) [CommRing R] (U : Subgroup Rˣ) :
    unitaryCayley R U = SimpleGraph.addCayley (Units.val '' (U : Set Rˣ)) := by
  classical
  ext a b
  simp only [unitaryCayley, SimpleGraph.fromRel_adj, SimpleGraph.addCayley_adj',
    Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨hne, ⟨u, hu, h⟩ | ⟨u, hu, h⟩⟩
    · exact ⟨hne, u, ⟨u, hu, rfl⟩, Or.inr ((sub_eq_iff_eq_add.mp h).trans (add_comm _ _))⟩
    · exact ⟨hne, u, ⟨u, hu, rfl⟩, Or.inl ((add_comm _ _).trans (sub_eq_iff_eq_add.mp h).symm)⟩
  · rintro ⟨hne, v, ⟨u, hu, rfl⟩, h | h⟩
    · exact ⟨hne, Or.inr ⟨u, hu, sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm _ _))⟩⟩
    · exact ⟨hne, Or.inl ⟨u, hu, sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))⟩⟩

private lemma cayley_adj_iff (a b : MonoidAlgebra (ZMod 2) G) :
    (unitaryCayley (MonoidAlgebra (ZMod 2) G) (basisSubgroup G)).Adj a b ↔
      (cube G).Adj (coeffEquiv G a) (coeffEquiv G b) := by
  rw [unitary_cayley_as_add_cayley, SimpleGraph.addCayley_adj']
  constructor
  · rintro ⟨hne, v, ⟨u, ⟨g, rfl⟩, rfl⟩, h | h⟩
    · exact ((difference_iff G b a).mp ⟨g,
        sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm _ _))⟩).symm
    · exact (difference_iff G a b).mp ⟨g,
        sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))⟩
  · intro h
    obtain ⟨g, hg⟩ := (difference_iff G a b).mpr h
    refine ⟨?_, _, ⟨(MonoidAlgebra.of (ZMod 2) G).toHomUnits g, ⟨g, rfl⟩, rfl⟩,
      Or.inr ((sub_eq_iff_eq_add.mp hg).trans (add_comm _ _))⟩
    intro heq
    subst b
    exact (cube G).loopless.irrefl _ h

private noncomputable def cayleyIso :
    unitaryCayley (MonoidAlgebra (ZMod 2) G) (basisSubgroup G) ≃g cube G where
  toEquiv := coeffEquiv G
  map_rel_iff' := by intro a b; exact (cayley_adj_iff G a b).symm

end D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum

namespace D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum
open Classical
open SimpleGraph D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum
variable {ι : Type*} [DecidableEq ι] [Fintype ι]


private def character (s : Finset ι) (x : ι → (ZMod 2)) : ℂ := ∏ i ∈ s, D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.complexSign (x i)

private lemma sign_step (a : (ZMod 2)) : D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.complexSign (a + 1) = -D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.complexSign a := by
  rw [D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.complexSign_add,
    D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_one]
  ring

omit [Fintype ι] in
private lemma character_flip (s : Finset ι) (x : ι → (ZMod 2)) (i : ι) :
    character s ((fun (x : ι → ZMod 2) (i : ι) => Function.update x i (x i + 1)) x i) = if i ∈ s then -character s x else character s x := by
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi]
    have hrest : (∏ j ∈ s.erase i, D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.complexSign ((fun (x : ι → ZMod 2) (i : ι) => Function.update x i (x i + 1)) x i j)) =
        ∏ j ∈ s.erase i, D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.complexSign (x j) := by
      change (∏ j ∈ s.erase i, (D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.complexSign ∘ Function.update x i (x i + 1)) j) = _
      rw [Function.comp_update]
      exact Finset.prod_update_of_notMem (by simp) _ _
    unfold character
    rw [← Finset.mul_prod_erase s (fun j => D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.complexSign ((fun (x : ι → ZMod 2) (i : ι) => Function.update x i (x i + 1)) x i j)) hi,
      ← Finset.mul_prod_erase s (fun j => D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.complexSign (x j)) hi, hrest]
    simp [sign_step]
  · rw [ite_eq_right hi]
    change (∏ j ∈ s, (D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.complexSign ∘ Function.update x i (x i + 1)) j) = _
    rw [Function.comp_update]
    exact Finset.prod_update_of_notMem hi _ _

omit [Fintype ι] in
private lemma flip_injective (x : ι → (ZMod 2)) : Function.Injective ((fun (x : ι → ZMod 2) (i : ι) => Function.update x i (x i + 1)) x) := by
  intro i j h
  rcases Function.update_eq_update_iff.mp h with he | he
  · exact he.1
  · exact False.elim ((by simp : x i + 1 ≠ x i) he.1)

private lemma cube_neighbors (x : ι → (ZMod 2)) :
    (cube ι).neighborFinset x = Finset.univ.image ((fun (x : ι → ZMod 2) (i : ι) => Function.update x i (x i + 1)) x) := by
  classical
  ext y
  simp [SimpleGraph.mem_neighborFinset, adj_iff_flip, eq_comm]

private lemma character_mulVec (s : Finset ι) (x : ι → (ZMod 2)) :
    ((cube ι).adjMatrix ℂ).mulVec (character s) x =
      ((Fintype.card ι : ℂ) - 2 * (s.card : ℂ)) * character s x := by
  classical
  rw [SimpleGraph.adjMatrix_mulVec_apply, cube_neighbors,
    Finset.sum_image (by intro i hi j hj h; exact flip_injective x h)]
  simp_rw [character_flip]
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff, Finset.univ_inter, Finset.sum_const,
    Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, nsmul_eq_mul]
  have hc : s.card ≤ Fintype.card ι := Finset.card_le_univ s
  push_cast [hc]
  ring

private lemma cube_zero_eigenvalue (heven : Even (Fintype.card ι)) :
    Module.End.HasEigenvalue ((cube ι).adjMatrix ℂ).mulVecLin (0 : ℂ) := by
  classical
  apply (zeroEigenvalue_iff _).mp
  obtain ⟨m, hm⟩ := heven
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset ι)) (n := m) (by simp; omega)
  refine ⟨character s, ?_, ?_⟩
  · intro h
    have := congrFun h (fun _ => 0)
    simp [character, D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient.complexSign] at this
  · funext x
    rw [character_mulVec]
    have he : (Fintype.card ι : ℂ) - 2 * (s.card : ℂ) = 0 := by
      rw [hcard, hm]
      push_cast
      ring
    simp [he]

private lemma zero_eigenvalue_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (hz : Module.End.HasEigenvalue (H.adjMatrix ℂ).mulVecLin (0 : ℂ)) : Module.End.HasEigenvalue (G.adjMatrix ℂ).mulVecLin (0 : ℂ) := by
  classical
  apply (zeroEigenvalue_iff _).mp
  obtain ⟨v, hv, hzero⟩ := (zeroEigenvalue_iff _).mpr hz
  refine ⟨fun a => v (e a), ?_, ?_⟩
  · intro h
    apply hv
    funext y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact congrFun h x
  · funext a
    have hz := congrFun hzero (e a)
    change ∑ b, G.adjMatrix ℂ a b * v (e b) = 0
    change ∑ b, H.adjMatrix ℂ (e a) b * v b = 0 at hz
    rw [← hz]
    apply Fintype.sum_equiv e.toEquiv
    intro b
    change (if G.Adj a b then (1 : ℂ) else 0) * v (e b) =
      (if H.Adj (e a) (e b) then (1 : ℂ) else 0) * v (e b)
    rw [e.map_adj_iff]

end D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum

namespace D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum
open SimpleGraph D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum

private lemma prime_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (hp : IsPrimeGraph H) : IsPrimeGraph G := by
  classical
  intro X hX
  let Y := X.map e.toEquiv.toEmbedding
  have hY : IsHomogeneousSet H (Y : Set W) := by
    intro w hw
    have hout : e.symm w ∉ X := by
      intro hx
      apply hw
      exact Finset.mem_map.mpr ⟨e.symm w, hx, e.apply_symm_apply w⟩
    rcases hX (e.symm w) hout with hall | hnone
    · left
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      change H.Adj w (e x)
      simpa only [e.apply_symm_apply] using e.map_adj_iff.mpr (hall x hx)
    · right
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      intro hadj
      change H.Adj w (e x) at hadj
      apply hnone x hx
      apply e.map_adj_iff.mp
      simpa only [e.apply_symm_apply] using hadj
  rcases hp Y hY with hs | hf
  · left; simpa [Y] using hs
  · right
    have hc := Fintype.card_congr e.toEquiv
    simpa [Y, ← hc] using hf

private lemma group_algebra_counterexample (G : Type) [CommGroup G] [Fintype G] [DecidableEq G]
    (hc : 3 ≤ Fintype.card G) (he : Even (Fintype.card G)) :
    IsFrobenius (MonoidAlgebra (ZMod 2) G) ∧ (-1 : (MonoidAlgebra (ZMod 2) G)ˣ) ∈ basisSubgroup G ∧
    (unitaryCayley (MonoidAlgebra (ZMod 2) G) (basisSubgroup G)).Connected ∧
    (unitaryCayley (MonoidAlgebra (ZMod 2) G) (basisSubgroup G))ᶜ.Connected ∧
    IsPrimeGraph (unitaryCayley (MonoidAlgebra (ZMod 2) G) (basisSubgroup G)) ∧
    Module.End.HasEigenvalue ((unitaryCayley (MonoidAlgebra (ZMod 2) G) (basisSubgroup G)).adjMatrix ℂ).mulVecLin (0 : ℂ) := by
  let e := cayleyIso G
  refine ⟨ring_frobenius G, minus_one_mem G, e.connected_iff.mpr cube_connected,
    ?_, prime_of_iso e (cube_prime hc), zero_eigenvalue_of_iso e (cube_zero_eigenvalue he)⟩
  let ec : (unitaryCayley (MonoidAlgebra (ZMod 2) G) (basisSubgroup G))ᶜ ≃g (cube G)ᶜ :=
    { toEquiv := e.toEquiv
      map_rel_iff' := by
        intro a b
        change (e a ≠ e b ∧ ¬ (cube G).Adj (e a) (e b)) ↔
          (a ≠ b ∧ ¬ (unitaryCayley (MonoidAlgebra (ZMod 2) G) (basisSubgroup G)).Adj a b)
        simp only [e.injective.ne_iff, e.map_adj_iff] }
  exact ec.connected_iff.mpr (cube_complement_connected hc)

private lemma even_cyclic_family (d : ℕ) [NeZero d] (hd : 4 ≤ d) (he : Even d) :
    IsFrobenius (MonoidAlgebra (ZMod 2) (Multiplicative (ZMod d))) ∧
    (-1 : (MonoidAlgebra (ZMod 2) (Multiplicative (ZMod d)))ˣ) ∈ basisSubgroup (Multiplicative (ZMod d)) ∧
    (unitaryCayley (MonoidAlgebra (ZMod 2) (Multiplicative (ZMod d)))
      (basisSubgroup (Multiplicative (ZMod d)))).Connected ∧
    (unitaryCayley (MonoidAlgebra (ZMod 2) (Multiplicative (ZMod d)))
      (basisSubgroup (Multiplicative (ZMod d))))ᶜ.Connected ∧
    IsPrimeGraph (unitaryCayley (MonoidAlgebra (ZMod 2) (Multiplicative (ZMod d)))
      (basisSubgroup (Multiplicative (ZMod d)))) ∧
    Module.End.HasEigenvalue ((unitaryCayley (MonoidAlgebra (ZMod 2) (Multiplicative (ZMod d)))
      (basisSubgroup (Multiplicative (ZMod d)))).adjMatrix ℂ).mulVecLin (0 : ℂ) := by
  apply group_algebra_counterexample
  · simpa using (show 3 ≤ d by omega)
  · simpa using he

end D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum

namespace D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum

theorem result : ¬ claim := by
  intro h
  obtain ⟨hf, hm, hc, hac, hp, hz⟩ := even_cyclic_family 4 (by decide) (by decide)
  exact (h _ hf _ hm hc hac).mp hp ((zeroEigenvalue_iff _).mpr hz)

end D5.S3.ArithUnits.NguyenTanUnitaryCayleyPrimeSpectrum
