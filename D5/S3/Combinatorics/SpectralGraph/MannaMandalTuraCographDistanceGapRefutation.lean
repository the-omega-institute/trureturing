/- GID: D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.claim; result=D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.result; claim=D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.claim
   digest: Connected cographs have distance eigenvalues arbitrarily close to −2 from below. -/

/-
admission_basis: open-problem-resolution, Manna–Mandal–Tura Open Problem 14.2(i), #32278.
Direct frozen dependencies: none. The proof imports pinned Mathlib.
registered_family_counters_gap — proof_shape: content. Its live strict quotient root, for
every positive natural q with r = q, follows from the exact determinant sign change.
result — proof_shape: content. The same root is used through registered_family_counters_gap
to produce a nonzero eigenvector of the native distance matrix inside the forbidden interval.
-/

import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! A family of counterexamples to Manna–Mandal–Tura, Open Problem 14.2(i). -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.SpectralGraph.MannaMandalTuraCographDistanceGapRefutation

open Matrix BigOperators

/-- Orbit order: universal vertex, isolated vertex before the join, edge endpoints. -/
private def quotient (r : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 2 * (r : ℝ); 1, 0, 4 * (r : ℝ); 1, 2, 4 * (r : ℝ) - 3]

private def shiftedPoly (r : ℕ) (t : ℝ) : ℝ :=
  (t + 1) * (t - 1) * (t - 3) + (6 - 4 * t) * (r : ℝ) * t

private theorem quotient_det (r : ℕ) (lam : ℝ) :
    ((lam • (1 : Matrix (Fin 3) (Fin 3) ℝ)) - quotient r).det =
      shiftedPoly r (lam + 2) := by
  rw [Matrix.det_fin_three]
  simp [Matrix.sub_apply, quotient, shiftedPoly]
  ring

private theorem shiftedPoly_at_zero (r : ℕ) : shiftedPoly r 0 = 3 := by
  norm_num [shiftedPoly]

private theorem shiftedPoly_neg_reciprocal (q : ℕ) (hq : 0 < q) :
    shiftedPoly q (-(1 / (q : ℝ))) < 0 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let z : ℝ := 1 / (q : ℝ)
  have hz : (q : ℝ) * z = 1 := by simp [z, hqR.ne']
  have hzPos : 0 < z := one_div_pos.mpr hqR
  change shiftedPoly q (-z) < 0
  have heq : shiftedPoly q (-z) = -((1 + z)^3 + 2) := by
    calc
      shiftedPoly q (-z) =
          (-z + 1) * (-z - 1) * (-z - 3) - (6 + 4 * z) * ((q : ℝ) * z) := by
        unfold shiftedPoly
        ring
      _ = _ := by rw [hz]; ring
  rw [heq]
  have hpos : 0 < (1 + z)^3 + 2 := by positivity
  linarith

private theorem strict_quotient_root (q : ℕ) (hq : 0 < q) :
    ∃ lam : ℝ, -2 - 1 / (q : ℝ) < lam ∧ lam < -2 ∧
      ((lam • (1 : Matrix (Fin 3) (Fin 3) ℝ)) - quotient q).det = 0 := by
  let a : ℝ := -(1 / (q : ℝ))
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ha : a < 0 := neg_neg_of_pos (one_div_pos.mpr hqR)
  have hleft : shiftedPoly q a < 0 := shiftedPoly_neg_reciprocal q hq
  have hright : 0 < shiftedPoly q 0 := by rw [shiftedPoly_at_zero]; norm_num
  have hcont : Continuous (shiftedPoly q) := by unfold shiftedPoly; fun_prop
  obtain ⟨t, ht, hroot⟩ :=
    intermediate_value_Icc ha.le hcont.continuousOn ⟨hleft.le, hright.le⟩
  have hat : a < t := lt_of_le_of_ne ht.1 (by
    intro he
    rw [he] at hleft
    exact hleft.ne hroot)
  have ht0 : t < 0 := lt_of_le_of_ne ht.2 (by
    intro he
    rw [he] at hroot
    exact hright.ne' hroot)
  refine ⟨t - 2, ?_, by linarith, ?_⟩
  · dsimp [a] at hat
    linarith
  · rw [quotient_det, sub_add_cancel, hroot]

private theorem arbitrarily_close_quotient_root (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧ ∃ lam : ℝ, -2 - ε < lam ∧ lam < -2 ∧
      ((lam • (1 : Matrix (Fin 3) (Fin 3) ℝ)) - quotient r).det = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have hq : 0 < n + 1 := Nat.succ_pos n
  obtain ⟨lam, hlo, hhi, hdet⟩ := strict_quotient_root (n + 1) hq
  push_cast at hlo
  exact ⟨n + 1, hq, lam, by linarith, hhi, hdet⟩

/-- False on the left is the universal vertex, true is the originally isolated vertex.
On the right, the first coordinate selects an edge and the second its endpoint. -/
abbrev Vertex (r : ℕ) := Bool ⊕ (Fin r × Bool)

private def center {r : ℕ} : Vertex r := .inl false

private def familyAdj {r : ℕ} : Vertex r → Vertex r → Prop
  | .inl a, .inl b => a ≠ b
  | .inl a, .inr _ => a = false
  | .inr _, .inl b => b = false
  | .inr (i, a), .inr (j, b) => i = j ∧ a ≠ b

/-- The join of the universal vertex with a singleton and r disjoint edges. -/
def family (r : ℕ) : SimpleGraph (Vertex r) where
  Adj := familyAdj
  symm := ⟨by
    rintro (a | ⟨i, a⟩) (b | ⟨j, b⟩)
    · exact Ne.symm
    · exact id
    · exact id
    · exact fun h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by
    rintro (a | ⟨i, a⟩) <;> simp [familyAdj]⟩

@[local simp] private theorem family_adj (r : ℕ) (a b : Vertex r) :
    (family r).Adj a b ↔ familyAdj a b := Iff.rfl

private theorem center_adj {r : ℕ} {v : Vertex r} (h : v ≠ center) :
    (family r).Adj center v := by
  rcases v with (_ | _) | ⟨i, b⟩ <;> simp_all [center, family, familyAdj]

private theorem family_connected (r : ℕ) : (family r).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable (G := family r)).mpr
  refine ⟨center, fun v => ?_⟩
  by_cases h : v = center
  · subst v
    exact SimpleGraph.Reachable.rfl
  · exact (center_adj h).reachable

/-- P₄-freeness uses induced graph embeddings of Mathlib's four-vertex path. -/
def P4Free {V : Type} (G : SimpleGraph V) : Prop :=
  IsEmpty (SimpleGraph.pathGraph 4 ↪g G)

private theorem outside_center_neighbor {r : ℕ} {a b : Vertex r}
    (ha : a ≠ center) (hb : b ≠ center) (hab : (family r).Adj a b) :
    ∃ (i : Fin r) (s : Bool), a = .inr (i, s) ∧ b = .inr (i, !s) := by
  rcases a with (_ | _) | ⟨i, s⟩ <;> rcases b with (_ | _) | ⟨j, t⟩ <;>
    simp_all [center, family, familyAdj]
  obtain ⟨rfl, hst⟩ := hab
  cases s <;> cases t <;> simp_all

private theorem family_p4_free (r : ℕ) : P4Free (family r) := by
  constructor
  intro e
  have houtside (i : Fin 4) : e i ≠ center := by
    let j : Fin 4 := ![2, 3, 0, 1] i
    have hj : i ≠ j ∧ ¬ (SimpleGraph.pathGraph 4).Adj i j := by
      fin_cases i <;> norm_num [j, SimpleGraph.pathGraph_adj]
    intro he
    have hne : e j ≠ center := by
      intro he'
      exact hj.1 (e.injective (he.trans he'.symm))
    have hadj : (family r).Adj (e i) (e j) := he ▸ center_adj hne
    exact hj.2 (e.map_rel_iff.mp hadj)
  have h10 : (family r).Adj (e 1) (e 0) :=
    e.map_rel_iff.mpr (by norm_num [SimpleGraph.pathGraph_adj])
  have h12 : (family r).Adj (e 1) (e 2) :=
    e.map_rel_iff.mpr (by norm_num [SimpleGraph.pathGraph_adj])
  obtain ⟨i, s, h1, h0⟩ := outside_center_neighbor (houtside 1) (houtside 0) h10
  obtain ⟨j, t, h1', h2⟩ := outside_center_neighbor (houtside 1) (houtside 2) h12
  have heq : (i, s) = (j, t) := Sum.inr.inj (h1.symm.trans h1')
  cases heq
  exact (by decide : (0 : Fin 4) ≠ 2) (e.injective (h0.trans h2.symm))

open scoped Classical in
private theorem family_dist (r : ℕ) (a b : Vertex r) :
    (family r).dist a b = if a = b then 0 else if (family r).Adj a b then 1 else 2 := by
  classical
  split_ifs with he hadj
  · subst b
    simp
  · exact SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  · have ha : a ≠ center := by
      intro hac
      exact hadj (hac ▸ center_adj (fun hbc => he (hac.trans hbc.symm)))
    have hb : b ≠ center := by
      intro hbc
      exact hadj (hbc ▸ (center_adj ha).symm)
    have hd : (family r).edist a b = 2 :=
      SimpleGraph.edist_eq_two_iff.mpr
        ⟨he, hadj, center, ((family r).mem_commonNeighbors (u := center) (v := a) (w := b)).mpr
          ⟨(center_adj ha).symm, (center_adj hb).symm⟩⟩
    change ((family r).edist a b).toNat = 2
    rw [hd]
    rfl

noncomputable def distanceMatrix {V : Type} (G : SimpleGraph V) : Matrix V V ℝ :=
  fun v w => (G.dist v w : ℝ)

private def orbit {r : ℕ} : Vertex r → Fin 3
  | .inl false => 0
  | .inl true => 1
  | .inr _ => 2

private def orbitLift {r : ℕ} (x : Fin 3 → ℝ) : Vertex r → ℝ :=
  fun v => x (orbit v)

private theorem orbit_lift_injective {r : ℕ} (hr : 0 < r) :
    Function.Injective (orbitLift (r := r)) := by
  intro x y h
  funext k
  fin_cases k
  · exact congrFun h (.inl false)
  · exact congrFun h (.inl true)
  · exact congrFun h (.inr (⟨0, hr⟩, false))

private theorem endpoint_sum (r : ℕ) (i : Fin r) (s : Bool) (z : ℝ) :
    (∑ j : Fin r, ∑ b : Bool, ((family r).dist (.inr (i, s)) (.inr (j, b)) : ℝ) * z)
      = (4 * (r : ℝ) - 3) * z := by
  classical
  calc
    _ = ∑ j : Fin r, (4 * z + if j = i then -(3 * z) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : j = i
      · subst j
        cases s <;> simp [family_dist, familyAdj] <;> ring
      · simp [family_dist, familyAdj, hij, Ne.symm hij]
        ring
    _ = _ := by
      simp [Finset.sum_add_distrib]
      ring

private theorem distance_mulVec_orbitLift (r : ℕ) (x : Fin 3 → ℝ) :
    distanceMatrix (family r) *ᵥ orbitLift x = orbitLift (quotient r *ᵥ x) := by
  classical
  funext v
  rcases v with (_ | _) | ⟨i, s⟩
  · simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fintype.sum_bool, Fin.sum_univ_three, distanceMatrix, orbitLift, orbit]
    simp [family_dist, familyAdj, quotient]
    ring
  · simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fintype.sum_bool, Fin.sum_univ_three, distanceMatrix, orbitLift, orbit]
    simp [family_dist, familyAdj, quotient]
    ring
  · change (distanceMatrix (family r) *ᵥ orbitLift x) (.inr (i, s)) =
        (quotient r *ᵥ x) 2
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type,
      orbitLift, orbit, distanceMatrix]
    rw [endpoint_sum]
    simp [Fin.sum_univ_three, family_dist, familyAdj, quotient]
    ring

private theorem lift_quotient_eigenvalue {r : ℕ} (hr : 0 < r) {lam : ℝ}
    (hdet : ((lam • (1 : Matrix (Fin 3) (Fin 3) ℝ)) - quotient r).det = 0) :
    Module.End.HasEigenvalue (distanceMatrix (family r)).mulVecLin lam := by
  obtain ⟨x, hx, heig⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at heig
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := orbitLift x)
  refine Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · rw [Matrix.mulVecLin_apply, distance_mulVec_orbitLift, ← heig]
    rfl
  · intro h
    exact hx (orbit_lift_injective hr h)

/-- The joined matching family has a distance eigenvalue in every open left neighborhood of −2. -/
theorem registered_family_counters_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℕ), 0 < r ∧ ∃ lam : ℝ, -2 - ε < lam ∧ lam < -2 ∧
      (family r).Connected ∧ P4Free (family r) ∧
      Module.End.HasEigenvalue (distanceMatrix (family r)).mulVecLin lam := by
  obtain ⟨r, hr, lam, hlo, hhi, hdet⟩ := arbitrarily_close_quotient_root ε hε
  exact ⟨r, hr, lam, hlo, hhi, family_connected r, family_p4_free r, lift_quotient_eigenvalue hr hdet⟩

/-- The published uniform-gap assertion of Open Problem 14.2(i). -/
def claim : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → P4Free G →
      ∀ lam : ℝ, Module.End.HasEigenvalue (distanceMatrix G).mulVecLin lam → ¬ (-2 - ε < lam ∧ lam < -2)

/-- There is no uniform open left gap at −2 for distance eigenvalues of connected cographs. -/
theorem result : ¬ claim := by
  rintro ⟨ε, hε, hgap⟩
  obtain ⟨r, _, lam, hlo, hhi, hc, hp, he⟩ := registered_family_counters_gap ε hε
  exact hgap (Vertex r) (family r) hc hp lam he ⟨hlo, hhi⟩

end D5.S3.Combinatorics.SpectralGraph.MannaMandalTuraCographDistanceGapRefutation
