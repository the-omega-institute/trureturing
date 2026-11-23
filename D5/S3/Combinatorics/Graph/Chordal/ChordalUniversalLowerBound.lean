/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.subtwo_universal_chordal_claim; result=D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.not_subtwo_universal_chordal; claim=D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.subtwo_universal_chordal_claim
   digest: Path powers admit coefficient two, and the integral cycle lattice forces two in width three. -/

import D5.S3.Combinatorics.Graph.Chordal.Characterization
import D5.S3.Combinatorics.Graph.Chordal.UniformGainPotential
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBoundCertificate

/-! Block-head tree potentials and the triangle-filling obstruction on a path power. -/

namespace SimpleGraph

/-- Join distinct indices at distance at most the width. -/
def pathPower (n k : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ Int.natAbs ((i : ℤ) - (j : ℤ)) ≤ k
  symm := ⟨by
    intro i j h
    refine ⟨h.1.symm, ?_⟩
    rw [show (j : ℤ) - (i : ℤ) = -((i : ℤ) - (j : ℤ)) by ring, Int.natAbs_neg]
    exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

namespace PathPower

private theorem within_iff {n k : ℕ} {i j : Fin n} :
    Int.natAbs ((i : ℤ) - (j : ℤ)) ≤ k ↔ i.val ≤ j.val + k ∧ j.val ≤ i.val + k := by
  omega

private theorem adj_iff {n k : ℕ} {i j : Fin n} :
    (pathPower n k).Adj i j ↔ i ≠ j ∧ i.val ≤ j.val + k ∧ j.val ≤ i.val + k := by
  change i ≠ j ∧ _ ↔ _
  rw [within_iff]

private theorem eq_or_adj_of_between {n k : ℕ} {i j : Fin n}
    (hij : i.val ≤ j.val) (hji : j.val ≤ i.val + k) :
    i = j ∨ (pathPower n k).Adj i j := by
  by_cases he : i = j
  · exact Or.inl he
  · exact Or.inr (adj_iff.mpr ⟨he, by omega, hji⟩)

/-- Increasing vertex order is an elimination order: all later neighbours lie in one
interval of width at most the edge span. -/
theorem pathPower_isChordal (n k : ℕ) : (pathPower n k).IsChordal := by
  apply IsPEO.isChordal (ord := Fin.val)
  refine ⟨Fin.val_injective, ?_⟩
  intro i j hj l hl hjl
  change i.val < j.val ∧ (pathPower n k).Adj i j at hj
  change i.val < l.val ∧ (pathPower n k).Adj i l at hl
  have h₁ := adj_iff.mp hj.2
  have h₂ := adj_iff.mp hl.2
  exact adj_iff.mpr ⟨hjl, by omega, by omega⟩

section Gains

variable {n k : ℕ} {H : Type*} [Group H] [PseudoMetricSpace H]
  [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]

private def blockHead (k : ℕ) (i : Fin n) : Fin n :=
  ⟨k * (i.val / k), (Nat.mul_div_le i.val k).trans_lt i.isLt⟩

private def diagonalOne (g : Fin n → Fin n → H) (i j : Fin n) : H :=
  if i = j then 1 else g i j

omit [PseudoMetricSpace H] [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H] in
private theorem diagonalOne_adj {g : Fin n → Fin n → H} {i j : Fin n}
    (h : (pathPower n k).Adj i j) : diagonalOne g i j = g i j :=
  ite_eq_right h.ne

omit [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H] in
private theorem triangle_with_diagonal {g : Fin n → Fin n → H} {ε : ℝ} (hε : 0 ≤ ε)
    (hrev : ∀ i j, (pathPower n k).Adj i j → g j i = (g i j)⁻¹)
    (htri : ∀ i j l, (pathPower n k).Adj i j → (pathPower n k).Adj j l →
      (pathPower n k).Adj i l → Dist.dist (g i j * g j l) (g i l) ≤ ε)
    {a b c : Fin n}
    (hab : a = b ∨ (pathPower n k).Adj a b) (hbc : b = c ∨ (pathPower n k).Adj b c)
    (hac : a = c ∨ (pathPower n k).Adj a c) :
    Dist.dist (diagonalOne g a b * diagonalOne g b c) (diagonalOne g a c) ≤ ε := by
  rcases hab with rfl | hab
  · simpa [diagonalOne] using hε
  rcases hbc with rfl | hbc
  · simpa [diagonalOne] using hε
  rcases hac with rfl | hac
  · simpa [diagonalOne, hab.ne, hab.ne.symm, hrev _ _ hab] using hε
  simpa only [diagonalOne_adj hab, diagonalOne_adj hbc, diagonalOne_adj hac] using
    htri _ _ _ hab hbc hac

private def headGain (n k : ℕ) (g : Fin n → Fin n → H) (a b : ℕ) : H :=
  if ha : k * a < n then
    if hb : k * b < n then g ⟨k * a, ha⟩ ⟨k * b, hb⟩ else 1
  else 1

private def headPotential (n k : ℕ) (g : Fin n → Fin n → H) : ℕ → H
  | 0 => 1
  | m + 1 => headPotential n k g m * headGain n k g m (m + 1)

/-- Integrate gains along consecutive block heads and from each head to its block.
The chord from the earlier endpoint to the later head splits a cross-block edge
comparison into two triangle comparisons. -/
theorem pathPower_exists_two_approximate_gain_potential
    (n k : ℕ) (hk : 1 ≤ k) (g : Fin n → Fin n → H) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, (pathPower n k).Adj i j → g j i = (g i j)⁻¹)
    (htri : ∀ i j l, (pathPower n k).Adj i j → (pathPower n k).Adj j l →
      (pathPower n k).Adj i l → Dist.dist (g i j * g j l) (g i l) ≤ ε) :
    ∃ φ : Fin n → H, ∀ i j, (pathPower n k).Adj i j →
      Dist.dist (g i j) ((φ i)⁻¹ * φ j) ≤ 2 * ε := by
  let γ := diagonalOne g
  let Q := headPotential n k γ
  let φ := fun i : Fin n => Q (i.val / k) * γ (blockHead k i) i
  have tri := @triangle_with_diagonal n k H _ _ g ε hε hrev htri
  have hpos : 0 < k := by omega
  have hhead (i : Fin n) : (blockHead k i) = i ∨ (pathPower n k).Adj (blockHead k i) i := by
    apply eq_or_adj_of_between
    · exact Nat.mul_div_le i.val k
    · have hrem := Nat.mod_lt i.val hpos
      have hdiv := Nat.mod_add_div i.val k
      change i.val ≤ k * (i.val / k) + k
      omega
  have forward {i j : Fin n} (hij : (pathPower n k).Adj i j) (h : i.val ≤ j.val) :
      Dist.dist (g i j) ((φ i)⁻¹ * φ j) ≤ 2 * ε := by
    let b := blockHead k i
    let c := blockHead k j
    have hab := (adj_iff.mp hij).2.2
    have hmono : i.val / k ≤ j.val / k := Nat.div_le_div_right h
    have hnext : j.val / k ≤ i.val / k + 1 := by
      simpa only [Nat.add_div_right _ hpos] using (Nat.div_le_div_right (c := k) hab)
    rw [← dist_mul_left (φ i), ← mul_assoc, mul_inv_cancel, one_mul, ← diagonalOne_adj (g := g) hij]
    change Dist.dist ((Q (i.val / k) * γ b i) * γ i j) (Q (j.val / k) * γ c j) ≤ 2 * ε
    by_cases hs : i.val / k = j.val / k
    · have hbc : b = c := Fin.ext (congrArg (k * ·) hs)
      rw [hs, hbc, mul_assoc, dist_mul_left]
      have hci : c = i ∨ (pathPower n k).Adj c i := hbc ▸ hhead i
      exact (tri hci (Or.inr hij) (hhead j)).trans (by linarith)
    · have hsucc : j.val / k = i.val / k + 1 := by omega
      have hc : c.val = b.val + k := by
        change k * (j.val / k) = k * (i.val / k) + k
        rw [hsucc, Nat.mul_succ]
      have hbc : b = c ∨ (pathPower n k).Adj b c :=
        eq_or_adj_of_between (by omega) (by omega)
      have hic : i = c ∨ (pathPower n k).Adj i c := by
        apply eq_or_adj_of_between
        · have hrem := Nat.mod_lt i.val hpos
          have hdiv := Nat.mod_add_div i.val k
          have hb : b.val = k * (i.val / k) := rfl
          omega
        · have hb : b.val ≤ i.val := Nat.mul_div_le i.val k
          omega
      have hQ : Q (j.val / k) = Q (i.val / k) * γ b c := by
        unfold Q
        conv_lhs => rw [hsucc]
        rw [headPotential]
        congr 1
        have hb : k * (i.val / k) < n := b.isLt
        have hc' : k * (i.val / k + 1) < n := hsucc ▸ c.isLt
        simp only [headGain, dite_eq_left hb, dite_eq_left hc']
        congr 1
        exact Fin.ext (congrArg (k * ·) hsucc.symm)
      rw [hQ, mul_assoc (Q (i.val / k)), mul_assoc (Q (i.val / k)), dist_mul_left]
      have h₁ : Dist.dist (γ b i * γ i j) (γ b i * (γ i c * γ c j)) ≤ ε := by
        rw [dist_mul_left, _root_.dist_comm]
        exact tri hic (hhead j) (Or.inr hij)
      have h₂ : Dist.dist (γ b i * (γ i c * γ c j)) (γ b c * γ c j) ≤ ε := by
        rw [← mul_assoc, dist_mul_right]
        exact tri (hhead i) hic hbc
      linarith [dist_triangle (γ b i * γ i j) (γ b i * (γ i c * γ c j)) (γ b c * γ c j)]
  refine ⟨φ, fun i j hij => ?_⟩
  rcases le_total i.val j.val with h | h
  · exact forward hij h
  · rw [hrev j i hij.symm]
    simpa only [mul_inv_rev, inv_inv] using
      (dist_inv_inv (g j i) ((φ j)⁻¹ * φ i)).le.trans (forward hij.symm h)

end Gains

end PathPower

end SimpleGraph

namespace SimpleGraph.PathPower

open scoped BigOperators

open private edgeAt triangle treeEdge offTreeEdge incidence edgeBoundary boundary edgeWeight
  triangleWeight combinedWeight basisFilling cut edge_span edgeAt_complete edge_injective
  triangle_complete edge_partition boundary_closed cut_incidence basis_filling boundary_unit
  weight_sum weight_combination column_bound objective_value from
  D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBoundCertificate

noncomputable section

private def fill {R : Type*} [Ring R] (x : Fin 28 → R) : Fin 19 → R :=
  fun j => ∑ t, x t * (boundary t j : R)

private theorem fill_add {R : Type*} [Ring R] (x y : Fin 28 → R) :
    fill (x + y) = fill x + fill y := by
  funext j
  simp [fill, add_mul, Finset.sum_add_distrib]

private theorem fill_neg {R : Type*} [Ring R] (x : Fin 28 → R) :
    fill (-x) = -fill x := by
  funext j
  simp [fill]

private theorem fill_single {R : Type*} [Ring R] (t : Fin 28) :
    fill (Pi.single t (1 : R)) = fun j => (boundary t j : R) := by
  classical
  funext j
  simp [fill, Pi.single_apply, ite_mul]

private theorem fill_surjective {R : Type*} [CommRing R] :
    Function.Surjective (fill (R := R)) := by
  intro z
  refine ⟨fun t => ∑ j : Fin 19, z j * (basisFilling j t : R), ?_⟩
  funext l
  calc
    _ = ∑ t : Fin 28, ∑ j : Fin 19, z j * ((basisFilling j t : R) * (boundary t l : R)) := by
      simp only [fill, Finset.sum_mul, mul_assoc]
    _ = ∑ j : Fin 19, z j * (∑ t : Fin 28, (basisFilling j t : R) * (boundary t l : R)) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = z l := by
      have h (j : Fin 19) :
          (∑ t : Fin 28, (basisFilling j t : R) * (boundary t l : R)) =
            if j = l then 1 else 0 := by
        simp only [← Int.cast_mul, ← Int.cast_sum, basis_filling]
        split <;> simp
      simp [h, mul_ite]

/-- The vertex-edge incidence operator for the oriented width-three path on twelve vertices. -/
def incidenceMap (R : Type*) [CommRing R] : (Fin 30 → R) →ₗ[R] (Fin 12 → R) where
  toFun z v := ∑ e, (incidence v e : R) * z e
  map_add' x y := by
    funext v
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    funext v
    simp [Finset.mul_sum, mul_left_comm]

private def edgeFill {R : Type*} [CommRing R] (x : Fin 28 → R) : Fin 30 → R :=
  fun e => ∑ t, (edgeBoundary t e : R) * x t

private theorem edgeFill_closed {R : Type*} [CommRing R] (x : Fin 28 → R) :
    edgeFill x ∈ (incidenceMap R).ker := by
  change incidenceMap R (edgeFill x) = 0
  funext v
  change (∑ e : Fin 30, (incidence v e : R) *
    (∑ t : Fin 28, (edgeBoundary t e : R) * x t)) = 0
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul, ← Int.cast_mul, ← Int.cast_sum, boundary_closed]

private theorem offTree_injective {R : Type*} [CommRing R]
    (z : (incidenceMap R).ker) (hz : ∀ j, z.val (offTreeEdge j) = 0) : z = 0 := by
  apply Subtype.ext
  funext e
  rcases edge_partition e with ⟨d, rfl⟩ | ⟨j, rfl⟩
  · have hc (v : Fin 12) : (∑ e : Fin 30, (incidence v e : R) * z.val e) = 0 :=
      congrFun (LinearMap.mem_ker.mp z.property) v
    have h (f : Fin 30) : (∑ v : Fin 12, (cut d v : R) * (incidence v f : R)) * z.val f =
        if treeEdge d = f then z.val f else 0 := by
      rcases edge_partition f with ⟨a, rfl⟩ | ⟨j, rfl⟩
      · have hda : treeEdge d = treeEdge a ↔ d = a := by
          constructor
          · intro he
            by_contra hn
            have h₁ := cut_incidence d a
            have h₂ := cut_incidence d d
            rw [← he] at h₁
            simp [hn] at h₁
            simp [h₁] at h₂
          · rintro rfl
            rfl
        simp only [← Int.cast_mul, ← Int.cast_sum, cut_incidence, hda]
        split <;> simp
      · simp [hz j]
    have hsum : (∑ v : Fin 12, (cut d v : R) *
        (∑ f : Fin 30, (incidence v f : R) * z.val f)) = 0 := by simp [hc]
    simp only [Finset.mul_sum, ← mul_assoc] at hsum
    rw [Finset.sum_comm] at hsum
    simpa [← Finset.sum_mul, h] using hsum
  · exact hz j

/-- Projection off the spanning tree identifies circulations with nineteen free coordinates. -/
def cycleCoordinates (R : Type*) [CommRing R] : (incidenceMap R).ker ≃ₗ[R] (Fin 19 → R) :=
  LinearEquiv.ofBijective
    { toFun := fun z j => z.val (offTreeEdge j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨by
      intro x y h
      apply sub_eq_zero.mp
      exact offTree_injective (x - y) (fun j => sub_eq_zero.mpr (congrFun h j)),
    by
      intro z
      obtain ⟨x, hx⟩ := fill_surjective z
      refine ⟨⟨edgeFill x, edgeFill_closed x⟩, ?_⟩
      funext j
      simpa [edgeFill, fill, boundary, mul_comm] using congrFun hx j⟩

private def integralLength (x : Fin 28 → ℤ) : ℕ := ∑ t, (x t).natAbs

private theorem integral_fill_exists (z : Fin 19 → ℤ) :
    ∃ m, ∃ x, fill x = z ∧ integralLength x = m := by
  obtain ⟨x, rfl⟩ := fill_surjective z
  exact ⟨integralLength x, x, rfl, rfl⟩

/-- The least number of signed triangular faces in an integral filling. -/
def integralNorm (z : Fin 19 → ℤ) : ℕ := by
  classical
  exact Nat.find (integral_fill_exists z)

private theorem integralNorm_spec (z : Fin 19 → ℤ) :
    ∃ x, fill x = z ∧ integralLength x = integralNorm z := by
  classical
  exact Nat.find_spec (integral_fill_exists z)

private theorem integralNorm_le {x : Fin 28 → ℤ} {z : Fin 19 → ℤ} (h : fill x = z) :
    integralNorm z ≤ integralLength x := by
  classical
  exact Nat.find_min' (integral_fill_exists z) ⟨x, h, rfl⟩

private theorem integralNorm_zero : integralNorm 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa [integralLength] using integralNorm_le (x := 0) (z := 0) (by ext j; simp [fill])

private theorem integralNorm_neg (z : Fin 19 → ℤ) : integralNorm (-z) = integralNorm z := by
  have upper (w : Fin 19 → ℤ) : integralNorm (-w) ≤ integralNorm w := by
    obtain ⟨x, hx, hlen⟩ := integralNorm_spec w
    exact (integralNorm_le (x := -x) (by rw [fill_neg, hx])).trans
      (by simp [integralLength, ← hlen])
  exact le_antisymm (upper z) (by simpa only [neg_neg] using upper (-z))

private theorem integralNorm_add (z w : Fin 19 → ℤ) :
    integralNorm (z + w) ≤ integralNorm z + integralNorm w := by
  obtain ⟨x, hx, hlenx⟩ := integralNorm_spec z
  obtain ⟨y, hy, hleny⟩ := integralNorm_spec w
  refine (integralNorm_le (x := x + y) (by rw [fill_add, hx, hy])).trans ?_
  rw [← hlenx, ← hleny, integralLength, integralLength, integralLength, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun t _ => Int.natAbs_add_le (x t) (y t))

private theorem integralNorm_eq_zero {z : Fin 19 → ℤ} (h : integralNorm z = 0) : z = 0 := by
  obtain ⟨x, hx, hlen⟩ := integralNorm_spec z
  have hzero (t : Fin 28) : (x t).natAbs = 0 := by
    apply Nat.eq_zero_of_le_zero
    rw [← h, ← hlen]
    exact Finset.single_le_sum (f := fun t => (x t).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  rw [← hx]
  funext j
  simp [fill, fun t => Int.natAbs_eq_zero.mp (hzero t)]

/-- The multiplicative copy of the integral cycle lattice. -/
def IntegralCycles := Multiplicative (Fin 19 → ℤ)

instance : CommGroup IntegralCycles := inferInstanceAs (CommGroup (Multiplicative (Fin 19 → ℤ)))

/-- The triangle-filling metric on the integral lattice. -/
instance integralMetric : MetricSpace IntegralCycles where
  dist z w := integralNorm ((Multiplicative.toAdd z) - (Multiplicative.toAdd w))
  dist_self z := by simp [integralNorm_zero]
  dist_comm z w := by
    rw [← neg_sub, integralNorm_neg]
  dist_triangle z w u := by
    rw [← Nat.cast_add]
    exact_mod_cast (calc
      integralNorm (Multiplicative.toAdd z - Multiplicative.toAdd u) =
          integralNorm ((Multiplicative.toAdd z - Multiplicative.toAdd w) +
            (Multiplicative.toAdd w - Multiplicative.toAdd u)) := by rw [sub_add_sub_cancel]
      _ ≤ _ := integralNorm_add _ _)
  eq_of_dist_eq_zero := by
    intro z w h
    have hz : integralNorm (Multiplicative.toAdd z - Multiplicative.toAdd w) = 0 := by
      exact_mod_cast h
    have he := sub_eq_zero.mp (integralNorm_eq_zero hz)
    exact congrArg Multiplicative.ofAdd he

instance : IsIsometricSMul IntegralCycles IntegralCycles where
  isometry_smul a := Isometry.of_dist_eq fun x y => by
    change (integralNorm ((Multiplicative.toAdd a + Multiplicative.toAdd x) -
      (Multiplicative.toAdd a + Multiplicative.toAdd y)) : ℝ) = _
    rw [add_sub_add_left_eq_sub]
    rfl

instance : IsIsometricSMul IntegralCyclesᵐᵒᵖ IntegralCycles where
  isometry_smul a := Isometry.of_dist_eq fun x y => by
    change (integralNorm ((Multiplicative.toAdd x + Multiplicative.toAdd a.unop) -
      (Multiplicative.toAdd y + Multiplicative.toAdd a.unop)) : ℝ) = _
    rw [add_sub_add_right_eq_sub]
    rfl

private def realLength (x : Fin 28 → ℝ) : ℝ := ∑ t, |x t|

private def realLengths (z : Fin 19 → ℝ) : Set ℝ :=
  {v | ∃ x, fill x = z ∧ realLength x = v}

private theorem realLengths_nonempty (z : Fin 19 → ℝ) : (realLengths z).Nonempty := by
  obtain ⟨x, rfl⟩ := fill_surjective z
  exact ⟨realLength x, x, rfl, rfl⟩

private theorem realLength_nonneg (x : Fin 28 → ℝ) : 0 ≤ realLength x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem realLengths_bddBelow (z : Fin 19 → ℝ) : BddBelow (realLengths z) :=
  ⟨0, fun _ ⟨x, _, hx⟩ => hx ▸ realLength_nonneg x⟩

/-- The quotient norm of real triangle fillings. -/
def realNorm (z : Fin 19 → ℝ) : ℝ := sInf (realLengths z)

private theorem realNorm_le {x : Fin 28 → ℝ} {z : Fin 19 → ℝ} (h : fill x = z) :
    realNorm z ≤ realLength x :=
  csInf_le (realLengths_bddBelow z) ⟨x, h, rfl⟩

private theorem realNorm_nonneg (z : Fin 19 → ℝ) : 0 ≤ realNorm z :=
  le_csInf (realLengths_nonempty z) fun _ ⟨x, _, hx⟩ => hx ▸ realLength_nonneg x

private theorem realNorm_zero : realNorm 0 = 0 := by
  apply le_antisymm _ (realNorm_nonneg _)
  simpa [realLength] using realNorm_le (x := 0) (z := 0) (by ext j; simp [fill])

private theorem abs_boundary (t : Fin 28) (j : Fin 19) : |(boundary t j : ℝ)| ≤ 1 := by
  have h := boundary_unit t j
  have h' : (|(boundary t j)| : ℤ) ≤ 1 := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  exact_mod_cast h'

private theorem coord_le_realNorm (z : Fin 19 → ℝ) (j : Fin 19) : |z j| ≤ realNorm z := by
  apply le_csInf (realLengths_nonempty z)
  rintro _ ⟨x, rfl, rfl⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_boundary t j)

private theorem realNorm_eq_zero {z : Fin 19 → ℝ} (h : realNorm z = 0) : z = 0 := by
  funext j
  exact abs_nonpos_iff.mp (h ▸ coord_le_realNorm z j)

private theorem realNorm_smul_le (a : ℝ) (z : Fin 19 → ℝ) :
    realNorm (a • z) ≤ |a| * realNorm z := by
  by_cases ha : a = 0
  · simp [ha, realNorm_zero]
  rw [mul_comm |a|, ← div_le_iff₀ (abs_pos.mpr ha)]
  apply le_csInf (realLengths_nonempty z)
  rintro _ ⟨x, rfl, rfl⟩
  apply (div_le_iff₀ (abs_pos.mpr ha)).mpr
  have hfill : fill (a • x) = a • fill x := by
    funext j
    simp [fill, Finset.mul_sum, mul_assoc]
  have hlen : realLength (a • x) = realLength x * |a| := by
    simp [realLength, abs_mul, Finset.mul_sum, mul_comm]
  simpa only [hlen] using realNorm_le hfill

private theorem realNorm_smul (a : ℝ) (z : Fin 19 → ℝ) :
    realNorm (a • z) = |a| * realNorm z := by
  refine le_antisymm (realNorm_smul_le a z) ?_
  by_cases ha : a = 0
  · simp [ha, realNorm_zero]
  have h := realNorm_smul_le a⁻¹ (a • z)
  rw [smul_smul, inv_mul_cancel₀ ha, one_smul, abs_inv,
    ← div_eq_inv_mul, le_div_iff₀ (abs_pos.mpr ha), mul_comm] at h
  exact h

private theorem realNorm_add (z w : Fin 19 → ℝ) :
    realNorm (z + w) ≤ realNorm z + realNorm w := by
  by_contra! h
  let δ := (realNorm (z + w) - (realNorm z + realNorm w)) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨_, ⟨x, hx, rfl⟩, h₁⟩ :=
    exists_lt_of_csInf_lt (realLengths_nonempty z) (show realNorm z < realNorm z + δ by linarith)
  obtain ⟨_, ⟨y, hy, rfl⟩, h₂⟩ :=
    exists_lt_of_csInf_lt (realLengths_nonempty w) (show realNorm w < realNorm w + δ by linarith)
  have h₃ := realNorm_le (show fill (x + y) = z + w by rw [fill_add, hx, hy])
  have hadd : realLength (x + y) ≤ realLength x + realLength y := by
    simp only [realLength, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun t _ => abs_add_le (x t) (y t)
  dsimp [δ] at h₁ h₂
  linarith

/-- Real cycle coordinates with the triangle-filling norm. -/
def RealCycles := Fin 19 → ℝ

instance : AddCommGroup RealCycles := inferInstanceAs (AddCommGroup (Fin 19 → ℝ))
instance : Module ℝ RealCycles := inferInstanceAs (Module ℝ (Fin 19 → ℝ))
instance : FiniteDimensional ℝ RealCycles := inferInstanceAs (FiniteDimensional ℝ (Fin 19 → ℝ))
instance : Norm RealCycles := ⟨realNorm⟩

private theorem realCore : NormedSpace.Core ℝ RealCycles where
  norm_nonneg := realNorm_nonneg
  norm_triangle := realNorm_add
  norm_smul a z := by
    change realNorm (fun i => a * z i) = ‖a‖ * realNorm z
    rw [Real.norm_eq_abs]
    exact realNorm_smul a (show Fin 19 → ℝ from z)
  norm_eq_zero_iff z := by
    change realNorm z = 0 ↔ z = 0
    exact ⟨realNorm_eq_zero, fun h => h.symm ▸ realNorm_zero⟩

instance : NormedAddCommGroup RealCycles := .ofCore realCore
instance : NormedSpace ℝ RealCycles := .ofCore realCore
instance : CompleteSpace RealCycles := FiniteDimensional.complete ℝ RealCycles

open private gainCoordinate gain_reverse gain_diagonal triangle_gain boundary_reads_gain from
  D5.S3.Combinatorics.Graph.Chordal.ChordalUniversalLowerBoundCertificate

private def castCoordinates {m : ℕ} (z : Fin m → ℤ) : Fin m → ℝ := fun i => z i

private theorem cast_fill (x : Fin 28 → ℤ) : fill (castCoordinates x) = castCoordinates (fill x) := by
  funext j
  simp [fill, castCoordinates]

private theorem cast_length (x : Fin 28 → ℤ) :
    realLength (castCoordinates x) = (integralLength x : ℝ) := by
  simp only [realLength, integralLength, Nat.cast_sum, castCoordinates]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]

private theorem realNorm_le_integralNorm (z : Fin 19 → ℤ) :
    realNorm (castCoordinates z) ≤ (integralNorm z : ℝ) := by
  obtain ⟨x, hx, hlen⟩ := integralNorm_spec z
  have h := realNorm_le (x := castCoordinates x) (by rw [cast_fill, hx])
  rwa [cast_length, hlen] at h

private theorem integralLength_single (t : Fin 28) :
    integralLength (Pi.single t 1) = 1 := by
  classical
  simp [integralLength, Pi.single_apply, apply_ite Int.natAbs]

private theorem short_triangle_fill {a b c : Fin 12}
    (hab : a = b ∨ (pathPower 12 3).Adj a b) (hbc : b = c ∨ (pathPower 12 3).Adj b c)
    (hac : a = c ∨ (pathPower 12 3).Adj a c) :
    ∃ x : Fin 28 → ℤ, fill x = gainCoordinate a b + gainCoordinate b c - gainCoordinate a c ∧
      integralLength x ≤ 1 := by
  have hdiag (v : Fin 12) : gainCoordinate v v = 0 := funext (gain_diagonal v)
  have hzero : fill (0 : Fin 28 → ℤ) = 0 := by ext j; simp [fill]
  rcases hab with rfl | hab
  · exact ⟨0, by simp [hzero, hdiag], by simp [integralLength]⟩
  rcases hbc with rfl | hbc
  · exact ⟨0, by simp [hzero, hdiag], by simp [integralLength]⟩
  rcases hac with rfl | hac
  · refine ⟨0, ?_, by simp [integralLength]⟩
    rw [hzero, hdiag, sub_zero]
    funext j
    simp [gain_reverse a b, Pi.add_apply]
  obtain ⟨t, pos, ht⟩ := triangle_gain a b c hab.ne hbc.ne hac.ne hab.2 hbc.2 hac.2
  cases pos
  · refine ⟨-(Pi.single t 1), ?_, by simpa [integralLength] using (integralLength_single t).le⟩
    rw [fill_neg, fill_single]
    funext j
    simpa [eq_comm] using ht j
  · refine ⟨Pi.single t 1, ?_, (integralLength_single t).le⟩
    rw [fill_single]
    funext j
    simpa [eq_comm] using ht j

private theorem integral_triangle_bound {a b c : Fin 12}
    (hab : a = b ∨ (pathPower 12 3).Adj a b) (hbc : b = c ∨ (pathPower 12 3).Adj b c)
    (hac : a = c ∨ (pathPower 12 3).Adj a c) :
    integralNorm (gainCoordinate a b + gainCoordinate b c - gainCoordinate a c) ≤ 1 := by
  obtain ⟨x, hx, hl⟩ := short_triangle_fill hab hbc hac
  exact (integralNorm_le hx).trans hl

private def realGainCoords (a b : Fin 12) : Fin 19 → ℝ := castCoordinates (gainCoordinate a b)

/-- The canonical real gains in the spanning-tree gauge. -/
def realGain (a b : Fin 12) : RealCycles := realGainCoords a b

private def rootClone {n : ℕ} (i : Fin n) : Fin 12 := ⟨min i.val 11, by omega⟩

/-- Canonical integral gains, extended by cloning the last vertex. -/
def integralGain {n : ℕ} (a b : Fin n) : IntegralCycles :=
  Multiplicative.ofAdd (gainCoordinate (rootClone a) (rootClone b))

private theorem rootClone_edge {n : ℕ} {a b : Fin n} (h : (pathPower n 3).Adj a b) :
    rootClone a = rootClone b ∨ (pathPower 12 3).Adj (rootClone a) (rootClone b) := by
  have ha := (adj_iff.mp h).2.1
  have hb := (adj_iff.mp h).2.2
  by_cases he : rootClone a = rootClone b
  · exact Or.inl he
  · exact Or.inr (adj_iff.mpr ⟨he,
      by change min a.val 11 ≤ min b.val 11 + 3; omega,
      by change min b.val 11 ≤ min a.val 11 + 3; omega⟩)

private theorem integralGain_reverse {n : ℕ} (a b : Fin n) :
    integralGain b a = (integralGain a b)⁻¹ := by
  change gainCoordinate (rootClone b) (rootClone a) = -gainCoordinate (rootClone a) (rootClone b)
  exact funext (gain_reverse _ _)

private theorem integralGain_flat {n : ℕ} {a b c : Fin n}
    (hab : (pathPower n 3).Adj a b) (hbc : (pathPower n 3).Adj b c)
    (hac : (pathPower n 3).Adj a c) :
    Dist.dist (integralGain a b * integralGain b c) (integralGain a c) ≤ 1 := by
  change (integralNorm _ : ℝ) ≤ 1
  exact_mod_cast integral_triangle_bound (rootClone_edge hab) (rootClone_edge hbc) (rootClone_edge hac)

private def score (e : Fin 30) (z : Fin 19 → ℝ) : ℝ :=
  ∑ j, (combinedWeight e j : ℝ) * z j

private theorem score_fill (e : Fin 30) (x : Fin 28 → ℝ) :
    score e (fill x) = ∑ t : Fin 28, x t *
      (∑ j : Fin 19, (combinedWeight e j : ℝ) * (boundary t j : ℝ)) := by
  simp only [score, fill, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext t
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem score_fill_bound (e : Fin 30) (x : Fin 28 → ℝ) :
    score e (fill x) ≤ (edgeWeight e : ℝ) * realLength x := by
  rw [score_fill, realLength, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  let q : ℝ := ∑ j : Fin 19, (combinedWeight e j : ℝ) * (boundary t j : ℝ)
  have hb : |q| ≤ (edgeWeight e : ℝ) := by
    have hb' := column_bound e t
    have hc : |(∑ j : Fin 19, combinedWeight e j * boundary t j)| ≤ (edgeWeight e : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hb'
    dsimp [q]
    exact_mod_cast hc
  change x t * q ≤ _
  calc
    x t * q ≤ |x t * q| := le_abs_self _
    _ = |q| * |x t| := by rw [abs_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (abs_nonneg _)

private theorem score_bound (e : Fin 30) (z : Fin 19 → ℝ) :
    score e z ≤ (edgeWeight e : ℝ) * realNorm z := by
  by_cases he : edgeWeight e = 0
  · obtain ⟨x, rfl⟩ := fill_surjective z
    simpa [he] using score_fill_bound e x
  have he' : 0 < (edgeWeight e : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero he
  rw [mul_comm (edgeWeight e : ℝ), ← div_le_iff₀ he']
  apply le_csInf (realLengths_nonempty z)
  rintro _ ⟨x, rfl, rfl⟩
  exact (div_le_iff₀ he').mpr (by simpa [mul_comm] using score_fill_bound e x)

private theorem pull_weight (r : Fin 30 → Fin 19 → ℝ) :
    (∑ e, score e (r e)) =
      ∑ t : Fin 28, ∑ j : Fin 19, (triangleWeight t j : ℝ) *
        (∑ e : Fin 30, (edgeBoundary t e : ℝ) * r e j) := by
  simp only [score, weight_combination, Int.cast_sum, Int.cast_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j : Fin 19, ∑ t : Fin 28, ∑ e : Fin 30,
        (edgeBoundary t e : ℝ) * (triangleWeight t j : ℝ) * r e j := by
      congr 1
      ext j
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro e _
      ring

private theorem incidence_gradient (e : Fin 30) (p : Fin 12 → ℝ) :
    (∑ v : Fin 12, (incidence v e : ℝ) * p v) = p (edgeAt e).2 - p (edgeAt e).1 := by
  classical
  have h (v : Fin 12) : incidence v e =
      (if (edgeAt e).2 = v then 1 else 0) - (if (edgeAt e).1 = v then 1 else 0) := by
    have hne : (edgeAt e).1 ≠ (edgeAt e).2 := fun he => by
      have hlt := (edge_span e).1
      rw [he] at hlt
      omega
    by_cases hv : (edgeAt e).2 = v
    · simp [incidence, hv, show (edgeAt e).1 ≠ v from hv ▸ hne]
    · by_cases hv' : (edgeAt e).1 = v <;> simp [incidence, hv, hv']
  simp [h, sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq, eq_comm]

private theorem gradient_closed (t : Fin 28) (p : Fin 12 → ℝ) :
    (∑ e : Fin 30, (edgeBoundary t e : ℝ) * (p (edgeAt e).2 - p (edgeAt e).1)) = 0 := by
  simp only [← incidence_gradient, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul, mul_comm (a := (edgeBoundary t _ : ℝ)), ← Int.cast_mul,
    ← Int.cast_sum, boundary_closed]

private theorem score_residual_sum (φ : Fin 12 → Fin 19 → ℝ) :
    (∑ e : Fin 30, score e
      (realGainCoords (edgeAt e).1 (edgeAt e).2 - (φ (edgeAt e).2 - φ (edgeAt e).1))) = 98 := by
  rw [pull_weight]
  have h (t : Fin 28) (j : Fin 19) :
      (∑ e : Fin 30, (edgeBoundary t e : ℝ) *
        (realGainCoords (edgeAt e).1 (edgeAt e).2 - (φ (edgeAt e).2 - φ (edgeAt e).1)) j) =
          (boundary t j : ℝ) := by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, gradient_closed t (fun v => φ v j),
      sub_zero, realGainCoords, castCoordinates]
    exact_mod_cast boundary_reads_gain t j
  simp only [h, ← Int.cast_mul, ← Int.cast_sum, objective_value]
  norm_num

private theorem exists_large_real_error (φ : Fin 12 → Fin 19 → ℝ) :
    ∃ i j, (pathPower 12 3).Adj i j ∧ (49 / 48 : ℝ) ≤
      realNorm (realGainCoords i j - (φ j - φ i)) := by
  by_contra! h
  let r (e : Fin 30) := realGainCoords (edgeAt e).1 (edgeAt e).2 - (φ (edgeAt e).2 - φ (edgeAt e).1)
  have hsmall (e : Fin 30) : realNorm (r e) < 49 / 48 := by
    have hs := edge_span e
    have hne : (edgeAt e).1 ≠ (edgeAt e).2 := by
      intro he
      rw [he] at hs
      omega
    exact h _ _ (adj_iff.mpr ⟨hne, by omega, hs.2⟩)
  have hle (e : Fin 30) : score e (r e) ≤ (edgeWeight e : ℝ) * (49 / 48) :=
    (score_bound e (r e)).trans (mul_le_mul_of_nonneg_left (hsmall e).le (Nat.cast_nonneg _))
  have hlt (e : Fin 30) (he : 0 < edgeWeight e) :
      score e (r e) < (edgeWeight e : ℝ) * (49 / 48) :=
    (score_bound e (r e)).trans_lt (mul_lt_mul_of_pos_left (hsmall e) (by exact_mod_cast he))
  have hsum : (∑ e : Fin 30, score e (r e)) < ∑ e : Fin 30, (edgeWeight e : ℝ) * (49 / 48) :=
    Finset.sum_lt_sum (fun e _ => hle e) ⟨0, Finset.mem_univ _, hlt 0 (by decide)⟩
  rw [score_residual_sum φ, ← Finset.sum_mul, ← Nat.cast_sum, weight_sum] at hsum
  norm_num at hsum


private theorem realGain_reverse (a b : Fin 12) : realGain b a = -realGain a b := by
  funext j
  change (gainCoordinate b a j : ℝ) = -(gainCoordinate a b j : ℝ)
  rw [gain_reverse a b j, Int.cast_neg]

private theorem realGain_flat {a b c : Fin 12}
    (hab : (pathPower 12 3).Adj a b) (hbc : (pathPower 12 3).Adj b c)
    (hac : (pathPower 12 3).Adj a c) :
    Dist.dist (realGain a b + realGain b c) (realGain a c) ≤ 1 := by
  have h := realNorm_le_integralNorm (gainCoordinate a b + gainCoordinate b c - gainCoordinate a c)
  have hi := integral_triangle_bound (Or.inr hab) (Or.inr hbc) (Or.inr hac)
  have he : castCoordinates (gainCoordinate a b + gainCoordinate b c - gainCoordinate a c) =
      realGain a b + realGain b c - realGain a c := by
    funext j
    change ((gainCoordinate a b j + gainCoordinate b c j - gainCoordinate a c j : ℤ) : ℝ) = _
    change ((gainCoordinate a b j + gainCoordinate b c j - gainCoordinate a c j : ℤ) : ℝ) =
      (gainCoordinate a b j : ℝ) + (gainCoordinate b c j : ℝ) - (gainCoordinate a c j : ℝ)
    push_cast
    rfl
  rw [he] at h
  rw [dist_eq_norm_sub]
  change realNorm _ ≤ 1
  exact h.trans (by exact_mod_cast hi)

private theorem exists_large_integral_error {n : ℕ} (hn : 12 ≤ n) (φ : Fin n → IntegralCycles) :
    ∃ i j, (pathPower n 3).Adj i j ∧
      2 ≤ Dist.dist (integralGain i j) ((φ i)⁻¹ * φ j) := by
  let embed (v : Fin 12) : Fin n := ⟨v.val, v.isLt.trans_le hn⟩
  let ψ (v : Fin 12) : Fin 19 → ℝ := castCoordinates (Multiplicative.toAdd (φ (embed v)))
  obtain ⟨a, b, hab, hlower⟩ := exists_large_real_error ψ
  have hc (v : Fin 12) : rootClone (embed v) = v :=
    Fin.ext (show min v.val 11 = v.val from min_eq_left (by omega))
  have hadj : (pathPower n 3).Adj (embed a) (embed b) :=
    ⟨fun h => hab.ne (Fin.ext (congrArg (fun q : Fin n => q.val) h)), hab.2⟩
  let z : Fin 19 → ℤ := gainCoordinate a b -
    (Multiplicative.toAdd (φ (embed b)) - Multiplicative.toAdd (φ (embed a)))
  have hcast : castCoordinates z = realGainCoords a b - (ψ b - ψ a) := by
    funext j
    simp [z, realGainCoords, ψ, castCoordinates, Pi.sub_apply]
  have hnorm := realNorm_le_integralNorm z
  rw [hcast] at hnorm
  have htwo : 2 ≤ integralNorm z := by
    by_contra! h
    have hn' : (integralNorm z : ℝ) ≤ 1 := by exact_mod_cast (show integralNorm z ≤ 1 by omega)
    linarith
  refine ⟨embed a, embed b, hadj, ?_⟩
  change 2 ≤ (integralNorm (gainCoordinate (rootClone (embed a)) (rootClone (embed b)) -
      (-Multiplicative.toAdd (φ (embed a)) + Multiplicative.toAdd (φ (embed b)))) : ℝ)
  rw [hc, hc, add_comm (-Multiplicative.toAdd (φ (embed a))), ← sub_eq_add_neg]
  exact_mod_cast htwo

/-- The canonical gains are triangle-one-flat. Every real potential has error at least
(49/48), and every integral potential has error at least two. -/
theorem pathPower_three_banach_and_integral_lower_bound :
    (∀ a b, (pathPower 12 3).Adj a b → realGain b a = -realGain a b) ∧
    (∀ a b c, (pathPower 12 3).Adj a b → (pathPower 12 3).Adj b c →
      (pathPower 12 3).Adj a c → Dist.dist (realGain a b + realGain b c) (realGain a c) ≤ 1) ∧
    (∀ φ : Fin 12 → RealCycles, ∃ i j, (pathPower 12 3).Adj i j ∧
      (49 / 48 : ℝ) ≤ Dist.dist (realGain i j) (φ j - φ i)) ∧
    (∀ a b, (pathPower 12 3).Adj a b → integralGain b a = (integralGain a b)⁻¹) ∧
    (∀ a b c, (pathPower 12 3).Adj a b → (pathPower 12 3).Adj b c →
      (pathPower 12 3).Adj a c → Dist.dist (integralGain a b * integralGain b c) (integralGain a c) ≤ 1) ∧
    (∀ φ : Fin 12 → IntegralCycles, ∃ i j, (pathPower 12 3).Adj i j ∧
      2 ≤ Dist.dist (integralGain i j) ((φ i)⁻¹ * φ j)) := by
  refine ⟨fun a b _ => realGain_reverse a b, fun _ _ _ => realGain_flat, ?_,
    fun a b _ => integralGain_reverse a b, fun _ _ _ => integralGain_flat,
    exists_large_integral_error le_rfl⟩
  intro φ
  obtain ⟨i, j, ha, h⟩ := exists_large_real_error φ
  refine ⟨i, j, ha, ?_⟩
  rw [dist_eq_norm_sub]
  exact h

/-- The cloned assignment has exact minimax error two on every width-three path
with at least twelve vertices. -/
theorem pathPower_three_exact_two (n : ℕ) (hn : 12 ≤ n) :
    (∀ a b, (pathPower n 3).Adj a b → integralGain b a = (integralGain a b)⁻¹) ∧
    (∀ a b c, (pathPower n 3).Adj a b → (pathPower n 3).Adj b c →
      (pathPower n 3).Adj a c → Dist.dist (integralGain a b * integralGain b c) (integralGain a c) ≤ 1) ∧
    (∀ φ : Fin n → IntegralCycles, ∃ i j, (pathPower n 3).Adj i j ∧
      2 ≤ Dist.dist (integralGain i j) ((φ i)⁻¹ * φ j)) ∧
    (∃ φ : Fin n → IntegralCycles, ∀ i j, (pathPower n 3).Adj i j →
      Dist.dist (integralGain i j) ((φ i)⁻¹ * φ j) ≤ 2) := by
  have hrev a b (_h : (pathPower n 3).Adj a b) := integralGain_reverse a b
  have hflat a b c (hab : (pathPower n 3).Adj a b) (hbc : (pathPower n 3).Adj b c)
      (hac : (pathPower n 3).Adj a c) := integralGain_flat hab hbc hac
  refine ⟨hrev, hflat, exists_large_integral_error hn, ?_⟩
  simpa using pathPower_exists_two_approximate_gain_potential n 3 (by decide) integralGain 1
    zero_le_one hrev hflat

/-- The proposed sub-two version of uniform chordal gain reconstruction. -/
def subtwo_universal_chordal_claim : Prop :=
  ∃ C < (2 : ℝ),
    ∀ (V : Type) [Finite V] {G : SimpleGraph V}, G.IsChordal →
    ∀ (H : Type) [Group H] [PseudoMetricSpace H] [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]
      (g : V → V → H) (ε : ℝ), 0 ≤ ε →
      (∀ i j, G.Adj i j → g j i = (g i j)⁻¹) →
      (∀ i j k, G.Adj i j → G.Adj j k → G.Adj i k →
        Dist.dist (g i j * g j k) (g i k) ≤ ε) →
      ∃ φ : V → H, ∀ i j, G.Adj i j →
        Dist.dist (g i j) ((φ i)⁻¹ * φ j) ≤ C * ε

/-- No coefficient strictly smaller than two works for all finite chordal graphs
and bi-invariant pseudometric groups. -/
theorem not_subtwo_universal_chordal : ¬ subtwo_universal_chordal_claim := by
  rintro ⟨C, hC, h⟩
  obtain ⟨_, _, _, hrev, hflat, hlower⟩ := pathPower_three_banach_and_integral_lower_bound
  obtain ⟨φ, hφ⟩ := h (Fin 12) (pathPower_isChordal 12 3) IntegralCycles integralGain 1
    zero_le_one hrev hflat
  obtain ⟨i, j, hij, herror⟩ := hlower φ
  have := hφ i j hij
  linarith

example : (pathPower 0 3).IsChordal := pathPower_isChordal 0 3

example : ∃ φ : Fin 12 → IntegralCycles, ∀ i j, (pathPower 12 3).Adj i j →
    Dist.dist (1 : IntegralCycles) ((φ i)⁻¹ * φ j) ≤ 0 := by
  exact ⟨fun _ => 1, by simp⟩

end

end SimpleGraph.PathPower

