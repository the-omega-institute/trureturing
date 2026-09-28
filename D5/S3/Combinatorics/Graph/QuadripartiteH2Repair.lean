/- GID: D5/S3/Combinatorics/Graph/QuadripartiteH2Repair
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/QuadripartiteH2Repair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate geodesics in the dual four-cube have the prescribed two-terminal boundary and exact support cost. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import D5.S3.Combinatorics.Graph.OctahedralCochainSharpness
import D5.S3.Combinatorics.Graph.TripartiteH1Repair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.QuadripartiteH2Repair

open D5.S3.Combinatorics.Graph.OctahedralCochainSharpness

def hamming4 (x y : Cube) : Nat :=
  (if x.1 ≠ y.1 then 1 else 0) +
    (if x.2.1 ≠ y.2.1 then 1 else 0) +
    (if x.2.2.1 ≠ y.2.2.1 then 1 else 0) +
    (if x.2.2.2 ≠ y.2.2.2 then 1 else 0)

def geodesic (x y : Cube) : Cochain := fun f =>
  if f = ((0 : Fin 4), drop 0 x) ∧ x.1 ≠ y.1 then 1 else
  if f = ((1 : Fin 4), drop 1 (y.1, x.2.1, x.2.2.1, x.2.2.2)) ∧
      x.2.1 ≠ y.2.1 then 1 else
  if f = ((2 : Fin 4), drop 2 (y.1, y.2.1, x.2.2.1, x.2.2.2)) ∧
      x.2.2.1 ≠ y.2.2.1 then 1 else
  if f = ((3 : Fin 4), drop 3 (y.1, y.2.1, y.2.2.1, x.2.2.2)) ∧
      x.2.2.2 ≠ y.2.2.2 then 1 else 0

/-- A coordinate geodesic has boundary exactly at its two endpoints. -/
theorem geodesic_boundary (x y : Cube) (b : Cube) :
    d2 (geodesic x y) b =
      (if b = x then 1 else 0) + (if b = y then 1 else 0) := by
  rcases x with ⟨x₀, x₁, x₂, x₃⟩
  rcases y with ⟨y₀, y₁, y₂, y₃⟩
  rcases b with ⟨b₀, b₁, b₂, b₃⟩
  cases x₀ <;> cases x₁ <;> cases x₂ <;> cases x₃ <;>
    cases y₀ <;> cases y₁ <;> cases y₂ <;> cases y₃ <;>
    cases b₀ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;>
    decide +kernel

/-- The support of a coordinate geodesic is its four-coordinate Hamming distance. -/
theorem geodesic_weight (x y : Cube) :
    weight (geodesic x y) = hamming4 x y := by
  rcases x with ⟨x₀, x₁, x₂, x₃⟩
  rcases y with ⟨y₀, y₁, y₂, y₃⟩
  cases x₀ <;> cases x₁ <;> cases x₂ <;> cases x₃ <;>
    cases y₀ <;> cases y₁ <;> cases y₂ <;> cases y₃ <;>
    decide +kernel


#print axioms geodesic_boundary
#print axioms geodesic_weight

private theorem even_defect_filling (s : Finset Cube) (hs : (s.card : ZMod 2) = 0) :
    ∃ h : Cochain,
      (∀ b : Cube, d2 h b = if b ∈ s then 1 else 0) ∧
      weight h ≤ 2 * s.card := by
  classical
  have path_data : ∀ x y : Cube,
      (∀ b : Cube, d2 (geodesic x y) b =
        (if b = x then 1 else 0) + (if b = y then 1 else 0)) ∧
      weight (geodesic x y) ≤ 4 := by
    intro x y
    refine ⟨geodesic_boundary x y, ?_⟩
    rw [geodesic_weight]
    unfold hamming4
    have h0 : (if x.1 ≠ y.1 then 1 else 0) ≤ 1 := by split <;> omega
    have h1 : (if x.2.1 ≠ y.2.1 then 1 else 0) ≤ 1 := by split <;> omega
    have h2 : (if x.2.2.1 ≠ y.2.2.1 then 1 else 0) ≤ 1 := by split <;> omega
    have h3 : (if x.2.2.2 ≠ y.2.2.2 then 1 else 0) ≤ 1 := by split <;> omega
    omega
  have subadd (h k : Cochain) : weight (h + k) ≤ weight h + weight k := by
    have point (x y : ZMod 2) :
        (if x + y ≠ 0 then (1 : ℕ) else 0) ≤
          (if x ≠ 0 then 1 else 0) + (if y ≠ 0 then 1 else 0) := by
      have z_cases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by
        intro z
        by_cases hz : z = 0
        · exact Or.inl hz
        · right
          apply (ZMod.val_eq_one (by decide) z).mp
          have hzv : z.val ≠ 0 := by
            intro hzv
            exact hz ((ZMod.val_eq_zero z).mp hzv)
          have hzlt := z.val_lt
          omega
      rcases z_cases x with rfl | rfl <;> rcases z_cases y with rfl | rfl <;> decide
    have family (u v : Cochain) :
        (∑ f : Face, if u f + v f ≠ 0 then 1 else 0) ≤
          (∑ f : Face, if u f ≠ 0 then 1 else 0) +
            ∑ f : Face, if v f ≠ 0 then 1 else 0 := by
      simp_rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun f _ => point _ _
    simpa [weight, Pi.add_apply] using family h k
  revert hs
  refine s.strongInductionOn ?_
  intro s ih hs
  by_cases he : s = ∅
  · subst s
    exact ⟨0, by simp [d2], by simp [weight]⟩
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hrest : (s.erase x).Nonempty := by
    by_contra hn
    have hz : s.erase x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hcard : s.card = 1 := by simpa [hz] using (Finset.card_erase_add_one hx).symm
    rw [hcard] at hs
    exact (by decide : (1 : ZMod 2) ≠ 0) hs
  obtain ⟨y, hy⟩ := hrest
  have hcard : ((s.erase x).erase y).card + 2 = s.card := by
    have hxcard := Finset.card_erase_add_one hx
    have hycard := Finset.card_erase_add_one hy
    omega
  have hpar : ((((s.erase x).erase y).card : ℕ) : ZMod 2) = 0 := by
    have hz := congrArg (fun n : ℕ => (n : ZMod 2)) hcard
    simpa [hs, show (2 : ZMod 2) = 0 by decide] using hz
  have hsub : (s.erase x).erase y ⊂ s :=
    Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset _ _)
      (Finset.erase_ssubset hx)
  obtain ⟨h, hh, hweight⟩ := ih _ hsub hpar
  refine ⟨h + geodesic x y, ?_, ?_⟩
  · intro b
    have hxy : y ≠ x := (Finset.mem_erase.mp hy).1
    have hymem : y ∈ s := (Finset.mem_erase.mp hy).2
    rw [show d2 (h + geodesic x y) b = d2 h b + d2 (geodesic x y) b by
      simp [d2, Finset.sum_add_distrib]]
    rw [hh, (path_data x y).1 b]
    by_cases hbx : b = x <;> by_cases hby : b = y <;>
      simp [hbx, hby, hx, hymem, hxy, Ne.symm hxy]
  · have hp := (path_data x y).2
    exact le_trans (subadd h (geodesic x y)) (by omega)

set_option maxHeartbeats 4000000 in
theorem universal_repair (p q : ℕ) :
    (∀ F : Cochain, ∃ e : EdgeCochain,
      q * weight (F + d1 e) ≤ p * defects F) ↔ 2 * q ≤ p := by
  classical
  have upper (F : Cochain) :
      ∃ e : EdgeCochain, weight (F + d1 e) ≤ 2 * defects F := by
    let s : Finset Cube := Finset.univ.filter fun b => d2 F b ≠ 0
    have bit_value (z : ZMod 2) : (if z ≠ 0 then 1 else 0) = z := by
      have z_cases : z = 0 ∨ z = 1 := by
        by_cases hz : z = 0
        · exact Or.inl hz
        · right
          apply (ZMod.val_eq_one (by decide) z).mp
          have hzv : z.val ≠ 0 := by
            intro hzv
            exact hz ((ZMod.val_eq_zero z).mp hzv)
          have hzlt := z.val_lt
          omega
      rcases z_cases with rfl | rfl <;> simp
    have hs : (s.card : ZMod 2) = 0 := by
      calc
        (s.card : ZMod 2) = ∑ b : Cube, d2 F b := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum]
          simp only [Nat.cast_one, s, Finset.sum_filter]
          exact Finset.sum_congr rfl fun b _ => bit_value _
        _ = 0 := by
          simp [d2, Finset.sum_add_distrib, Fintype.sum_prod_type, drop,
            Fin.sum_univ_succ]
          ring_nf
          simp [show (2 : ZMod 2) = 0 by decide]
    have hcard : s.card = defects F := by
      simp only [s, defects, Finset.card_eq_sum_ones, Finset.sum_filter,
        Fintype.sum_prod_type]
    obtain ⟨H, hH, hweight⟩ := even_defect_filling s hs
    have hsame (b : Cube) : d2 H b = d2 F b := by
      rw [hH]
      by_cases hz : d2 F b = 0
      · have : b ∉ s := by simp [s, hz]
        simp [this, hz]
      · have : b ∈ s := by simp [s, hz]
        have hone : d2 F b = 1 := by
          calc
            d2 F b = if d2 F b ≠ 0 then 1 else 0 := (bit_value _).symm
            _ = 1 := by simp [hz]
        simp [this, hone]
    have hzero (b : Cube) : d2 (F + H) b = 0 := by
      rw [show d2 (F + H) b = d2 F b + d2 H b by
        simp [d2, Finset.sum_add_distrib]]
      rw [hsame]
      exact CharTwo.add_self_eq_zero _
    have hexact : ∀ K : Cochain, (∀ b : Cube, d2 K b = 0) →
        ∃ e : EdgeCochain, ∀ f : Face, d1 e f = K f := by
      intro K hK
      let C : Bool → Bool → Bool → Bool → ZMod 2 :=
        fun a b c d =>
          K ((0 : Fin 4), (b, c, d)) + K ((1 : Fin 4), (a, c, d)) +
            K ((2 : Fin 4), (a, b, d)) + K ((3 : Fin 4), (a, b, c))
      let eAB : Bool → Bool → ZMod 2 := fun a b => K ((2 : Fin 4), (a, b, false))
      let eAC : Bool → Bool → ZMod 2 := fun a c => K ((1 : Fin 4), (a, c, false))
      let eBC : Bool → Bool → ZMod 2 := fun b c => K ((0 : Fin 4), (b, c, false))
      let eAD : Bool → Bool → ZMod 2 :=
        fun a d => K ((1 : Fin 4), (a, false, d)) + K ((1 : Fin 4), (a, false, false))
      let eBD : Bool → Bool → ZMod 2 :=
        fun b d => K ((0 : Fin 4), (b, false, d)) + K ((0 : Fin 4), (b, false, false))
      let eCD : Bool → Bool → ZMod 2 :=
        fun c d => K ((0 : Fin 4), (false, c, d)) + K ((0 : Fin 4), (false, c, false)) +
          K ((0 : Fin 4), (false, false, d)) + K ((0 : Fin 4), (false, false, false))
      let E : EdgeCochain := fun t =>
        (∑ a : Bool, ∑ b : Bool, if t = {(0, a), (1, b)} then eAB a b else 0) +
        (∑ a : Bool, ∑ c : Bool, if t = {(0, a), (2, c)} then eAC a c else 0) +
        (∑ a : Bool, ∑ d : Bool, if t = {(0, a), (3, d)} then eAD a d else 0) +
        (∑ b : Bool, ∑ c : Bool, if t = {(1, b), (2, c)} then eBC b c else 0) +
        (∑ b : Bool, ∑ d : Bool, if t = {(1, b), (3, d)} then eBD b d else 0) +
        (∑ c : Bool, ∑ d : Bool, if t = {(2, c), (3, d)} then eCD c d else 0)
      have hc (a b c d : Bool) : C a b c d = 0 := by
        simpa [C, d2, Fin.sum_univ_succ, drop, add_assoc] using hK (a, b, c, d)
      have hC (a b c d : Bool) :
          K ((0 : Fin 4), (b, c, d)) + K ((1 : Fin 4), (a, c, d)) +
            K ((2 : Fin 4), (a, b, d)) + K ((3 : Fin 4), (a, b, c)) = 0 := by
        simpa [C] using hc a b c d
      have hAB (a b : Bool) : E {(0, a), (1, b)} = eAB a b := by
        cases a <;> cases b <;> simp [E, Finset.ext_iff, Fin.forall_fin_succ]
      have hAC (a c : Bool) : E {(0, a), (2, c)} = eAC a c := by
        cases a <;> cases c <;> simp [E, Finset.ext_iff, Fin.forall_fin_succ]
      have hAD (a d : Bool) : E {(0, a), (3, d)} = eAD a d := by
        cases a <;> cases d <;> simp [E, Finset.ext_iff, Fin.forall_fin_succ]
      have hBC (b c : Bool) : E {(1, b), (2, c)} = eBC b c := by
        cases b <;> cases c <;> simp [E, Finset.ext_iff, Fin.forall_fin_succ]
      have hBD (b d : Bool) : E {(1, b), (3, d)} = eBD b d := by
        cases b <;> cases d <;> simp [E, Finset.ext_iff, Fin.forall_fin_succ]
      have hCD (c d : Bool) : E {(2, c), (3, d)} = eCD c d := by
        cases c <;> cases d <;> simp [E, Finset.ext_iff, Fin.forall_fin_succ]
      have face3 (a b c : Bool) :
          K ((3 : Fin 4), (a, b, c)) =
            K ((2 : Fin 4), (a, b, false)) + K ((1 : Fin 4), (a, c, false)) +
              K ((0 : Fin 4), (b, c, false)) := by
        linear_combination (norm := ring_nf) hC a b c false
        simp [show (2 : ZMod 2) = 0 by decide]
      have face2 (a b d : Bool) :
          K ((2 : Fin 4), (a, b, d)) =
            K ((2 : Fin 4), (a, b, false)) +
              (K ((1 : Fin 4), (a, false, d)) + K ((1 : Fin 4), (a, false, false))) +
              (K ((0 : Fin 4), (b, false, d)) + K ((0 : Fin 4), (b, false, false))) := by
        linear_combination (norm := ring_nf) (hC a b false d) + (hC a b false false)
        simp [show (2 : ZMod 2) = 0 by decide]
      have face1 (a c d : Bool) :
          K ((1 : Fin 4), (a, c, d)) =
            K ((1 : Fin 4), (a, c, false)) +
              (K ((1 : Fin 4), (a, false, d)) + K ((1 : Fin 4), (a, false, false))) +
              (K ((0 : Fin 4), (false, c, d)) + K ((0 : Fin 4), (false, c, false)) +
                K ((0 : Fin 4), (false, false, d)) +
                  K ((0 : Fin 4), (false, false, false))) := by
        linear_combination (norm := ring_nf) (hC a false c d) + (hC a false c false) +
          (hC a false false d) + (hC a false false false)
        simp [show (2 : ZMod 2) = 0 by decide]
      have face0 (b c d : Bool) :
          K ((0 : Fin 4), (b, c, d)) =
            K ((0 : Fin 4), (b, c, false)) +
              (K ((0 : Fin 4), (b, false, d)) + K ((0 : Fin 4), (b, false, false))) +
              (K ((0 : Fin 4), (false, c, d)) + K ((0 : Fin 4), (false, c, false)) +
                K ((0 : Fin 4), (false, false, d)) +
                  K ((0 : Fin 4), (false, false, false))) := by
        linear_combination (norm := ring_nf) (hC false b c d) + (hC false b c false) +
          (hC false b false d) + (hC false b false false) + (face1 false c d)
        simp [show (2 : ZMod 2) = 0 by decide]
      refine ⟨E, ?_⟩
      intro f
      rcases f with ⟨i, a, b, c⟩
      fin_cases i
      · change E {(1, a), (2, b)} + E {(1, a), (3, c)} +
          E {(2, b), (3, c)} = K ((0 : Fin 4), (a, b, c))
        rw [hBC a b, hBD a c, hCD b c]
        exact (face0 a b c).symm
      · change E {(0, a), (2, b)} + E {(0, a), (3, c)} +
          E {(2, b), (3, c)} = K ((1 : Fin 4), (a, b, c))
        rw [hAC a b, hAD a c, hCD b c]
        exact (face1 a b c).symm
      · change E {(0, a), (1, b)} + E {(0, a), (3, c)} +
          E {(1, b), (3, c)} = K ((2 : Fin 4), (a, b, c))
        rw [hAB a b, hAD a c, hBD b c]
        exact (face2 a b c).symm
      · change E {(0, a), (1, b)} + E {(0, a), (2, c)} +
          E {(1, b), (2, c)} = K ((3 : Fin 4), (a, b, c))
        rw [hAB a b, hAC a c, hBC b c]
        exact (face3 a b c).symm
    obtain ⟨e, he⟩ := hexact (F + H) hzero
    refine ⟨e, ?_⟩
    have heq : F + d1 e = H := by
      funext f
      have hf := he f
      change F f + d1 e f = H f
      rw [hf]
      change F f + (F f + H f) = H f
      ring_nf
      simp [show (2 : ZMod 2) = 0 by decide]
    rw [heq]
    simpa [hcard] using hweight
  constructor
  · intro h
    obtain ⟨e, he⟩ := h path
    have hlow := (antipodal_repair_sharpness).2.2.2.2.2.2.2.2 e
    have hp : 4 * q ≤ p * 2 := by
      exact le_trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left q hlow) he
    omega
  · intro hp F
    obtain ⟨e, he⟩ := upper F
    refine ⟨e, ?_⟩
    nlinarith

#print axioms universal_repair

end D5.S3.Combinatorics.Graph.QuadripartiteH2Repair
