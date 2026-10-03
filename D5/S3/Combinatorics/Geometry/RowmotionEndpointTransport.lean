/- GID: D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/RowmotionEndpointTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete reverse-extension toggles transport minimal ceiling endpoints. -/

import Mathlib.Order.UpperLower.Closure
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Minimal
import Mathlib.Data.Set.SymmDiff
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport

open scoped symmDiff

variable {P : Type*} [PartialOrder P] {N : ℕ}

/-- A complete enumeration, with strictly larger points visited first. -/
def ReverseExtension (e : Fin N ≃ P) : Prop :=
  ∀ x y : P, x < y → (e.symm y).val < (e.symm x).val

/-- A point is toggled precisely when the symmetric difference is interval-closed. -/
noncomputable def toggle (x : P) (S : Set P) : Set P := by
  classical
  exact if (S ∆ {x}).OrdConnected then S ∆ {x} else S

/-- The literal successive states; after the enumeration ends the state stays fixed. -/
noncomputable def trace (e : Fin N ≃ P) (I : Set P) : ℕ → Set P
  | 0 => I
  | k + 1 => if h : k < N then toggle (e ⟨k, h⟩) (trace e I k) else trace e I k

/-- A minimal initial point below a minimal ceiling point becomes a maximal floor point,
while the ceiling point becomes maximal in the actual final toggle state. -/
theorem endpoint_transport (e : Fin N ≃ P) (he : ReverseExtension e)
    (I : Set P) (hI : I.OrdConnected) {m c : P}
    (hm : Minimal (· ∈ I) m)
    (hc : Minimal (· ∈ (upperClosure I : Set P) \ I) c) (hmc : m < c) :
    let J := trace e I N
    Maximal (· ∈ J) c ∧ Maximal (· ∈ (lowerClosure J : Set P) \ J) m := by
  classical
  let idx : P → ℕ := fun x => (e.symm x).val
  let S : ℕ → Set P := trace e I
  let J : Set P := S N
  have idx_lt (x : P) : idx x < N := (e.symm x).isLt
  have point_at (x : P) : e ⟨idx x, idx_lt x⟩ = x := e.apply_symm_apply x
  have step (k : ℕ) (hk : k < N) : S (k + 1) = toggle (e ⟨k, hk⟩) (S k) := by
    simp only [S, trace, dif_pos hk]
  have other (x y : P) (A : Set P) (hy : y ≠ x) :
      y ∈ toggle x A ↔ y ∈ A := by
    unfold toggle
    split <;> simp [Set.mem_symmDiff, hy]
  have flip_self (x : P) (A : Set P) : x ∈ A ∆ {x} ↔ x ∉ A := by
    simp [Set.mem_symmDiff]
  have flip_other (x y : P) (A : Set P) (hy : y ≠ x) :
      y ∈ A ∆ {x} ↔ y ∈ A := by
    simp [Set.mem_symmDiff, hy]
  have convex : ∀ k, (S k).OrdConnected := by
    intro k
    induction k with
    | zero => exact hI
    | succ k ih =>
      by_cases hk : k < N
      · rw [step k hk]
        unfold toggle
        split
        · assumption
        · exact ih
      · simpa only [S, trace, dif_neg hk] using ih
  have stable : ∀ b a : ℕ, a ≤ b → ∀ x : P,
      (idx x < a ∨ b ≤ idx x) → (x ∈ S b ↔ x ∈ S a) := by
    intro b
    induction b with
    | zero =>
      intro a hab x hx
      have : a = 0 := Nat.eq_zero_of_le_zero hab
      subst a
      rfl
    | succ b ih =>
      intro a hab x hx
      by_cases hab' : a ≤ b
      · have hx' : idx x < a ∨ b ≤ idx x := by omega
        have hxb : idx x ≠ b := by omega
        have hs : x ∈ S (b + 1) ↔ x ∈ S b := by
          by_cases hb : b < N
          · rw [step b hb]
            apply other
            intro hh
            have hh' := congrArg (fun z => (e.symm z).val) hh
            simp only [e.symm_apply_apply] at hh'
            exact hxb hh'
          · simp only [S, trace, dif_neg hb]
        exact hs.trans (ih a hab' x hx')
      · have : a = b + 1 := by omega
        subst a
        rfl
  have initial (y x : P) (hyx : y ≤ x) : y ∈ S (idx x) ↔ y ∈ I := by
    have hidx : idx x ≤ idx y := by
      rcases eq_or_lt_of_le hyx with h | h
      · subst y; rfl
      · exact Nat.le_of_lt (he y x h)
    exact stable (idx x) 0 (Nat.zero_le _) y (Or.inr hidx)
  have final (x y : P) (hyx : x < y) : y ∈ S (idx x) ↔ y ∈ J := by
    exact (stable N (idx x) (Nat.le_of_lt (idx_lt x)) y (Or.inl (he x y hyx))).symm
  have own (x : P) : x ∈ J ↔ x ∈ toggle x (S (idx x)) := by
    have hh := stable N (idx x + 1) (by have := idx_lt x; omega) x (Or.inl (by omega))
    rw [step (idx x) (idx_lt x), point_at x] at hh
    exact hh
  -- An initial hole between an included point and a later point blocks that later insertion.
  have blocked (u v z : P) (hu : u ∈ I) (hv : v ∉ I)
      (huv : u < v) (hvz : v < z) : z ∉ J := by
    have huz : u < z := lt_trans huv hvz
    have hzI : z ∉ I := by
      intro hz
      exact hv (hI.out hu hz ⟨le_of_lt huv, le_of_lt hvz⟩)
    have huS : u ∈ S (idx z) := (initial u z (le_of_lt huz)).mpr hu
    have hvS : v ∉ S (idx z) := fun h => hv ((initial v z (le_of_lt hvz)).mp h)
    have hzS : z ∉ S (idx z) := fun h => hzI ((initial z z le_rfl).mp h)
    have hn : ¬ (S (idx z) ∆ {z}).OrdConnected := by
      intro hh
      have huF : u ∈ S (idx z) ∆ {z} :=
        (flip_other z u (S (idx z)) (ne_of_lt huz)).mpr huS
      have hzF : z ∈ S (idx z) ∆ {z} := (flip_self z (S (idx z))).mpr hzS
      have hvF := hh.out huF hzF ⟨le_of_lt huv, le_of_lt hvz⟩
      exact hvS ((flip_other z v (S (idx z)) (ne_of_lt hvz)).mp hvF)
    intro hz
    have hh := (own z).mp hz
    exact hzS (by simpa only [toggle, if_neg hn] using hh)
  have above_c (z : P) (hcz : c < z) : z ∉ J :=
    blocked m c z hm.1 hc.1.2 hmc hcz
  have c_before : c ∉ S (idx c) := fun h => hc.1.2 ((initial c c le_rfl).mp h)
  have add_c : (S (idx c) ∆ {c}).OrdConnected := by
    constructor
    intro u hu v hv y hy
    by_cases huc : u = c
    · subst u
      have hvc : v = c := by
        by_contra hvne
        have hcv : c < v := lt_of_le_of_ne (le_trans hy.1 hy.2) (Ne.symm hvne)
        have hvS := (flip_other c v (S (idx c)) hvne).mp hv
        exact above_c v hcv ((final c v hcv).mp hvS)
      subst v
      have : y = c := le_antisymm hy.2 hy.1
      subst y
      exact (flip_self c (S (idx c))).mpr c_before
    · have huS := (flip_other c u (S (idx c)) huc).mp hu
      by_cases hvc : v = c
      · subst v
        by_cases hyc : y = c
        · subst y
          exact (flip_self c (S (idx c))).mpr c_before
        · have huI : u ∈ I := (initial u c (le_trans hy.1 hy.2)).mp huS
          have hyI : y ∈ I := by
            by_contra hyI
            have hyUp : y ∈ (upperClosure I : Set P) := mem_upperClosure.mpr ⟨u, huI, hy.1⟩
            have hcy := hc.2 ⟨hyUp, hyI⟩ hy.2
            exact hyc (le_antisymm hy.2 hcy)
          exact (flip_other c y (S (idx c)) hyc).mpr ((initial y c hy.2).mpr hyI)
      · have hvS := (flip_other c v (S (idx c)) hvc).mp hv
        by_cases hyc : y = c
        · subst y
          exact (flip_self c (S (idx c))).mpr c_before
        · exact (flip_other c y (S (idx c)) hyc).mpr ((convex (idx c)).out huS hvS hy)
  have c_final : c ∈ J := by
    apply (own c).mpr
    simpa only [toggle, if_pos add_c] using (flip_self c (S (idx c))).mpr c_before
  have m_before : m ∈ S (idx m) := (initial m m le_rfl).mpr hm.1
  have remove_m : (S (idx m) ∆ {m}).OrdConnected := by
    constructor
    intro u hu v hv y hy
    have hum : u ≠ m := by
      intro hh; subst u
      exact ((flip_self m (S (idx m))).mp hu) m_before
    have hvm : v ≠ m := by
      intro hh; subst v
      exact ((flip_self m (S (idx m))).mp hv) m_before
    have huS := (flip_other m u (S (idx m)) hum).mp hu
    have hvS := (flip_other m v (S (idx m)) hvm).mp hv
    have hym : y ≠ m := by
      intro hh; subst y
      have huI := (initial u m hy.1).mp huS
      have hmu := hm.2 huI hy.1
      exact hum (le_antisymm hy.1 hmu)
    exact (flip_other m y (S (idx m)) hym).mpr ((convex (idx m)).out huS hvS hy)
  have m_absent : m ∉ J := by
    intro hh
    have hh' := (own m).mp hh
    have hflip : m ∈ S (idx m) ∆ {m} := by
      simpa only [toggle, if_pos remove_m] using hh'
    exact ((flip_self m (S (idx m))).mp hflip) m_before
  have floor_above (y z : P) (hmy : m < y) (hyz : y < z) (hz : z ∈ J) : y ∈ J := by
    have hyI : y ∈ I := by
      by_contra hyI
      exact blocked m y z hm.1 hyI hmy hyz hz
    have hyS : y ∈ S (idx y) := (initial y y le_rfl).mpr hyI
    have hmS : m ∈ S (idx y) := (initial m y (le_of_lt hmy)).mpr hm.1
    have hzS : z ∈ S (idx y) := (final y z hyz).mpr hz
    have hn : ¬ (S (idx y) ∆ {y}).OrdConnected := by
      intro hh
      have hmF := (flip_other y m (S (idx y)) (ne_of_lt hmy)).mpr hmS
      have hzF := (flip_other y z (S (idx y)) (ne_of_gt hyz)).mpr hzS
      have hyF := hh.out hmF hzF ⟨le_of_lt hmy, le_of_lt hyz⟩
      exact ((flip_self y (S (idx y))).mp hyF) hyS
    apply (own y).mpr
    simpa only [toggle, if_neg hn] using hyS
  change Maximal (· ∈ J) c ∧ Maximal (· ∈ (lowerClosure J : Set P) \ J) m
  constructor
  · refine ⟨c_final, ?_⟩
    intro z hz hcz
    rcases eq_or_lt_of_le hcz with h | h
    · exact le_of_eq h.symm
    · exact False.elim (above_c z h hz)
  · refine ⟨⟨mem_lowerClosure.mpr ⟨c, c_final, le_of_lt hmc⟩, m_absent⟩, ?_⟩
    intro y hy hmy
    rcases eq_or_lt_of_le hmy with h | h
    · exact le_of_eq h.symm
    · obtain ⟨z, hz, hyz⟩ := mem_lowerClosure.mp hy.1
      rcases eq_or_lt_of_le hyz with hyz | hyz
      · subst z
        exact False.elim (hy.2 hz)
      · exact False.elim (hy.2 (floor_above y z h hyz hz))

#print axioms endpoint_transport

end D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport
