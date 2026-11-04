/- GID: D5/S3/FiniteGroups/BajnokBeattyCayleyNecessity
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyCayleyNecessity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Necessary congruences for arbitrary near extremal rank two signed Cayley generators. -/

import D5.S3.FiniteGroups.NearSquareLatticeRigidity
import Mathlib.Data.ZMod.Basic

/-! The affine odd coset and its actual relation lattice for arbitrary generating pairs. -/

/- proof_shape: top_strip_necessity: content.
   escape_witness: oddLattice_cover (every affine odd coset has an exact square
   representative), and kernel_not_four (the full relation kernel is not divisible by four).
   admission_basis: escape-witness. Direct frozen dependencies:
   NearSquareLatticeRigidity.near_square_rigidity and NearSquareLatticeRigidity.span_pair_index.
   The public helpers kernel_even, oddLattice_index and oddLattice_cover are
   consumed by BajnokBeattyAllRegimes.result.
   This proves only the top-strip necessary direction, for arbitrary pairs. -/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity

open NearSquareLatticeRigidity

abbrev Target (k : ℕ) := ZMod 2 × ZMod (2 * k)

/-- Signed coefficient vectors of the given radius cover the group. -/
def LeeCovers {G : Type*} [AddCommGroup G] (f : Plane →+ G) (R : ℤ) : Prop :=
  ∀ g : G, ∃ z : Plane, |z 0| + |z 1| ≤ R ∧ f z = g

/-- The integral sum-and-difference map. -/
def sumDiff : Plane →ₗ[ℤ] Plane where
  toFun z := ![z 0 + z 1, z 0 - z 1]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

/-- The relation lattice of the affine odd square. -/
def oddLattice {G : Type*} [AddCommGroup G] (f : Plane →+ G) : Submodule ℤ Plane :=
  (f.toIntLinearMap.comp sumDiff).ker

private theorem coordinates (z : Plane) :
    z = z 0 • ![(1 : ℤ), 0] + z 1 • ![(0 : ℤ), 1] := by
  ext i
  fin_cases i <;> simp

private def modTwo (k : ℕ) : Target k →+ (Fin 2 → ZMod 2) where
  toFun g := ![g.1, ZMod.castHom (dvd_mul_right 2 k) (ZMod 2) g.2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' g h := by ext i; fin_cases i <;> simp

private theorem modTwo_surjective (k : ℕ) : Function.Surjective (modTwo k) := by
  intro z
  obtain ⟨a, ha⟩ := ZMod.castHom_surjective (dvd_mul_right 2 k) (z 1)
  refine ⟨(z 0, a), ?_⟩
  ext i
  fin_cases i
  · rfl
  · exact ha

theorem kernel_even {k : ℕ} (f : Plane →+ Target k)
    (hf : Function.Surjective f) {z : Plane} (hz : f z = 0) :
    2 ∣ z 0 ∧ 2 ∣ z 1 := by
  let g := (modTwo k).comp f
  let B := Pi.basisFun (ZMod 2) (Fin 2)
  let A : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    B.constr (ZMod 2) ![g ![1, 0], g ![0, 1]]
  have hA : ∀ w : Plane, A (fun i => (w i : ZMod 2)) = g w := by
    intro w
    calc
      _ = (w 0 : ZMod 2) • g ![1, 0] + (w 1 : ZMod 2) • g ![0, 1] := by
        simp [A, B, Module.Basis.constr_apply_fintype, Fin.sum_univ_two]
      _ = w 0 • g ![1, 0] + w 1 • g ![0, 1] := by
        simp only [Int.cast_smul_eq_zsmul]
      _ = g (w 0 • ![1, 0] + w 1 • ![0, 1]) := by
        rw [map_add, map_zsmul, map_zsmul]
      _ = g w := congrArg g (coordinates w).symm
  have hsurj : Function.Surjective A := by
    intro v
    obtain ⟨w, hw⟩ := (modTwo_surjective k).comp hf v
    exact ⟨fun i => (w i : ZMod 2), (hA w).trans hw⟩
  have hinj : Function.Injective A := Finite.injective_iff_surjective.mpr hsurj
  have he : (fun i => (z i : ZMod 2)) = 0 := by
    apply hinj
    rw [hA]
    simp [g, hz]
  constructor
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (z 0) 2).mp (congrFun he 0)
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (z 1) 2).mp (congrFun he 1)

private theorem kernel_not_four {k : ℕ} (f : Plane →+ Target k)
    (hf : Function.Surjective f) :
    ¬ (∀ z : Plane, f z = 0 → 4 ∣ z 0 ∧ 4 ∣ z 1) := by
  intro h
  obtain ⟨z, hz⟩ := hf (1, 0)
  have h2 : f (2 • z) = 0 := by
    rw [map_nsmul, hz]
    apply Prod.ext
    · change (2 : ℕ) • (1 : ZMod 2) = 0
      decide
    · simp
  obtain ⟨h0, h1⟩ := h (2 • z) h2
  have he0 : 2 ∣ z 0 := by change 4 ∣ (2 : ℤ) * z 0 at h0; omega
  have he1 : 2 ∣ z 1 := by change 4 ∣ (2 : ℤ) * z 1 at h1; omega
  obtain ⟨x, hx⟩ := he0
  obtain ⟨y, hy⟩ := he1
  have he : z = 2 • (![x, y] : Plane) := by
    ext i; fin_cases i <;> simp [hx, hy]
  have hh := congrArg Prod.fst hz
  rw [he, map_nsmul] at hh
  change (2 : ℕ) • (f ![x, y]).1 = 1 at hh
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [nsmul_eq_mul] at hh
  change (2 : ZMod 2) * (f ![x, y]).1 = 1 at hh
  rw [htwo, zero_mul] at hh
  exact zero_ne_one hh

theorem sumDiff_injective : Function.Injective sumDiff := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  change x 0 + x 1 = y 0 + y 1 at h0
  change x 0 - x 1 = y 0 - y 1 at h1
  ext i
  fin_cases i
  · change x 0 = y 0
    omega
  · change x 1 = y 1
    omega

private theorem sumDiff_range : sumDiff.range =
    Submodule.span ℤ (Set.range ![![(1 : ℤ), 1], ![(1 : ℤ), -1]]) := by
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    rw [coordinates w, map_add, map_smul, map_smul]
    apply Submodule.add_mem
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨0, rfl⟩
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨1, rfl⟩
  · apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact ⟨![1, 0], by ext j; fin_cases j <;> norm_num [sumDiff]⟩
    · exact ⟨![0, 1], by ext j; fin_cases j <;> norm_num [sumDiff]⟩

theorem sumDiff_index : sumDiff.range.toAddSubgroup.index = 2 := by
  rw [sumDiff_range, span_pair_index _ _ (by norm_num)]
  norm_num

private theorem oddLattice_map {k : ℕ} (f : Plane →+ Target k)
    (hf : Function.Surjective f) :
    (oddLattice f).map sumDiff = f.toIntLinearMap.ker := by
  apply le_antisymm
  · rintro z ⟨w, hw, rfl⟩
    exact hw
  · intro z hz
    obtain ⟨h0, h1⟩ := kernel_even f hf hz
    obtain ⟨x, hx⟩ := h0
    obtain ⟨y, hy⟩ := h1
    have he : sumDiff ![x+y, x-y] = z := by
      ext i
      fin_cases i <;> simp [sumDiff] <;> omega
    exact ⟨![x+y, x-y], by change f (sumDiff _) = 0; rw [he]; exact hz, he⟩

theorem oddLattice_index {k : ℕ} (hk : 0 < k) (f : Plane →+ Target k)
    (hf : Function.Surjective f) : (oddLattice f).toAddSubgroup.index = 2 * k := by
  have hi := AddSubgroup.index_map_of_injective
    (H := (oddLattice f).toAddSubgroup) (f := sumDiff.toAddMonoidHom) sumDiff_injective
  change ((oddLattice f).map sumDiff).toAddSubgroup.index =
    (oddLattice f).toAddSubgroup.index * sumDiff.range.toAddSubgroup.index at hi
  rw [oddLattice_map f hf, sumDiff_index] at hi
  have hker : f.ker.index = 4 * k := by
    rw [AddSubgroup.index_ker, f.range_eq_top_of_surjective hf, AddSubgroup.card_top]
    simp [Target, Nat.card_prod, Nat.card_zmod]
    omega
  change f.ker.index = _ at hi
  omega

private theorem oddLattice_parity {k : ℕ} (f : Plane →+ Target k)
    (hf : Function.Surjective f) {z : Plane} (hz : z ∈ oddLattice f) :
    2 ∣ z 0 + z 1 := by
  have he := (kernel_even f hf hz).1
  simpa [sumDiff] using he

theorem oddLattice_cover {k : ℕ} (f : Plane →+ Target k) {t : ℤ}
    (hcover : LeeCovers f (2 * t)) : RectangleCovers (oddLattice f) (2*t) (2*t) := by
  have hf : Function.Surjective f := fun g => by obtain ⟨z, _, hz⟩ := hcover g; exact ⟨z, hz⟩
  intro z
  let v : Plane := ![z 0 - t + (z 1 - t) + 1, z 0 - t - (z 1 - t)]
  obtain ⟨w, hw, hfw⟩ := hcover (f v)
  have hker : f (w-v) = 0 := by rw [map_sub, hfw, sub_self]
  obtain ⟨h0, h1⟩ := kernel_even f hf hker
  change 2 ∣ w 0 - v 0 at h0
  change 2 ∣ w 1 - v 1 at h1
  dsimp [v] at h0 h1
  obtain ⟨i, hi⟩ := h0
  obtain ⟨j, hj⟩ := h1
  change w 0 - (z 0 - t + (z 1 - t) + 1) = 2 * i at hi
  change w 1 - (z 0 - t - (z 1 - t)) = 2 * j at hj
  let x := (w 0 + w 1 - 1) / 2
  let y := (w 0 - w 1 - 1) / 2
  have hs : w 0 + w 1 = 2*x+1 := by dsimp [x]; omega
  have hd : w 0 - w 1 = 2*y+1 := by dsimp [y]; omega
  have hw0 := le_abs_self (w 0)
  have hw1 := le_abs_self (w 1)
  have hw0' := neg_abs_le (w 0)
  have hw1' := neg_abs_le (w 1)
  have hx : -t ≤ x ∧ x < t := by constructor <;> omega
  have hy : -t ≤ y ∧ y < t := by constructor <;> omega
  refine ⟨x+t, y+t, by omega, by omega, by omega, by omega, ?_⟩
  change f (sumDiff (z - ![x+t, y+t])) = 0
  have he : sumDiff (z - ![x+t, y+t]) = v-w := by
    ext i
    fin_cases i
    · change z 0 - (x+t) + (z 1 - (y+t)) =
        (z 0 - t + (z 1 - t) + 1) - w 0
      omega
    · change z 0 - (x+t) - (z 1 - (y+t)) =
        (z 0 - t - (z 1 - t)) - w 1
      omega
  rw [he, map_sub, hfw, sub_self]

private def fourPlane : Submodule ℤ Plane where
  carrier := {z | 4 ∣ z 0 ∧ 4 ∣ z 1}
  zero_mem' := ⟨dvd_zero _, dvd_zero _⟩
  add_mem' hx hy := ⟨dvd_add hx.1 hy.1, dvd_add hx.2 hy.2⟩
  smul_mem' c z hz := ⟨dvd_mul_of_dvd_right hz.1 c, dvd_mul_of_dvd_right hz.2 c⟩

private theorem hom_top_strip_necessity {k : ℕ} {t r : ℤ}
    (ht : 1 ≤ t) (hr : 0 ≤ r) (hrt : r < t)
    (hk : (k : ℤ) = 2 * t ^ 2 - r)
    (f : Plane →+ Target k) (hcover : LeeCovers f (2*t)) :
    2 ∣ r ∧ (Odd t → 4 ∣ r) := by
  have hf : Function.Surjective f := fun g => by
    obtain ⟨z, _, hz⟩ := hcover g
    exact ⟨z, hz⟩
  have hkpos : 0 < k := by
    have : (0 : ℤ) < k := by nlinarith [sq_nonneg (t-1)]
    exact_mod_cast this
  have hi : ((oddLattice f).toAddSubgroup.index : ℤ) = (2*t)^2 - 2*r := by
    rw [oddLattice_index hkpos f hf]
    push_cast
    nlinarith
  obtain ⟨a, b, ε, ha, han, hb, hbn, hε, hab, hL⟩ := near_square_rigidity
    (oddLattice f) (by omega) (by omega) (by omega) hi (oddLattice_cover f hcover)
  have hu : ![2*t, -ε*b] ∈ oddLattice f := by
    rw [hL]
    exact Submodule.subset_span ⟨0, rfl⟩
  have hv : ![-a, ε*(2*t)] ∈ oddLattice f := by
    rw [hL]
    exact Submodule.subset_span ⟨1, rfl⟩
  have h2b : 2 ∣ b := by
    have h := oddLattice_parity f hf hu
    change 2 ∣ 2*t + -ε*b at h
    rcases hε with rfl | rfl <;> omega
  have h2a : 2 ∣ a := by
    have h := oddLattice_parity f hf hv
    change 2 ∣ -a + ε*(2*t) at h
    rcases hε with rfl | rfl <;> omega
  obtain ⟨u, hau⟩ := h2a
  obtain ⟨v, hbv⟩ := h2b
  have hrprod : r = 2*(u*v) := by
    rw [hau, hbv] at hab
    nlinarith [hab]
  refine ⟨⟨u*v, hrprod⟩, ?_⟩
  intro htodd
  by_contra hr4
  have huodd : u % 2 = 1 := by
    by_contra h
    have hu2 : 2 ∣ u := by omega
    obtain ⟨w, hw⟩ := hu2
    apply hr4
    rw [hw] at hrprod
    exact ⟨w*v, by nlinarith⟩
  have hvodd : v % 2 = 1 := by
    by_contra h
    have hv2 : 2 ∣ v := by omega
    obtain ⟨w, hw⟩ := hv2
    apply hr4
    rw [hw] at hrprod
    exact ⟨u*w, by nlinarith⟩
  have htmod : t % 2 = 1 := by obtain ⟨w, hw⟩ := htodd; omega
  have hle : oddLattice f ≤ fourPlane.comap sumDiff := by
    rw [hL]
    apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    fin_cases i
    · change 4 ∣ 2*t + -ε*b ∧ 4 ∣ 2*t - -ε*b
      rcases hε with rfl | rfl <;> constructor <;> omega
    · change 4 ∣ -a + ε*(2*t) ∧ 4 ∣ -a - ε*(2*t)
      rcases hε with rfl | rfl <;> constructor <;> omega
  apply kernel_not_four f hf
  intro z hz
  have hzmem : z ∈ (oddLattice f).map sumDiff := by
    rw [oddLattice_map f hf]
    exact hz
  obtain ⟨w, hw, rfl⟩ := hzmem
  exact hle hw

/-- Every signed Cayley pair covering the top strip satisfies the necessary congruences. -/
theorem top_strip_necessity {t r : ℤ} {k : ℕ}
    (ht : 1 ≤ t) (hr : 0 ≤ r) (hrt : r < t)
    (hk : (k : ℤ) = 2 * t ^ 2 - r)
    (a b : Target k)
    (hcover : ∀ g : Target k, ∃ x y : ℤ,
      |x| + |y| ≤ 2*t ∧ x • a + y • b = g) :
    2 ∣ r ∧ (Odd t → 4 ∣ r) := by
  let f : Plane →+ Target k := {
    toFun := fun z => z 0 • a + z 1 • b
    map_zero' := by simp
    map_add' := by intro z w; simp only [Pi.add_apply, add_zsmul]; abel }
  apply hom_top_strip_necessity ht hr hrt hk f
  intro g
  obtain ⟨x, y, hxy, he⟩ := hcover g
  exact ⟨![x,y], hxy, he⟩

end D5.S3.FiniteGroups.BajnokBeattyCayleyNecessity
