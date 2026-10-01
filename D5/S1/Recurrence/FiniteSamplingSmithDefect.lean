/- GID: D5/S1/Recurrence/FiniteSamplingSmithDefect
   generality: I
   mirror-B: D5/B/S1/Recurrence/FiniteSamplingSmithDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral normal form and modular kernel for Fibonacci samples. -/

import D5.S1.Recurrence.FiniteColumnGcdNormalization
import D5.S1.Recurrence.FibVajda
import D5.S1.Scale.Fibonacci
import D5.S1.Recurrence.LucasCompanion
import Mathlib.LinearAlgebra.FreeModule.PID

open Matrix
open D5.S1.Recurrence.FiniteColumnGcdNormalization

namespace D5.S1.Recurrence.FiniteSamplingSmithDefect

/-- Finite Fibonacci sampling has integral factors `1` and `fib g`; its modular kernel is
controlled by their common time step, including modulus one. -/
theorem finite_sampling_smith_defect (m : ℕ) (hm : 2 ≤ m)
    (t : Fin m → ℕ) (ht : StrictMono t) :
    let i0 : Fin m := ⟨0, by omega⟩
    let g := (Finset.univ.erase i0).gcd (fun i => t i - t i0)
    let H : Matrix (Fin m) (Fin 2) ℤ := fun i =>
      ![(Nat.fib (t i) : ℤ), (Nat.fib (t i + 1) : ℤ)]
    let D : Matrix (Fin m) (Fin 2) ℤ := fun i j =>
      if i.val = 0 ∧ j = 0 then 1
      else if i.val = 1 ∧ j = 1 then (Nat.fib g : ℤ) else 0
    0 < Nat.fib g ∧
    ∃ (U : (Matrix (Fin m) (Fin m) ℤ)ˣ)
      (V : (Matrix (Fin 2) (Fin 2) ℤ)ˣ),
      (U : Matrix (Fin m) (Fin m) ℤ) * H * (V : Matrix (Fin 2) (Fin 2) ℤ) = D ∧
      ∀ (N : ℕ), 0 < N →
        Nat.card ((H.map (Int.castRingHom (ZMod N))).mulVecLin.ker) =
          Nat.gcd N (Nat.fib g) ∧
        (Function.Injective (H.map (Int.castRingHom (ZMod N))).mulVec ↔
          Nat.gcd N (Nat.fib g) = 1) := by
  classical
  dsimp only
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  let s := t i0
  let A : Matrix (Fin 2) (Fin 2) ℤ :=
    !![(Nat.fib (s + 1) : ℤ) - Nat.fib s, Nat.fib s;
      Nat.fib s, Nat.fib (s + 1)]
  have hA : IsUnit A := by
    dsimp only [A]
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    have hc := D5.S1.Scale.fib_cassini_from_golden_norm s
    have hr : (Nat.fib (s+2) : ℤ) = Nat.fib s + Nat.fib (s+1) := by
      exact_mod_cast (Nat.fib_add_two (n := s))
    have hd : (!![(Nat.fib (s+1) : ℤ) - Nat.fib s, Nat.fib s;
        Nat.fib s, Nat.fib (s+1)] : Matrix (Fin 2) (Fin 2) ℤ).det = (-1 : ℤ)^s := by
      simp only [Matrix.det_fin_two_of]
      rw [hr, pow_succ (-1 : ℤ)] at hc
      nlinarith
    rw [hd]
    exact (isUnit_one : IsUnit (1 : ℤ)).neg.pow s
  have hrow (s d : ℕ) :
      ![(Nat.fib (s+d) : ℤ), (Nat.fib (s+d+1) : ℤ)] =
      Matrix.vecMul ![(Nat.fib d : ℤ), (Nat.fib (d+1) : ℤ)]
        !![(Nat.fib (s+1) : ℤ) - Nat.fib s, Nat.fib s;
          Nat.fib s, Nat.fib (s+1)] := by
    have ha : (Nat.fib (s+d+1) : ℤ) =
        Nat.fib s * Nat.fib d + Nat.fib (s+1) * Nat.fib (d+1) := by
      exact_mod_cast Nat.fib_add s d
    have hb : (Nat.fib (s+d+2) : ℤ) =
        Nat.fib s * Nat.fib (d+1) + Nat.fib (s+1) * Nat.fib (d+2) := by
      exact_mod_cast (show Nat.fib (s+d+2) = _ by
        simpa only [Nat.add_assoc] using Nat.fib_add s (d+1))
    have hc : (Nat.fib (s+d+2) : ℤ) = Nat.fib (s+d) + Nat.fib (s+d+1) := by
      exact_mod_cast (Nat.fib_add_two (n := s+d))
    have hd : (Nat.fib (d+2) : ℤ) = Nat.fib d + Nat.fib (d+1) := by
      exact_mod_cast (Nat.fib_add_two (n := d))
    ext j
    fin_cases j <;> simp [Matrix.vecMul, Fin.sum_univ_two] <;> nlinarith
  let H : Matrix (Fin m) (Fin 2) ℤ := fun i =>
    ![(Nat.fib (t i) : ℤ), (Nat.fib (t i+1) : ℤ)]
  let f : Fin m → ℤ := fun i => Nat.fib (t i - s)
  let q : Fin m → ℤ := fun i => Nat.fib (t i - s + 1)
  let B : Matrix (Fin m) (Fin 2) ℤ := fun i => ![f i, q i]
  have hshift : H = B * A := by
    ext i j
    change H i j = ∑ k : Fin 2, B i k * A k j
    have hle : s ≤ t i := ht.monotone (show 0 ≤ i.val from Nat.zero_le _)
    have h := congrFun (hrow s (t i - s)) j
    simpa only [H, B, A, f, q, Matrix.vecMul, dotProduct,
      Nat.add_sub_of_le hle] using h
  have hundo : H * A⁻¹ = B := by
    rw [hshift, Matrix.mul_assoc, Matrix.mul_nonsing_inv A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA), Matrix.mul_one]
  have hf0 : f i0 = 0 := by simp [f, s]
  have hq0 : q i0 = 1 := by simp [q, s]
  let clear : (Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ) :=
    { toFun := fun x i => if i = i0 then x i else x i - q i * x i0
      invFun := fun x i => if i = i0 then x i else x i + q i * x i0
      left_inv := by intro x; ext i; by_cases h : i = i0 <;> simp [h]
      right_inv := by intro x; ext i; by_cases h : i = i0 <;> simp [h]
      map_add' := by intro x y; ext i; by_cases h : i = i0 <;> simp [h, mul_add] <;> ring
      map_smul' := by intro r x; ext i; by_cases h : i = i0 <;> simp [h, smul_eq_mul] <;> ring }
  have hcf : clear f = f := by ext i; by_cases h : i = i0 <;> simp [clear, h, hf0]
  have hcq : clear q = Pi.single i0 1 := by
    ext i; by_cases h : i = i0 <;> simp [clear, h, hq0, Pi.single_apply]
  let all : Finset (Fin m) := Finset.univ.erase i0
  let tail := all.erase i1
  have h1 : i1 ∈ all := by simp [all, Ne.symm h01]
  have hlt : t i0 < t i1 := ht (by simp [i0, i1])
  have hgpos : 0 < all.gcd (fun i => t i - t i0) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hz := (Finset.gcd_eq_zero_iff.mp hzero) i1 h1
    have hp : 0 < t i1 - t i0 := Nat.sub_pos_of_lt hlt
    omega
  have hfgpos : 0 < Nat.fib (all.gcd (fun i => t i - t i0)) := Nat.fib_pos.mpr hgpos
  obtain ⟨e, he⟩ := finite_column_gcd_normalization tail i1
    (Finset.notMem_erase _ _) (f i1) f
  let z : Fin m → ℤ := Pi.single i0 1
  have hz1 : z i1 = 0 := by simp [z, Pi.single_apply, Ne.symm h01]
  have hzt : ∀ i ∈ tail, z i = 0 := by
    intro i hi
    have hi0 : i ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [z, Pi.single_apply, hi0]
  have hef := he f rfl (fun _ _ => rfl)
  have heplus := he (f + z) (by simp [hz1]) (by intro i hi; simp [hzt i hi])
  have hez : e z = z := by
    have hsum : e (f + z) = e f + z := by
      rw [heplus, hef]
      ext i
      by_cases h : i = i1
      · subst i; simp [hz1]
      by_cases hi : i ∈ tail
      · simp [h, hi, hzt i hi]
      simp [h, hi]
    rw [map_add] at hsum
    exact add_left_cancel hsum
  have hg : Nat.gcd (f i1).natAbs (tail.gcd (fun i => (f i).natAbs)) =
      Nat.fib (all.gcd (fun i => t i - t i0)) := by
    have hg1 : Nat.gcd (f i1).natAbs (tail.gcd (fun i => (f i).natAbs)) =
        all.gcd (fun i => (f i).natAbs) := by
      simpa only [tail, Finset.insert_erase h1, gcd_eq_nat_gcd] using
        (Finset.gcd_insert (s := all.erase i1) (f := fun i => (f i).natAbs) (b := i1)).symm
    rw [hg1]
    simp only [f, s, Int.natAbs_natCast]
    simpa only [Finset.gcd, Nat.fib_zero] using
      (Finset.fold_hom (op := GCDMonoid.gcd) (op' := GCDMonoid.gcd)
        (s := all) (b := 0) (f := fun i => t i - t i0) (m := Nat.fib)
        (fun x y => Nat.fib_gcd x y))
  have henf : e f = Pi.single i1 (Nat.fib (all.gcd (fun i => t i - t i0)) : ℤ) := by
    rw [hef, hg]
    ext i
    by_cases hi : i = i1
    · subst i; simp [Pi.single_apply]
    by_cases ht : i ∈ tail
    · simp [hi, ht, Pi.single_apply]
    have hi0 : i = i0 := by
      by_contra hn
      exact ht (by simp [tail, all, hi, hn])
    subst i
    simp [hi, ht, hf0, Pi.single_apply]
  let E := clear.trans e
  let U : (Matrix (Fin m) (Fin m) ℤ)ˣ :=
    { val := E.toLinearMap.toMatrix'
      inv := E.symm.toLinearMap.toMatrix'
      val_inv := by rw [← LinearMap.toMatrix'_comp]; simp
      inv_val := by rw [← LinearMap.toMatrix'_comp]; simp }
  let Q : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
  let AU := Matrix.nonsingInvUnit A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  let QU := Matrix.nonsingInvUnit Q (by simp [Q, Matrix.det_fin_two_of])
  have hnormal : ∃ (U : (Matrix (Fin m) (Fin m) ℤ)ˣ)
      (V : (Matrix (Fin 2) (Fin 2) ℤ)ˣ),
      (U : Matrix (Fin m) (Fin m) ℤ) * H *
        (V : Matrix (Fin 2) (Fin 2) ℤ) =
        (fun i j => if i.val = 0 ∧ j = 0 then 1
          else if i.val = 1 ∧ j = 1 then (Nat.fib (all.gcd (fun i => t i - t i0)) : ℤ)
          else 0) := by
    refine ⟨U, AU⁻¹ * QU, ?_⟩
    change (U : Matrix (Fin m) (Fin m) ℤ) * H * (A⁻¹ * Q) = _
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (U : Matrix (Fin m) (Fin m) ℤ) H A⁻¹, hundo]
    have hBQ : B * Q = fun i => ![q i, f i] := by
      ext i j
      fin_cases j
      · change f i * 0 + q i * 1 = q i
        ring
      · change f i * 1 + q i * 0 = f i
        ring
    rw [Matrix.mul_assoc, hBQ]
    ext i j
    fin_cases j
    · change (E.toLinearMap.toMatrix' *ᵥ q) i = _
      rw [LinearMap.toMatrix'_mulVec]
      change e (clear q) i = _
      rw [hcq, hez]
      simp [z, Pi.single_apply, i0, i1, Fin.ext_iff]
    · change (E.toLinearMap.toMatrix' *ᵥ f) i = _
      rw [LinearMap.toMatrix'_mulVec]
      change e (clear f) i = _
      rw [hcf, henf]
      simp [Pi.single_apply, i0, i1, all, Fin.ext_iff]
  obtain ⟨U, V, hUV⟩ := hnormal
  refine ⟨hfgpos, U, V, hUV, ?_⟩
  intro N hN
  letI : NeZero N := ⟨by omega⟩
  let d := Nat.fib (all.gcd (fun i => t i - t i0))
  let φ := Int.castRingHom (ZMod N)
  let A_mod := H.map φ
  let u := Units.map (RingHom.mapMatrix φ).toMonoidHom U
  let v := Units.map (RingHom.mapMatrix φ).toMonoidHom V
  let D_mod : Matrix (Fin m) (Fin 2) (ZMod N) := fun i j =>
    if i.val = 0 ∧ j = 0 then 1 else if i.val = 1 ∧ j = 1 then (d : ZMod N) else 0
  have hd : (u : Matrix (Fin m) (Fin m) (ZMod N)) * A_mod *
      (v : Matrix (Fin 2) (Fin 2) (ZMod N)) = D_mod := by
    have h := congrArg (fun M : Matrix (Fin m) (Fin 2) ℤ => M.map φ) hUV
    rw [Matrix.map_mul, Matrix.map_mul] at h
    change (U : Matrix (Fin m) (Fin m) ℤ).map φ * H.map φ *
      (V : Matrix (Fin 2) (Fin 2) ℤ).map φ = D_mod
    apply Eq.trans h
    ext i j
    dsimp [D_mod, Matrix.map]
    split_ifs <;> simp [φ, d]
  have invV (x : Fin 2 → ZMod N) :
      (v : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ
        ((↑v⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have vInv (x : Fin 2 → ZMod N) :
      (↑v⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ
        ((v : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hker (x : Fin 2 → ZMod N) :
      A_mod *ᵥ ((v : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ x) = 0 ↔
      D_mod *ᵥ x = 0 := by
    rw [← hd, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro h; rw [h, Matrix.mulVec_zero]
    · intro h
      apply Matrix.mulVec_injective_of_isUnit u.isUnit
      simpa only [Matrix.mulVec_zero] using h
  have hD (x : Fin 2 → ZMod N) : D_mod *ᵥ x = 0 ↔
      x 0 = 0 ∧ (d : ZMod N) * x 1 = 0 := by
    constructor
    · intro h
      constructor
      · have h0 := congrFun h i0
        simpa [D_mod, i0, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
      · have h1 := congrFun h i1
        simpa [D_mod, i1, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h1
    · rintro ⟨h0, h1⟩
      ext i
      by_cases hi0 : i.val = 0
      · simp [D_mod, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hi0, h0]
      by_cases hi1 : i.val = 1
      · simp [D_mod, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hi0, hi1, h1]
      simp [D_mod, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hi0, hi1]
  let K := (nsmulAddMonoidHom d : ZMod N →+ ZMod N).ker
  let eH : A_mod.mulVecLin.ker ≃ D_mod.mulVecLin.ker :=
    { toFun := fun x => ⟨(↑v⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ x,
        (hker _).mp (by rw [invV]; exact x.property)⟩
      invFun := fun x => ⟨(v : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ x,
        (hker _).mpr x.property⟩
      left_inv := by intro x; apply Subtype.ext; exact invV x
      right_inv := by intro x; apply Subtype.ext; exact vInv x }
  let eD : D_mod.mulVecLin.ker ≃ K :=
    { toFun := fun x => ⟨x.val 1, by
        change d • x.val 1 = 0
        simpa [nsmul_eq_mul] using ((hD x.val).mp x.property).2⟩
      invFun := fun x => ⟨![0, x.val], by
        apply (hD _).mpr
        constructor
        · rfl
        · change (d : ZMod N) * x.val = 0
          have hx : d • x.val = 0 := x.property
          simpa only [nsmul_eq_mul] using hx⟩
      left_inv := by
        intro x
        apply Subtype.ext
        ext j
        fin_cases j
        · simpa using ((hD x.val).mp x.property).1.symm
        · rfl
      right_inv := by intro x; rfl }
  have hc : Nat.card A_mod.mulVecLin.ker = Nat.gcd N d := by
    calc
      Nat.card A_mod.mulVecLin.ker = Nat.card K := Nat.card_congr (eH.trans eD)
      _ = Nat.gcd N d := by
        simpa only [Nat.card_eq_fintype_card, ZMod.card] using
          IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod N) d
  refine ⟨hc, ?_⟩
  rw [← hc]
  constructor
  · intro hinj
    have hbot : A_mod.mulVecLin.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
    rw [hbot]
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  · intro hcard
    have hs := (Nat.card_eq_one_iff_unique.mp hcard).1
    change Function.Injective A_mod.mulVecLin
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    exact congrArg Subtype.val (hs.elim (⟨x, hx⟩ : A_mod.mulVecLin.ker) 0)

#print axioms finite_sampling_smith_defect

end D5.S1.Recurrence.FiniteSamplingSmithDefect
