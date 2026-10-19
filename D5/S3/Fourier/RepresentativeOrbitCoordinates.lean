/- GID: D5/S3/Fourier/RepresentativeOrbitCoordinates
   generality: G
   mirror-B: D5/B/S3/Fourier/RepresentativeOrbitCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary Fourier coordinates realize the dependent product of actual doubling-orbit fields. -/

import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

open scoped BigOperators
open Function
namespace D5.S3.Fourier.RepresentativeOrbitCoordinates
set_option maxHeartbeats 1200000

/-- Binary Fourier coordinates at arbitrary representatives of all doubling orbits. -/
theorem representative_fourier_coordinates
    (n d : ℕ) (hn : 3 ≤ n) (ho : Odd n) (_hd : 1 ≤ d)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (ζ : F) (hζ : IsPrimitiveRoot ζ n) :
    let : NeZero n := ⟨by omega⟩
    let : Algebra (ZMod 2) F := ZMod.algebra F 2
    let G := Fin d → ZMod n
    let p : Equiv.Perm G := Equiv.piCongrRight
      (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
    let O := Quotient (Equiv.Perm.SameCycle.setoid p)
    ∀ sec : O → G, (∀ q, Quotient.mk (Equiv.Perm.SameCycle.setoid p) (sec q) = q) →
    ∃ e : (G → ZMod 2) ≃ₗ[ZMod 2]
        ((q : O) → IntermediateField.adjoin (ZMod 2)
          (Set.range (fun j : Fin d => ζ ^ (sec q j).val))),
      ∀ a q, (e a q : F) =
        ∑ r : G, algebraMap (ZMod 2) F (a r) *
          ∏ j : Fin d, ζ ^ (sec q j * r j).val := by
  classical
  let : NeZero n := ⟨by omega⟩
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let G := Fin d → ZMod n
  let p : Equiv.Perm G := Equiv.piCongrRight
    (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
  let O := Quotient (Equiv.Perm.SameCycle.setoid p)
  let qof : G → O := Quotient.mk (Equiv.Perm.SameCycle.setoid p)
  dsimp only
  intro sec hsec
  let K (t : G) := IntermediateField.adjoin (ZMod 2)
    (Set.range (fun j : Fin d => ζ ^ (t j).val))
  let ψ := AddChar.zmodChar n hζ.pow_eq_one
  let χ (t r : G) : F := ψ (∑ j, t j * r j)
  let T (a : G → ZMod 2) (t : G) : F := ∑ r, algebraMap (ZMod 2) F (a r) * χ t r
  let U (Y : G → F) (r : G) : F := ∑ t, Y t * χ (-t) r
  let g : F → F := frobenius F 2
  have hp (t : G) : p t = fun j => (2 : ZMod n) * t j := by
    funext j
    simp [p, Equiv.piCongrRight, Units.mulLeft, ZMod.coe_unitOfCoprime]
  have hpiter (t : G) (m : ℕ) : (p : G → G)^[m] t = fun j => (2 : ZMod n)^m * t j := by
    have he : (p : G → G) = fun x : G => (fun _ => (2 : ZMod n)) * x := funext hp
    rw [he, mul_left_iterate_apply]
    rfl
  have hpow (b : ZMod n) (m : ℕ) : ψ ((2 : ZMod n)^m * b) = (ψ b)^(2^m) := by
    rw [← ψ.map_nsmul_eq_pow]
    congr 1
    simp [nsmul_eq_mul]
  have hprod (t r : G) : χ t r = ∏ j : Fin d, ζ ^ (t j * r j).val := by
    exact congrArg Additive.toMul (map_sum ψ.toAddMonoidHom
      (fun j : Fin d => t j * r j) Finset.univ) |>.trans (toMul_sum _ _)
  have hχadd (t s r : G) : χ (t+s) r = χ t r * χ s r := by
    change ψ (∑ j, (t j+s j)*r j) = _
    simp only [add_mul, Finset.sum_add_distrib]
    exact ψ.map_add_eq_mul _ _
  have hχsym (t r : G) : χ t r = χ r t := by
    simp only [χ, mul_comm]
  have hχsq (t r : G) : χ (p t) r = (χ t r)^2 := by
    rw [hp]
    change ψ (∑ j, (2 * t j) * r j) = _
    have hh : (∑ j, (2 * t j) * r j) = 2 * (∑ j, t j * r j) := by
      simp [Finset.mul_sum, mul_assoc]
    rw [hh]
    simpa using hpow (∑ j, t j*r j) 1
  have hpn (t : G) : p (-t) = -(p t) := by
    rw [hp, hp]
    funext j
    change (2 : ZMod n) * -(t j) = -(2*t j)
    exact mul_neg _ _
  have hnF : (n : F) = 1 := natCast_eq_one_of_odd_of_two_eq_zero ho CharTwo.two_eq_zero
  have horth (w : G) : (∑ r : G, χ w r) = if w=0 then 1 else 0 := by
    simp_rw [hprod]
    rw [← Fintype.prod_sum (fun j (a : ZMod n) => ζ ^ (w j*a).val)]
    have hs (j : Fin d) : (∑ a : ZMod n, ζ ^ (w j*a).val) = if w j=0 then (1:F) else 0 := by
      have h := AddChar.sum_mulShift (ψ := ψ) (w j)
        (AddChar.zmodChar_primitive_of_primitive_root n hζ)
      simpa (config := { congrConsts := false })
        [ψ, AddChar.zmodChar_apply, mul_comm, ZMod.card, hnF] using h
    simp_rw [hs]
    by_cases hw : w=0
    · simp [hw, G]
    · rw [if_neg hw]
      obtain ⟨j,hj⟩ : ∃ j, w j ≠ 0 := not_forall.mp (fun h => hw (funext h))
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  have hleft (a : G → ZMod 2) (r : G) : U (T a) r = algebraMap (ZMod 2) F (a r) := by
    simp only [U, T, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      (∑ s : G, ∑ t : G, (algebraMap (ZMod 2) F (a s)*χ t s)*χ (-t) r) =
          ∑ s : G, algebraMap (ZMod 2) F (a s) * (∑ t : G, χ (s-r) t) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        have hneg : χ (-t) r = χ (-r) t := by
          change ψ (∑ j, (-t) j*r j)=ψ (∑ j, (-r) j*t j)
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          change -(t j)*r j = -(r j)*t j
          ring
        rw [mul_assoc, hχsym t s, hneg, ← hχadd]
        congr 2
        simp [sub_eq_add_neg]
      _ = algebraMap (ZMod 2) F (a r) := by simp [horth, sub_eq_zero, G]
  have hright (Y : G → F) (t : G) : (∑ r : G, U Y r * χ t r) = Y t := by
    simp only [U, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      (∑ s : G, ∑ r : G, (Y s*χ (-s) r)*χ t r) =
          ∑ s : G, Y s * (∑ r : G, χ (t-s) r) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [mul_assoc, ← hχadd]
        congr 2
        simp [sub_eq_add_neg, add_comm]
      _ = Y t := by simp [horth, sub_eq_zero, G]
  have hbin (b : ZMod 2) : g (algebraMap (ZMod 2) F b) = algebraMap (ZMod 2) F b := by
    change (algebraMap (ZMod 2) F b)^2 = _
    rw [← map_pow, ZMod.pow_card]
  have hTcomp (a : G → ZMod 2) : ∀ t, T a (p t) = g (T a t) := by
    intro t
    simp only [T, g, map_sum, map_mul, frobenius_def]
    apply Finset.sum_congr rfl
    intro r _
    rw [hχsq]
    congr 1
    exact (hbin (a r)).symm
  have hbinary_inverse (Y : G → F) (hY : ∀ t, Y (p t)=g (Y t)) : ∃ a, T a=Y := by
    have hfix (r : G) : (U Y r)^2 = U Y r := by
      change g (U Y r) = U Y r
      simp only [U, g, map_sum, map_mul, frobenius_def]
      have hh (t : G) : (Y t)^2 * (χ (-t) r)^2 = Y (p t)*χ (-(p t)) r := by
        rw [hY, ← hχsq, hpn]
        rfl
      simp_rw [hh]
      exact (Fintype.sum_equiv p (fun t => Y (p t)*χ (-(p t)) r)
        (fun t => Y t*χ (-t) r) (fun _ => rfl))
    have hb (r : G) : ∃ b : ZMod 2, algebraMap (ZMod 2) F b = U Y r := by
      rcases eq_zero_or_one_of_sq_eq_self (hfix r) with h|h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
    choose a ha using hb
    refine ⟨a, funext (fun t => ?_)⟩
    simpa only [T, ha] using hright Y t
  have hmem (a : G → ZMod 2) (t : G) : T a t ∈ K t := by
    apply IntermediateField.sum_mem
    intro r _
    apply IntermediateField.mul_mem
    · exact IntermediateField.algebraMap_mem _ _
    · rw [hprod]
      apply IntermediateField.prod_mem
      intro j _
      have he : ψ (t j * r j) = (ψ (t j))^(r j).val := by
        rw [← ψ.map_nsmul_eq_pow]
        congr 1
        simp [nsmul_eq_mul, mul_comm]
      change ψ (t j * r j) ∈ K t
      rw [he]
      simpa (config := { congrConsts := false }) only [ψ, AddChar.zmodChar_apply] using
        _root_.pow_mem (IntermediateField.subset_adjoin (ZMod 2)
          (Set.range (fun j : Fin d => ζ ^ (t j).val)) ⟨j,rfl⟩) (r j).val
  have hkpos (t : G) : 0 < minimalPeriod (p : G → G) t :=
    minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts t)
  have hperiod (q : O) (x : K (sec q)) :
      IsPeriodicPt g (minimalPeriod (p : G → G) (sec q)) (x : F) := by
    let k := minimalPeriod (p : G → G) (sec q)
    let φ := iterateFrobenius F 2 k
    have heφ : (φ : F → F) = g^[k] := (coe_iterateFrobenius F 2 k)
    change g^[k] (x : F) = (x : F)
    rw [← heφ]
    refine IntermediateField.adjoin_induction (F := ZMod 2)
      (motive := fun y _ => φ y=y) ?_ ?_ ?_ ?_ ?_ x.property
    · rintro y ⟨j,rfl⟩
      have hh := congrFun (iterate_minimalPeriod (f := (p : G → G)) (x := sec q)) j
      rw [hpiter] at hh
      change (2 : ZMod n)^k * sec q j = sec q j at hh
      change (ζ ^ (sec q j).val)^(2^k) = _
      calc
        _ = ψ ((2 : ZMod n)^k * sec q j) := (hpow _ k).symm
        _ = ζ ^ (sec q j).val := by rw [hh]; rfl
    · intro b
      rw [heφ]
      exact iterate_fixed (hbin b) k
    · intro y z hy hz ey ez
      rw [map_add, ey, ez]
    · intro y hy ey
      rw [map_inv₀, ey]
    · intro y z hy hz ey ez
      rw [map_mul, ey, ez]
  have hqiter (t : G) (i : ℕ) : qof ((p : G → G)^[i] t) = qof t := by
    apply Quotient.sound
    change p.SameCycle ((p^i) t) t
    exact (Equiv.Perm.SameCycle.refl p t).pow_left
  have hreach (t : G) : ∃ i : ℕ, (p : G → G)^[i] (sec (qof t)) = t := by
    have hc : p.SameCycle (sec (qof t)) t := Quotient.exact (hsec (qof t))
    obtain ⟨i,hi⟩ := hc.exists_nat_pow_eq
    exact ⟨i,hi⟩
  let pos (t : G) := (hreach t).choose
  have hpos (t : G) : (p : G → G)^[pos t] (sec (qof t)) = t := (hreach t).choose_spec
  have hext (a : (q : O) → K (sec q)) :
      ∃ Y : G → F, (∀ t, Y (p t)=g (Y t)) ∧ ∀ q, Y (sec q)=(a q : F) := by
    let Y (t : G) : F := g^[pos t] (a (qof t) : F)
    have htransport (q : O) (i : ℕ) : Y ((p : G → G)^[i] (sec q)) = g^[i] (a q : F) := by
      let t := (p : G → G)^[i] (sec q)
      have hqt : qof t=q := (hqiter (sec q) i).trans (hsec q)
      have ht : (p : G → G)^[pos t] (sec q) = (p : G → G)^[i] (sec q) := by
        simpa only [hqt] using hpos t
      let k := minimalPeriod (p : G → G) (sec q)
      have hmod : pos t % k = i % k :=
        (iterate_eq_iterate_iff_of_lt_minimalPeriod
          (Nat.mod_lt _ (hkpos (sec q))) (Nat.mod_lt _ (hkpos (sec q)))).mp
            ((iterate_mod_minimalPeriod_eq).trans (ht.trans (iterate_mod_minimalPeriod_eq).symm))
      change g^[pos t] (a (qof t) : F)=g^[i] (a q : F)
      rw [hqt, ← (hperiod q (a q)).iterate_mod_apply (pos t),
        ← (hperiod q (a q)).iterate_mod_apply i, hmod]
    refine ⟨Y, ?_, ?_⟩
    · intro t
      obtain ⟨i,hi⟩ := hreach t
      rw [← hi, ← iterate_succ_apply' (f := (p : G → G)), htransport, htransport,
        iterate_succ_apply' (f := g)]
    · intro q
      simpa using htransport q 0
  let L : (G → ZMod 2) →ₗ[ZMod 2] ((q : O) → K (sec q)) := {
    toFun := fun a q => ⟨T a (sec q), hmem a (sec q)⟩
    map_add' := by
      intro a b
      funext q
      apply Subtype.ext
      change T (a+b) (sec q) = T a (sec q)+T b (sec q)
      simp only [T, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro c a
      funext q
      apply Subtype.ext
      change (∑ r : G, algebraMap (ZMod 2) F (c * a r) * χ (sec q) r) =
        algebraMap (ZMod 2) F c * (∑ r : G, algebraMap (ZMod 2) F (a r) * χ (sec q) r)
      simp only [map_mul, Finset.mul_sum, mul_assoc] }
  have hinj : Injective L := by
    intro a b hab
    have hsame : T a=T b := by
      funext t
      obtain ⟨i,hi⟩ := hreach t
      have hc : T a (sec (qof t))=T b (sec (qof t)) :=
        congrArg (fun z : (q : O) → K (sec q) => (z (qof t) : F)) hab
      have ha : Semiconj (T a) (p : G → G) g := hTcomp a
      have hb : Semiconj (T b) (p : G → G) g := hTcomp b
      rw [← hi, ha.iterate_right i, hb.iterate_right i, hc]
    funext r
    apply (algebraMap (ZMod 2) F).injective
    rw [← hleft a r, ← hleft b r, hsame]
  have hsurj : Surjective L := by
    intro a
    obtain ⟨Y,hY,hYa⟩ := hext a
    obtain ⟨b,hb⟩ := hbinary_inverse Y hY
    refine ⟨b, ?_⟩
    funext q
    apply Subtype.ext
    change T b (sec q)=(a q : F)
    rw [hb, hYa]
  refine ⟨LinearEquiv.ofBijective L ⟨hinj,hsurj⟩, ?_⟩
  intro a q
  change T a (sec q) = _
  simp only [T, hprod, G]

end D5.S3.Fourier.RepresentativeOrbitCoordinates
