/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedPairMobius
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedPairMobius
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All divided mode-one conjugation coefficients of the native mixed Leech pair. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWard
import D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder

/-! The all-order mode-one coefficient law for the native mixed Leech pair.
The first input is homogeneous. The second input is handled by its finite
projected-basis expansion. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairMobius

open ActualLeechHyperbolic (leechData)
open LatticeGeneratingFieldLocality (Carrier)
open LatticeInvolution (minusSpace)
open LatticeHalfFockGradedTrace
  (actualAmbientBasis actualGrade actual_basis_eigenvalue oddWeight)
open LatticeHalfFockParityT (actualParity_preserves_grade)
open LatticeSugawaraCurrents (sugawaraMode gramComplex)
open NativeOddTwistedIntertwiner (Twisted leechUnit)
open NativeOddUpperRightSkew (lowering mixedPairing_lowering_tail)
open NativeFullMixedField (project)
open NativeMixedPairField (mu)
open NativeMixedPairWard (mu_coeff_L1_ward)

open private project_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
open private actualGrade_eigen lowering_pow_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private lowering_eigen from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private c c_step_zero c_step_succ from
  D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder

private abbrev State (s : Bool) := Twisted leechData leechUnit s

private abbrev Mode (s : Bool) := State (!s) →ₗ[ℂ] Carrier leechData

private abbrev V : Module.End ℂ (Carrier leechData) :=
  sugawaraMode leechData (gramComplex leechData)⁻¹ 1

private abbrev T (s : Bool) : Module.End ℂ (State s) :=
  lowering leechData leechUnit s

private def mode (s : Bool) (e : ℤ) : State s →ₗ[ℂ] Mode s :=
  (LinearMap.compRight ℂ (minusSpace leechData).subtype).comp
    ((LinearMap.proj e).comp (HVertexOperator.coeff.comp (mu s)))

private theorem mode_apply (s : Bool) (e : ℤ) (u : State s) (v : State (!s)) :
    mode s e u v = ((mu s u).coeff e v).val := rfl

private abbrev post (s : Bool) : Module.End ℂ (Mode s) :=
  LinearMap.compRight ℂ V

private abbrev pre (s : Bool) : Module.End ℂ (Mode s) :=
  LinearMap.lcomp ℂ (Carrier leechData) (T (!s))

private def ad (s : Bool) : Module.End ℂ (Mode s) :=
  post s - pre s

private def dividedAd (s : Bool) (n : ℕ) (e : ℤ) (u : State s) : Mode s :=
  (n.factorial : ℂ)⁻¹ • (ad s ^ n) (mode s e u)

private abbrev ambientBasis := actualAmbientBasis leechData leechUnit

private theorem projected_basis_grade (s : Bool) (i : _) :
    (project s (ambientBasis i)).val ∈
      actualGrade leechData leechUnit (oddWeight leechData i.1) := by
  have hi : ambientBasis i ∈ actualGrade leechData leechUnit (oddWeight leechData i.1) := by
    apply (actualGrade_eigen leechData leechUnit _ _).mpr
    simpa only [Prod.eta] using actual_basis_eigenvalue leechData leechUnit i.1 i.2
  rw [project_val]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hi (Submodule.smul_mem _ _
    (actualParity_preserves_grade leechData leechUnit _ _ hi)))

private theorem ward (s : Bool) (M : ℕ) (e : ℤ) (u : State s)
    (hu : u.val ∈ actualGrade leechData leechUnit M) :
    ad s (mode s e u) =
      mode s e (T s u) + (3 + (M : ℂ) + (e : ℂ)/2 - 1) • mode s (e-2) u := by
  classical
  let F : Mode s := ad s (mode s e u)
  let G : Mode s := mode s e (T s u) +
    (3 + (M : ℂ) + (e : ℂ)/2 - 1) • mode s (e-2) u
  change F = G
  apply LinearMap.ext
  intro v
  have onBasis (i : _) :
      F (project (!s) (ambientBasis i)) = G (project (!s) (ambientBasis i)) := by
    let w := project (!s) (ambientBasis i)
    have law : V (mode s e u w) = mode s e (T s u) w +
        mode s e u (T (!s) w) + (3 + (M : ℂ) + (e : ℂ)/2 - 1) • mode s (e-2) u w := by
      simpa only [mode_apply] using
        (mu_coeff_L1_ward s M (oddWeight leechData i.1) e u w hu
          (projected_basis_grade (!s) i))
    change V (mode s e u w) - mode s e u (T (!s) w) =
      mode s e (T s u) w + (3 + (M : ℂ) + (e : ℂ)/2 - 1) • mode s (e-2) u w
    rw [sub_eq_iff_eq_add, law]
    abel
  have decomp := sum_projectedBasis (!s) v
  have hF := congrArg (fun w : State (!s) => F w) decomp
  have hG := congrArg (fun w : State (!s) => G w) decomp
  change F v = G v
  rw [← hF, ← hG]
  simp only [map_sum, map_smul, onBasis]

private theorem power_grade (s : Bool) (M k : ℕ) (u : State s)
    (hu : u.val ∈ actualGrade leechData leechUnit M) (hk : 2 * k ≤ M) :
    ((T s ^ k) u).val ∈ actualGrade leechData leechUnit (M-2*k) := by
  apply (actualGrade_eigen leechData leechUnit _ _).mpr
  simp only [T, lowering_pow_val]
  have he := lowering_eigen leechData leechUnit (M : ℤ) u.val
    (by simpa only [Int.cast_natCast] using
      (actualGrade_eigen leechData leechUnit M u.val).mp hu) k
  rwa [show (M : ℤ) - 2*(k : ℤ) = ((M-2*k : ℕ) : ℤ) by omega, Int.cast_natCast] at he

private theorem dividedAd_step (s : Bool) (n : ℕ) (e : ℤ) (u : State s) :
    (n+1 : ℂ) • dividedAd s (n+1) e u = ad s (dividedAd s n e u) := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hs : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [dividedAd, map_smul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, smul_smul, pow_succ', Module.End.mul_apply]
  congr 1
  field_simp

private theorem sum_step (s : Bool) (α : ℂ) (n : ℕ) (F : ℕ → Mode s) :
    (n + 1 : ℂ) • (∑ k ∈ Finset.range (n + 2), c α (n + 1) k • F k) =
      (∑ k ∈ Finset.range (n + 1), c α n k • F (k + 1)) +
      ∑ k ∈ Finset.range (n + 1), (c α n k * (α - (n : ℂ) - (k : ℂ))) • F k := by
  let g (k : ℕ) := (c α n k * (α - (n : ℂ) - (k : ℂ))) • F k
  have top : g (n + 1) = 0 := by simp [g, c]
  have shift : (∑ k ∈ Finset.range (n + 1), g (k + 1)) + g 0 =
      ∑ k ∈ Finset.range (n + 1), g k := by
    rw [← Finset.sum_range_succ', Finset.sum_range_succ, top, add_zero]
  calc
    _ = (∑ k ∈ Finset.range (n + 1),
          ((n + 1 : ℂ) * c α (n + 1) (k + 1)) • F (k + 1)) +
        ((n + 1 : ℂ) * c α (n + 1) 0) • F 0 := by
      rw [Finset.smul_sum, Finset.sum_range_succ']
      simp only [smul_smul]
    _ = (∑ k ∈ Finset.range (n + 1), (c α n k • F (k + 1) + g (k + 1))) + g 0 := by
      rw [c_step_zero]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        rw [c_step_succ α n k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)), add_smul]
        simp only [g, Nat.cast_add, Nat.cast_one, mul_comm]
      · simp [g, mul_comm]
    _ = _ := by rw [Finset.sum_add_distrib, add_assoc, shift]

private theorem dividedAd_homogeneous (s : Bool) (M : ℕ) (e : ℤ) (u : State s)
    (hu : u.val ∈ actualGrade leechData leechUnit M) (n : ℕ) :
    dividedAd s n e u =
      ∑ k ∈ Finset.range (n+1), c (3+(M:ℂ)+(e:ℂ)/2-1) n k •
        mode s (e-2*(n:ℤ)+2*(k:ℤ)) ((T s ^ k) u) := by
  let α : ℂ := 3+(M:ℂ)+(e:ℂ)/2-1
  change dividedAd s n e u =
    ∑ k ∈ Finset.range (n+1), c α n k •
      mode s (e-2*(n:ℤ)+2*(k:ℤ)) ((T s ^ k) u)
  induction n with
  | zero => simp [dividedAd, c]
  | succ n ih =>
    let F := fun k : ℕ => mode s (e-2*((n+1:ℕ):ℤ)+2*(k:ℤ)) ((T s ^ k) u)
    have mode_step (k : ℕ) :
        ad s (mode s (e-2*(n:ℤ)+2*(k:ℤ)) ((T s ^ k) u)) =
          F (k+1) + (α-(n:ℂ)-(k:ℂ)) • F k := by
      have first : F (k+1) = mode s (e-2*(n:ℤ)+2*(k:ℤ)) (T s ((T s ^ k) u)) := by
        dsimp only [F]
        rw [show e-2*((n+1:ℕ):ℤ)+2*((k+1:ℕ):ℤ) = e-2*(n:ℤ)+2*(k:ℤ) by omega,
          pow_succ' (T s), Module.End.mul_apply]
      have second : e-2*(n:ℤ)+2*(k:ℤ)-2 = e-2*((n+1:ℕ):ℤ)+2*(k:ℤ) := by omega
      by_cases hk : 2*k ≤ M
      · have law := ward s (M-2*k) (e-2*(n:ℤ)+2*(k:ℤ)) ((T s ^ k) u)
          (power_grade s M k u hu hk)
        have scalar : 3 + ((M-2*k : ℕ) : ℂ) + ((e-2*(n:ℤ)+2*(k:ℤ) : ℤ) : ℂ)/2 - 1 =
            α-(n:ℂ)-(k:ℂ) := by
          rw [Nat.cast_sub hk]
          dsimp only [α]
          push_cast
          ring
        rw [scalar, second, ← first] at law
        exact law
      · have hz : (T s ^ k) u = 0 :=
          mixedPairing_lowering_tail s M u hu k (by omega)
        rw [first]
        simp only [F, hz, map_zero, smul_zero, zero_add]
    apply smul_right_injective (Mode s)
      (show (n+1:ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
    change (n+1:ℂ) • dividedAd s (n+1) e u =
      (n+1:ℂ) • ∑ k ∈ Finset.range (n+2), c α (n+1) k • F k
    rw [dividedAd_step s n e u, ih, map_sum]
    simp only [map_smul]
    calc
      _ = ∑ k ∈ Finset.range (n+1), c α n k •
            (F (k+1) + (α-(n:ℂ)-(k:ℂ)) • F k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [mode_step]
      _ = (∑ k ∈ Finset.range (n+1), c α n k • F (k+1)) +
            ∑ k ∈ Finset.range (n+1), (c α n k*(α-(n:ℂ)-(k:ℂ))) • F k := by
        simp only [smul_add, smul_smul, Finset.sum_add_distrib]
      _ = _ := (sum_step s α n F).symm

private theorem post_pow_apply (s : Bool) (j : ℕ) (f : Mode s) (v : State (!s)) :
    (post s ^ j) f v = (V ^ j) (f v) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ' (post s), Module.End.mul_apply]
    change V ((post s ^ j) f v) = _
    rw [ih, pow_succ' V, Module.End.mul_apply]

private theorem pre_pow_apply (s : Bool) (j : ℕ) (f : Mode s) (v : State (!s)) :
    (pre s ^ j) f v = f ((T (!s) ^ j) v) := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ' (pre s), Module.End.mul_apply]
    change (pre s ^ j) f (T (!s) v) = _
    rw [ih, pow_succ (T (!s)), Module.End.mul_apply]

private theorem dividedAd_eq_sum (s : Bool) (n : ℕ) (e : ℤ) (u : State s) :
    dividedAd s n e u =
      ∑ i ∈ Finset.range (n+1),
        ((-1:ℂ)^(n-i) / ((i.factorial:ℂ) * ((n-i).factorial:ℂ))) •
          (V ^ i).comp ((mode s e u).comp (T (!s) ^ (n-i))) := by
  have comm : Commute (post s) (pre s) := by
    rw [commute_iff_eq]
    exact LinearMap.ext₂ fun f v => rfl
  have expansion := comm.neg_right.add_pow n
  have term (i : ℕ) :
      (post s ^ i * (-pre s) ^ (n-i) *
        (n.choose i : Module.End ℂ (Mode s))) (mode s e u) =
      ((n.choose i:ℂ) * (-1:ℂ)^(n-i)) •
        (V ^ i).comp ((mode s e u).comp (T (!s) ^ (n-i))) := by
    apply LinearMap.ext
    intro v
    rw [show -(pre s) = (-1:ℂ) • pre s from (neg_one_smul ℂ _).symm]
    simp only [smul_pow, Module.End.mul_apply, Module.End.natCast_apply,
      ← Nat.cast_smul_eq_nsmul ℂ, map_smul, LinearMap.smul_apply,
      post_pow_apply, pre_pow_apply, LinearMap.comp_apply, smul_smul] <;> module
  change (n.factorial:ℂ)⁻¹ • (ad s ^ n) (mode s e u) = _
  rw [ad, sub_eq_add_neg, expansion, LinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [term, smul_smul, Nat.cast_choose ℂ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  congr 1
  have hn : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

/-- Every divided mode-one conjugation coefficient of the native mixed Leech
pair. The first state has oscillator degree `M` and doubled weight `3 + M`.
The coefficient identity holds for either input order, any second state,
and every integer doubled exponent. -/
theorem mu_coeff_L1_mobius (s : Bool) (M n : ℕ) (e : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M) :
    (∑ i ∈ Finset.range (n+1),
      ((-1:ℂ)^(n-i) / ((i.factorial:ℂ) * ((n-i).factorial:ℂ))) •
        (sugawaraMode leechData (gramComplex leechData)⁻¹ 1 ^ i)
          ((mu s u).coeff e ((lowering leechData leechUnit (!s) ^ (n-i)) v)).val) =
    ∑ k ∈ Finset.range (n+1),
      (Ring.choose (3+(M:ℂ)+(e:ℂ)/2-(k:ℂ)-1) (n-k) / (k.factorial:ℂ)) •
        ((mu s ((lowering leechData leechUnit s ^ k) u)).coeff (e-2*(n:ℤ)+2*(k:ℤ)) v).val := by
  have closed : dividedAd s n e u =
      ∑ k ∈ Finset.range (n+1),
        (Ring.choose (3+(M:ℂ)+(e:ℂ)/2-(k:ℂ)-1) (n-k) / (k.factorial:ℂ)) •
          mode s (e-2*(n:ℤ)+2*(k:ℤ)) ((T s ^ k) u) := by
    rw [dividedAd_homogeneous s M e u hu n]
    apply Finset.sum_congr rfl
    intro k hk
    rw [c, ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    have h : 3+(M:ℂ)+(e:ℂ)/2-1-(k:ℂ) = 3+(M:ℂ)+(e:ℂ)/2-(k:ℂ)-1 := by ring
    rw [h]
  have h := LinearMap.congr_fun ((dividedAd_eq_sum s n e u).symm.trans closed) v
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, mode_apply] using h

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairMobius
