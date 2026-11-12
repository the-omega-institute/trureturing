/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthExpansion
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth moments under a quadratic relation expand by index multiplicity. -/

/-
proof_shape: sum_two: bind-only (consumer: SixthOrderTopPairingRefutation).
escape_witness: none; this delivery changes visibility only, with no new proof
  content. The existing two-index sum identity is reused across modules.
admission_basis: consumed-helper reuse.
-/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.IndexEqualityPatterns
import D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection
import D5.S3.Zeros.LeeYang.TreePairStability

/-! Fourth moments are evaluated by the five index-multiplicity types. -/

open scoped BigOperators
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing A] [Algebra ℝ A]

lemma sum_two (F : ι → ι → ℝ) :
    (∑ x : Fin 2 → ι with Function.Injective x, F (x 0) (x 1)) =
      ∑ d, ∑ e with d ≠ e, F d e := by
  simp only [Finset.sum_filter]
  rw [D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection.sum_fin_cons]
  simp_rw [D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection.sum_fin_cons]
  simp [Function.injective_iff_pairwise_ne, Pairwise, Function.onFun, Fin.forall_fin_succ, ne_comm]

private lemma sum_three (F : ι → ι → ι → ℝ) :
    (∑ x : Fin 3 → ι with Function.Injective x, F (x 0) (x 1) (x 2)) =
      ∑ d, ∑ e, ∑ g with d ≠ e ∧ d ≠ g ∧ e ≠ g, F d e g := by
  simp only [Finset.sum_filter]
  rw [D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection.sum_fin_cons]
  simp_rw [D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection.sum_fin_cons]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  change (∑ d, ∑ e, ∑ t, if Function.Injective ![d,e,t] then F d e t else 0) = _
  have hi (d e t : ι) : Function.Injective ![d,e,t] ↔
      d ≠ e ∧ d ≠ t ∧ e ≠ t := by
    simp [Function.injective_iff_pairwise_ne, Pairwise, Function.onFun,
      Fin.forall_fin_succ, ne_comm, and_assoc]; tauto
  simp_rw [hi]

private lemma excluded_sum (f : ι → ℝ) (e g : ι) (heg : e ≠ g) :
    (∑ d with d ≠ e ∧ d ≠ g, f d) = indexSum f - f e - f g := by
  have h := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun d => d ≠ e ∧ d ≠ g) (f := f)
  have he : (∑ d : ι with ¬(d ≠ e ∧ d ≠ g), f d) = f e + f g := by
    rw [show Finset.univ.filter (fun d : ι => ¬(d ≠ e ∧ d ≠ g)) = {e,g} by
      ext d; simp; tauto]
    simp [heg]
  rw [he] at h
  dsimp [indexSum]
  linarith

private lemma distinctIndexMoment_two (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f g : ι → ℝ) :
    distinctIndexMoment ℓ Y ![f,g] = ∑ d, ∑ e with d ≠ e, f d * g e * ℓ (Y d * Y e) := by
  simpa [distinctIndexMoment, Fin.prod_univ_two] using
    sum_two (fun d e => f d * g e * ℓ (Y d * Y e))

private lemma distinctIndexMoment_three (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f g h : ι → ℝ) :
    distinctIndexMoment ℓ Y ![f,g,h] =
      ∑ d, ∑ e, ∑ t with d ≠ e ∧ d ≠ t ∧ e ≠ t,
        f d * g e * h t * ℓ (Y d * Y e * Y t) := by
  simpa [distinctIndexMoment, Fin.prod_univ_three, mul_assoc] using
    sum_three (fun d e t => f d * g e * h t * ℓ (Y d * Y e * Y t))

private lemma excluded_moment (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A)
    (f g h : ι → ℝ) :
    (∑ d, ∑ e, ∑ t with d ≠ e ∧ d ≠ t ∧ e ≠ t,
      f d * g e * h t * ℓ (Y e * Y t)) =
    indexSum f * distinctIndexMoment ℓ Y ![g,h] - distinctIndexMoment ℓ Y ![f*g,h] - distinctIndexMoment ℓ Y ![f*h,g] := by
  rw [distinctIndexMoment_pair_comm ℓ Y (f*h) g]
  simp only [distinctIndexMoment_two, Pi.mul_apply, Finset.sum_filter]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext e; rw [Finset.sum_comm]
  have he (e t : ι) :
      (∑ d, if d ≠ e ∧ d ≠ t ∧ e ≠ t then
        f d * g e * h t * ℓ (Y e * Y t) else 0) =
      if e ≠ t then (indexSum f - f e - f t) * (g e * h t * ℓ (Y e * Y t)) else 0 := by
    by_cases het : e = t
    · simp [het]
    · rw [← excluded_sum f e t het]
      simp only [ne_eq, het, not_false_eq_true, and_true, ite_true,
        Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> ring
  simp_rw [he, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> ring

private lemma constant_offdiag (f g : ι → ℝ) :
    (∑ d, ∑ e with d ≠ e, f d * g e) = indexSum f * indexSum g - indexSum (f*g) := by
  simpa [Finset.sum_filter, indexSum, Pi.mul_apply, Fintype.sum_mul_sum] using
    (FiolArbitraryTreePair.sum_off_diagonal (fun d e => f d * g e))

private lemma algebra_scalar (ℓ : A →ₗ[ℝ] ℝ) (c : ℝ) (x : A) :
    ℓ (algebraMap ℝ A c * x) = c * ℓ x := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

private lemma pair_single_single (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (hq : ∀ d, Y d ^ 2 = a • Y d + algebraMap ℝ A b)
    (f g h : ι → ℝ) :
    (∑ x : Fin 3 → ι with Function.Injective x,
      f (x 0) * g (x 1) * h (x 2) * ℓ (Y (x 0)^2 * Y (x 1) * Y (x 2))) =
      a * distinctIndexMoment ℓ Y ![f,g,h] +
      b * (indexSum f * distinctIndexMoment ℓ Y ![g,h] - distinctIndexMoment ℓ Y ![f*g,h] - distinctIndexMoment ℓ Y ![f*h,g]) := by
  rw [sum_three (fun d e t => f d * g e * h t * ℓ (Y d^2 * Y e * Y t)),
    distinctIndexMoment_three, ← excluded_moment ℓ Y f g h]
  simp_rw [hq, Algebra.smul_def, add_mul, map_add ℓ, mul_assoc,
    algebra_scalar, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;>
    apply Finset.sum_congr rfl <;> intro d hd <;>
    apply Finset.sum_congr rfl <;> intro e he <;>
    apply Finset.sum_congr rfl <;> intro t ht <;> ring

private lemma triple_single (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (h0 : ∀ d, ℓ (Y d) = 0)
    (hq : ∀ d, Y d ^ 2 = a • Y d + algebraMap ℝ A b)
    (f g : ι → ℝ) :
    (∑ x : Fin 2 → ι with Function.Injective x,
      f (x 0) * g (x 1) * ℓ (Y (x 0)^3 * Y (x 1))) =
      (a^2+b) * distinctIndexMoment ℓ Y ![f,g] := by
  have hp (d : ι) : Y d ^ 3 =
      algebraMap ℝ A (a^2+b) * Y d + algebraMap ℝ A (a*b) := by
    calc
      _ = Y d ^ 2 * Y d := by ring
      _ = _ := by rw [hq]; simp only [Algebra.smul_def, add_mul];
                  rw [show algebraMap ℝ A a * Y d * Y d =
                    algebraMap ℝ A a * Y d ^ 2 by ring, hq]
                  simp only [Algebra.smul_def, map_add, map_mul, map_pow]; ring
  rw [sum_two (fun d e => f d * g e * ℓ (Y d^3 * Y e)), distinctIndexMoment_two]
  have hv (d e : ι) : ℓ (Y d^3 * Y e) = (a^2+b) * ℓ (Y d * Y e) := by
    rw [hp, add_mul, map_add ℓ]
    simp only [mul_assoc, algebra_scalar, h0, mul_zero, add_zero]
  simp only [hv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  ring

private lemma pair_pair (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (h1 : ℓ 1 = 1) (h0 : ∀ d, ℓ (Y d) = 0)
    (hq : ∀ d, Y d ^ 2 = a • Y d + algebraMap ℝ A b)
    (f g : ι → ℝ) :
    (∑ x : Fin 2 → ι with Function.Injective x,
      f (x 0) * g (x 1) * ℓ (Y (x 0)^2 * Y (x 1)^2)) =
      a^2 * distinctIndexMoment ℓ Y ![f,g] + b^2 * (indexSum f * indexSum g - indexSum (f*g)) := by
  have hp (d e : ι) : Y d ^ 2 * Y e ^ 2 =
      algebraMap ℝ A (a^2) * (Y d * Y e) +
      algebraMap ℝ A (a*b) * Y d + algebraMap ℝ A (a*b) * Y e +
      algebraMap ℝ A (b^2) * 1 := by
    rw [hq, hq]
    simp only [Algebra.smul_def, map_mul, map_pow]
    ring
  have hv (d e : ι) : ℓ (Y d^2 * Y e^2) = a^2 * ℓ (Y d * Y e) + b^2 := by
    rw [hp, map_add ℓ, map_add ℓ, map_add ℓ,
      algebra_scalar, algebra_scalar, algebra_scalar, algebra_scalar, h0, h0, h1]
    ring
  rw [sum_two (fun d e => f d * g e * ℓ (Y d^2 * Y e^2)), distinctIndexMoment_two,
    ← constant_offdiag f g]
  simp only [hv, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro d hd <;>
    apply Finset.sum_congr rfl <;> intro e he <;> ring

omit [DecidableEq ι] in
private lemma quadruple (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (h1 : ℓ 1 = 1) (h0 : ∀ d, ℓ (Y d) = 0)
    (hq : ∀ d, Y d ^ 2 = a • Y d + algebraMap ℝ A b)
    (f : ι → ℝ) : (∑ d, f d * ℓ (Y d^4)) = (a^2*b+b^2) * indexSum f := by
  have hp (d : ι) : Y d^4 =
      algebraMap ℝ A (a^3+2*a*b) * Y d + algebraMap ℝ A (a^2*b+b^2) * 1 := by
    calc
      _ = (Y d ^ 2)^2 := by ring
      _ = _ := by
        rw [hq]
        simp only [Algebra.smul_def, add_sq]
        rw [show (algebraMap ℝ A a * Y d)^2 =
          algebraMap ℝ A (a^2) * Y d^2 by simp [map_pow, mul_pow], hq]
        simp only [Algebra.smul_def, map_add, map_mul, map_pow, map_ofNat]
        ring
  simp_rw [hp, map_add ℓ, algebra_scalar, h0, h1, mul_zero, zero_add, mul_one]
  simp only [indexSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The raw fourth moment is the sum of its five index-multiplicity contributions. -/
theorem quadratic_fourth_moment_expansion
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (a b : ℝ)
    (h1 : ℓ 1 = 1) (h0 : ∀ d, ℓ (Y d) = 0)
    (hq : ∀ d, Y d ^ 2 = a • Y d + algebraMap ℝ A b)
    (f g h q : ι → ℝ) :
    quadraticFamilyMoment ℓ Y ![f,g,h,q] = distinctIndexMoment ℓ Y ![f,g,h,q] +
      a * repeatedPairSum (fun u v w => distinctIndexMoment ℓ Y ![u,v,w]) f g h q +
      a^2 * pairPairSum (fun u v => distinctIndexMoment ℓ Y ![u,v]) f g h q +
      (a^2-2*b) * tripleSingletonSum (fun u v => distinctIndexMoment ℓ Y ![u,v]) f g h q +
      (a^2*b-2*b^2) * indexSum (f*g*h*q) +
      b * repeatedPairSum (fun u v w => indexSum u * distinctIndexMoment ℓ Y ![v,w]) f g h q +
      b^2 * perfectPairingSum (fun u v => indexSum (u*v)) f g h q := by
  let F : (Fin 4 → ι) → ℝ := fun x =>
    (∏ i, (![f,g,h,q] : Fin 4 → ι → ℝ) i (x i)) * ℓ (∏ i, Y (x i))
  have h0123 : patternSum (r := 4) ![0,1,2,3] F = distinctIndexMoment ℓ Y ![f,g,h,q] := by
    unfold patternSum distinctIndexMoment
    apply Finset.sum_congr rfl
    intro x hx
    simp [F, Fin.prod_univ_four, Function.comp_def]
  have h0012 : patternSum (r := 3) ![0,0,1,2] F =
      a * distinctIndexMoment ℓ Y ![f*g,h,q] +
      b * (indexSum (f*g) * distinctIndexMoment ℓ Y ![h,q] -
        distinctIndexMoment ℓ Y ![(f*g)*h,q] - distinctIndexMoment ℓ Y ![(f*g)*q,h]) := by
    convert pair_single_single ℓ Y a b hq (f*g) h q using 1
    unfold patternSum
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_four, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply]
    congr 1; ring_nf
  have h0102 : patternSum (r := 3) ![0,1,0,2] F =
      a * distinctIndexMoment ℓ Y ![f*h,g,q] +
      b * (indexSum (f*h) * distinctIndexMoment ℓ Y ![g,q] -
        distinctIndexMoment ℓ Y ![(f*h)*g,q] - distinctIndexMoment ℓ Y ![(f*h)*q,g]) := by
    convert pair_single_single ℓ Y a b hq (f*h) g q using 1
    unfold patternSum
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_four, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply]
    congr 1 <;> ring_nf
  have h0120 : patternSum (r := 3) ![0,1,2,0] F =
      a * distinctIndexMoment ℓ Y ![f*q,g,h] +
      b * (indexSum (f*q) * distinctIndexMoment ℓ Y ![g,h] -
        distinctIndexMoment ℓ Y ![(f*q)*g,h] - distinctIndexMoment ℓ Y ![(f*q)*h,g]) := by
    convert pair_single_single ℓ Y a b hq (f*q) g h using 1
    unfold patternSum
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_four, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply]
    congr 1 <;> ring_nf
  have h0112 : patternSum (r := 3) ![0,1,1,2] F =
      a * distinctIndexMoment ℓ Y ![g*h,f,q] +
      b * (indexSum (g*h) * distinctIndexMoment ℓ Y ![f,q] -
        distinctIndexMoment ℓ Y ![(g*h)*f,q] - distinctIndexMoment ℓ Y ![(g*h)*q,f]) := by
    convert pair_single_single ℓ Y a b hq (g*h) f q using 1
    unfold patternSum
    rw [← sum_perm (Equiv.swap 0 1) (fun x => F (x ∘ ![0,1,1,2]))]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_four, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply, Equiv.swap_apply_def]
    norm_num
    congr 1 <;> ring_nf
  have h0121 : patternSum (r := 3) ![0,1,2,1] F =
      a * distinctIndexMoment ℓ Y ![g*q,f,h] +
      b * (indexSum (g*q) * distinctIndexMoment ℓ Y ![f,h] -
        distinctIndexMoment ℓ Y ![(g*q)*f,h] - distinctIndexMoment ℓ Y ![(g*q)*h,f]) := by
    convert pair_single_single ℓ Y a b hq (g*q) f h using 1
    unfold patternSum
    rw [← sum_perm (Equiv.swap 0 1) (fun x => F (x ∘ ![0,1,2,1]))]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_four, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply, Equiv.swap_apply_def]
    norm_num
    congr 1 <;> ring_nf
  have h0122 : patternSum (r := 3) ![0,1,2,2] F =
      a * distinctIndexMoment ℓ Y ![h*q,f,g] +
      b * (indexSum (h*q) * distinctIndexMoment ℓ Y ![f,g] -
        distinctIndexMoment ℓ Y ![(h*q)*f,g] - distinctIndexMoment ℓ Y ![(h*q)*g,f]) := by
    convert pair_single_single ℓ Y a b hq (h*q) f g using 1
    unfold patternSum
    rw [← sum_perm ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
      (fun x => F (x ∘ ![0,1,2,2]))]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_four, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply,
      Equiv.trans_apply, Equiv.swap_apply_def]
    norm_num
    congr 1 <;> ring_nf
  have h0011 : patternSum (r := 2) ![0,0,1,1] F =
      a^2 * distinctIndexMoment ℓ Y ![f*g,h*q] + b^2 * (indexSum (f*g) * indexSum (h*q) - indexSum ((f*g)*(h*q))) := by
    convert pair_pair ℓ Y a b h1 h0 hq (f*g) (h*q) using 1
    unfold patternSum
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_four, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply]
    congr 1 <;> ring_nf
  have h0101 : patternSum (r := 2) ![0,1,0,1] F =
      a^2 * distinctIndexMoment ℓ Y ![f*h,g*q] + b^2 * (indexSum (f*h) * indexSum (g*q) - indexSum ((f*h)*(g*q))) := by
    convert pair_pair ℓ Y a b h1 h0 hq (f*h) (g*q) using 1
    unfold patternSum
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_four, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply]
    congr 1 <;> ring_nf
  have h0110 : patternSum (r := 2) ![0,1,1,0] F =
      a^2 * distinctIndexMoment ℓ Y ![f*q,g*h] + b^2 * (indexSum (f*q) * indexSum (g*h) - indexSum ((f*q)*(g*h))) := by
    convert pair_pair ℓ Y a b h1 h0 hq (f*q) (g*h) using 1
    unfold patternSum
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_four, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply]
    congr 1 <;> ring_nf
  have h0001 : patternSum (r := 2) ![0,0,0,1] F =
      (a^2+b) * distinctIndexMoment ℓ Y ![f*g*h,q] := by
    convert triple_single ℓ Y a b h0 hq (f*g*h) q using 1
    unfold patternSum
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_four, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply]
    congr 1; ring_nf
  have h0010 : patternSum (r := 2) ![0,0,1,0] F =
      (a^2+b) * distinctIndexMoment ℓ Y ![f*g*q,h] := by
    convert triple_single ℓ Y a b h0 hq (f*g*q) h using 1
    unfold patternSum
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_four, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply]
    congr 1 <;> ring_nf
  have h0100 : patternSum (r := 2) ![0,1,0,0] F =
      (a^2+b) * distinctIndexMoment ℓ Y ![f*h*q,g] := by
    convert triple_single ℓ Y a b h0 hq (f*h*q) g using 1
    unfold patternSum
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_four, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply]
    congr 1 <;> ring_nf
  have h0111 : patternSum (r := 2) ![0,1,1,1] F =
      (a^2+b) * distinctIndexMoment ℓ Y ![g*h*q,f] := by
    convert triple_single ℓ Y a b h0 hq (g*h*q) f using 1
    unfold patternSum
    rw [← sum_perm (Equiv.swap 0 1) (fun x => F (x ∘ ![0,1,1,1]))]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [F, Fin.prod_univ_four, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply, Equiv.swap_apply_def]
    norm_num
    congr 1 <;> ring_nf
  have h0000 : patternSum (r := 1) ![0,0,0,0] F =
      (a^2*b+b^2) * indexSum (f*g*h*q) := by
    convert quadruple ℓ Y a b h1 h0 hq (f*g*h*q) using 1
    unfold patternSum
    have hi : ∀ x : Fin 1 → ι, Function.Injective x :=
      fun _ _ _ _ => Subsingleton.elim _ _
    simp only [hi, Finset.filter_true]
    rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    apply Finset.sum_congr rfl
    intro d hd
    simp [F, Fin.prod_univ_four, Function.comp_def, pow_succ, mul_assoc]
  rw [quadraticFamilyMoment_eq_tuple_sum]
  change (∑ x, F x) = _
  rw [sum_fin_four_eq_pattern_sums, h0123, h0012, h0102, h0120, h0112, h0121,
    h0122, h0011, h0101, h0110, h0001, h0010, h0100, h0111, h0000]
  simp only [repeatedPairSum, pairPairSum, tripleSingletonSum, perfectPairingSum]
  simp only [mul_left_comm, mul_comm]
  ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
