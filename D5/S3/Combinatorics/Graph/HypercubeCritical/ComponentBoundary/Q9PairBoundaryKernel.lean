/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairBoundaryKernel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairBoundaryKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Two leading weighted Huang axes reduce to a two-slice boundary kernel. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedStarLift

/-! Two leading axes in the weighted Huang boundary kernel for Q9 Problem 2. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PairBoundaryKernel

open scoped BigOperators
open BalancedCriticalSpectrum (Q flip)
open Q9IsotropicHuang (flipSign weightedAction weightedLinear weightedLinear_apply)
open Q9WeightedStarLift (boundaryKernel supported)

variable {F X : Type*} [Field F]

private def pairSlice (u v : Bool) : (Bool × Bool × X → F) →ₗ[F] (X → F) :=
  LinearMap.funLeft F F (fun x => (u, v, x))

private def slice (u : Bool) : (Bool × X → F) →ₗ[F] (X → F) :=
  LinearMap.funLeft F F (fun x => (u, x))

private theorem slice_apply (u : Bool) (f : Bool × X → F) (x : X) :
    slice u f x = f (u, x) := rfl

/-- The false-prefix Huang action in block order `00,10,01,11`. -/
def pairAction (B : Module.End F (X → F)) (a b : F) :
    Module.End F (Bool × Bool × X → F) :=
  LinearMap.pi fun (u, v, x) =>
    (LinearMap.proj x).comp (match u, v with
      | false, false => B.comp (pairSlice false false) +
          a • pairSlice true false - b • pairSlice false true
      | true, false => -(B.comp (pairSlice true false)) +
          a • pairSlice false false + b • pairSlice true true
      | false, true => -(B.comp (pairSlice false true)) -
          b • pairSlice false false + a • pairSlice true true
      | true, true => B.comp (pairSlice true true) +
          b • pairSlice true false + a • pairSlice false true)

/-- Allowed slices `(M,S,S,∅)` for either the source or the rows. -/
def pairMask (M S : Set X) : Set (Bool × Bool × X) :=
  {z | match z.1, z.2.1 with
  | false, false => z.2.2 ∈ M
  | true, true => False
  | _, _ => z.2.2 ∈ S}

/-- Allowed supports of the two slices in the reduced kernel. -/
def sliceMask (M S : Set X) : Set (Bool × X) :=
  {z | if z.1 then z.2 ∈ S else z.2 ∈ M}

/-- The two-slice operator sends `(p,q)` to `(B p + c q,-B q + p)`
when its two off-diagonal coefficients are `c` and `1`. -/
def sliceAction (B : Module.End F (X → F)) (upper lower : F) :
    Module.End F (Bool × X → F) :=
  LinearMap.pi fun (u, x) =>
    (LinearMap.proj x).comp (match u with
      | false => B.comp (slice false) + upper • slice true
      | true => -(B.comp (slice true)) + lower • slice false)

private def lift (a b : F) : (Bool × X → F) →ₗ[F] (Bool × Bool × X → F) :=
  LinearMap.pi fun (u, v, x) =>
    (LinearMap.proj x).comp (match u, v with
      | false, false => slice false
      | true, false => a • slice true
      | false, true => (-b) • slice true
      | true, true => 0)

private theorem pairSlice_lift (a b : F) (f : Bool × X → F) (u v : Bool) :
    pairSlice u v (lift a b f) = match u, v with
      | false, false => slice false f
      | true, false => a • slice true f
      | false, true => (-b) • slice true f
      | true, true => 0 := by
  cases u <;> cases v <;> rfl

private theorem pairAction_lift (B : Module.End F (X → F)) (a b : F)
    (f : Bool × X → F) :
    pairAction B a b (lift a b f) = lift a b (sliceAction B (a ^ 2 + b ^ 2) 1 f) := by
  funext z
  rcases z with ⟨u, v, x⟩
  change pairAction B a b (lift a b f) (u, v, x) =
    pairSlice u v (lift a b (sliceAction B (a ^ 2 + b ^ 2) 1 f)) x
  cases u <;> cases v <;>
    simp only [pairAction, sliceAction, LinearMap.pi_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
      LinearMap.smul_apply, pairSlice_lift, map_smul, map_zero,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, Pi.neg_apply, smul_eq_mul,
      slice_apply] <;> ring

private theorem lift_supported_iff (a b : F) (hc : a ^ 2 + b ^ 2 ≠ 0)
    (M S : Set X) (f : Bool × X → F) :
    lift a b f ∈ supported (pairMask M S) ↔ f ∈ supported (sliceMask M S) := by
  change (∀ z ∉ pairMask M S, lift a b f z = 0) ↔ (∀ z ∉ sliceMask M S, f z = 0)
  constructor
  · intro h z hz
    rcases z with ⟨u, x⟩
    cases u
    · exact h (false, false, x) (by simpa [pairMask, sliceMask] using hz)
    · have hx : x ∉ S := by simpa [sliceMask] using hz
      have ha : a * f (true, x) = 0 := h (true, false, x) hx
      have hb : (-b) * f (true, x) = 0 := h (false, true, x) hx
      by_contra hf
      have ha₀ := (mul_eq_zero.mp ha).resolve_right hf
      have hb₀ := neg_eq_zero.mp ((mul_eq_zero.mp hb).resolve_right hf)
      exact hc (by simp [ha₀, hb₀])
  · intro h z hz
    rcases z with ⟨u, v, x⟩
    cases u <;> cases v
    · exact h (false, x) (by simpa [pairMask, sliceMask] using hz)
    · change (-b) * f (true, x) = 0
      rw [h (true, x) (by simpa [pairMask, sliceMask] using hz), mul_zero]
    · change a * f (true, x) = 0
      rw [h (true, x) (by simpa [pairMask, sliceMask] using hz), mul_zero]
    · rfl

private def lower (a b : F) (f : Bool × Bool × X → F) : Bool × X → F
  | (false, x) => f (false, false, x)
  | (true, x) => (a * f (true, false, x) - b * f (false, true, x)) / (a ^ 2 + b ^ 2)

private theorem lower_lift (a b : F) (hc : a ^ 2 + b ^ 2 ≠ 0) (f : Bool × X → F) :
    lower a b (lift a b f) = f := by
  funext z
  rcases z with ⟨u, x⟩
  cases u
  · rfl
  · change (a * (a * f (true, x)) - b * ((-b) * f (true, x))) / (a ^ 2 + b ^ 2) =
      f (true, x)
    apply (div_eq_iff hc).2
    ring

private theorem lift_lower (a b : F) (hc : a ^ 2 + b ^ 2 ≠ 0) (f : Bool × Bool × X → F)
    (h11 : ∀ x, f (true, true, x) = 0)
    (hrow : ∀ x, b * f (true, false, x) + a * f (false, true, x) = 0) :
    lift a b (lower a b f) = f := by
  funext z
  rcases z with ⟨u, v, x⟩
  cases u <;> cases v
  · rfl
  · change (-b) * ((a * f (true, false, x) - b * f (false, true, x)) / (a ^ 2 + b ^ 2)) =
      f (false, true, x)
    rw [← mul_div_assoc]
    apply (div_eq_iff hc).2
    linear_combination -a * hrow x
  · change a * ((a * f (true, false, x) - b * f (false, true, x)) / (a ^ 2 + b ^ 2)) =
      f (true, false, x)
    rw [← mul_div_assoc]
    apply (div_eq_iff hc).2
    linear_combination -b * hrow x
  · exact (h11 x).symm

/-- Eliminate the forbidden `11` slice. The map sends `(p,q)` to `(p,a q,-b q,0)`.
Its inverse reads `p = f00` and `q = (a f10 - b f01) / (a² + b²)` pointwise.
The source and row masks can be chosen independently, in particular for each parity. -/
def boundaryKernelEquiv (B : Module.End F (X → F)) (a b : F) (hc : a ^ 2 + b ^ 2 ≠ 0)
    (M S M' S' : Set X) :
    boundaryKernel (sliceAction B (a ^ 2 + b ^ 2) 1) (sliceMask M S) (sliceMask M' S') ≃ₗ[F]
      boundaryKernel (pairAction B a b) (pairMask M S) (pairMask M' S') := by
  have hmem (f : Bool × X → F) :
      lift a b f ∈ boundaryKernel (pairAction B a b) (pairMask M S) (pairMask M' S') ↔
        f ∈ boundaryKernel (sliceAction B (a ^ 2 + b ^ 2) 1) (sliceMask M S)
          (sliceMask M' S') := by
    change (lift a b f ∈ supported (pairMask M S) ∧
      pairAction B a b (lift a b f) ∈ supported (pairMask M' S')) ↔
        (f ∈ supported (sliceMask M S) ∧
          sliceAction B (a ^ 2 + b ^ 2) 1 f ∈ supported (sliceMask M' S'))
    rw [pairAction_lift]
    exact and_congr (lift_supported_iff a b hc M S f) (lift_supported_iff a b hc M' S' _)
  have hreconstruct (f : boundaryKernel (pairAction B a b) (pairMask M S) (pairMask M' S')) :
      lift a b (lower a b f) = (f : Bool × Bool × X → F) := by
    have hf : (∀ z ∉ pairMask M S, (f : Bool × Bool × X → F) z = 0) ∧
        (∀ z ∉ pairMask M' S', pairAction B a b f z = 0) := f.property
    have h11 (x : X) : (f : Bool × Bool × X → F) (true, true, x) = 0 :=
      hf.1 (true, true, x) (by simp [pairMask])
    have hs : pairSlice true true (f : Bool × Bool × X → F) = 0 := funext h11
    apply lift_lower a b hc _ h11
    intro x
    have hz := hf.2 (true, true, x) (by simp [pairMask])
    simp only [pairAction, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.add_apply, LinearMap.smul_apply, hs, map_zero, Pi.add_apply, zero_add,
      Pi.smul_apply, smul_eq_mul] at hz
    exact hz
  exact
    { toFun := fun f => ⟨lift a b f, (hmem f).2 f.property⟩
      invFun := fun f => ⟨lower a b f, (hmem _).1 (by
        rw [hreconstruct f]
        exact f.property)⟩
      left_inv := fun f => by
        apply Subtype.ext
        change lower a b (lift a b (f : Bool × X → F)) = (f : Bool × X → F)
        exact lower_lift a b hc (f : Bool × X → F)
      right_inv := fun f => Subtype.ext (hreconstruct f)
      map_add' := fun f g => Subtype.ext (map_add (lift a b) (f : Bool × X → F) g)
      map_smul' := fun r f => Subtype.ext (map_smul (lift a b) r (f : Bool × X → F)) }

private theorem sliceAction_similarity (B : Module.End F (X → F))
    (c r : F) (hc : c ≠ 0) (hr : r ^ 2 = c) :
    ∃ D : (Bool × X → F) ≃ₗ[F] (Bool × X → F),
      ∀ f, sliceAction B r r (D f) = D (sliceAction B c 1 f) := by
  have hr₀ : r ≠ 0 := by
    rintro rfl
    exact hc (by simpa using hr.symm)
  let scale (s : F) : Module.End F (Bool × X → F) :=
    LinearMap.pi fun (u, x) => (LinearMap.proj x).comp (match u with
      | false => slice false
      | true => s • slice true)
  have hscale (s t : F) (hst : s * t = 1) : (scale s).comp (scale t) = LinearMap.id := by
    apply LinearMap.ext
    intro f
    funext z
    rcases z with ⟨u, x⟩
    cases u
    · rfl
    · change s * (t * f (true, x)) = f (true, x)
      rw [← mul_assoc, hst, one_mul]
  refine ⟨LinearEquiv.ofLinearMap (scale r) (scale r⁻¹)
    (hscale _ _ (mul_inv_cancel₀ hr₀)) (hscale _ _ (inv_mul_cancel₀ hr₀)), fun f => ?_⟩
  change sliceAction B r r (scale r f) = scale r (sliceAction B c 1 f)
  have hp : slice false (scale r f) = slice false f := rfl
  have hq : slice true (scale r f) = r • slice true f := rfl
  have hscale_apply (g : Bool × X → F) (u : Bool) (x : X) :
      scale r g (u, x) = (if u then r else 1) * g (u, x) := by
    cases u
    · exact (one_mul _).symm
    · rfl
  funext z
  rcases z with ⟨u, x⟩
  cases u <;>
    simp only [hscale_apply, sliceAction, LinearMap.pi_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
      hp, hq, map_smul, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, slice_apply,
      Bool.false_eq_true, ↓reduceIte, ← hr] <;> ring

/-- Weighted Huang action on the tail cube, with the original sign convention. -/
def tailAction {n : ℕ} (w : Fin n → F) : Module.End F (Q n → F) :=
  ∑ i, w i • LinearMap.pi (fun x => (flipSign i x : F) • LinearMap.proj (flip x i))

private theorem tailAction_apply {n : ℕ} (w : Fin n → F) (f : Q n → F) (x : Q n) :
    tailAction w f x = ∑ i, w i * (flipSign i x : F) * f (flip x i) := by
  simp [tailAction, Finset.sum_apply, mul_assoc]

private theorem flipSign_cons_succ {n : ℕ} (u : Bool) (x : Q n) (i : Fin n) :
    flipSign i.succ (Fin.cons u x) = (if u then 1 else -1) * flipSign i x := by
  have ht : Sensitivity.π (Fin.cons u x) = x :=
    Fin.tail_cons (α := fun _ : Fin (n + 1) => Bool) u x
  change (if (Fin.cons u x : Q (n + 1)) 0 then 1 else -1) *
    flipSign i (Sensitivity.π (Fin.cons u x)) = _
  rw [Fin.cons_zero, ht]

private theorem tailAction_cons {n : ℕ} (a : F) (w : Fin n → F)
    (f : Q (n + 1) → F) (u : Bool) (x : Q n) :
    tailAction (Fin.cons a w) f (Fin.cons u x) =
      (if u then 1 else -1) * tailAction w (fun y => f (Fin.cons u y)) x +
        a * f (Fin.cons (!u) x) := by
  rw [tailAction_apply, Fin.sum_univ_succ, tailAction_apply]
  have hzero : flipSign 0 (Fin.cons u x) = 1 := rfl
  simp only [hzero, Int.cast_one, mul_one, Fin.cons_zero, Fin.cons_succ, flipSign_cons_succ,
    Int.cast_mul, BalancedCriticalSpectrum.flip, Fin.update_cons_zero, ← Fin.cons_update]
  rw [Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases u <;> simp

-- The positive B slice is the true prefix of the new Huang axis.
example {n : ℕ} (w : Fin n → F) (c r : F) (hc : c ≠ 0) (hr : r ^ 2 = c) :
    ∃ D : (Bool × Q n → F) ≃ₗ[F] (Q (n + 1) → F),
      ∀ f, tailAction (Fin.cons r w) (D f) = D (sliceAction (tailAction w) c 1 f) := by
  obtain ⟨D, hD⟩ := sliceAction_similarity (tailAction w) c r hc hr
  let vertices : Bool × Q n ≃ Q (n + 1) :=
    { toFun := fun z => Fin.cons (!z.1) z.2
      invFun := fun x => (!x 0, Fin.tail x)
      left_inv := by
        rintro ⟨u, x⟩
        simp
      right_inv := by
        intro x
        simp }
  let E := LinearEquiv.funCongrLeft F F vertices
  have hrow (g : Q (n + 1) → F) :
      E (tailAction (Fin.cons r w) g) = sliceAction (tailAction w) r r (E g) := by
    funext z
    rcases z with ⟨u, x⟩
    change tailAction (Fin.cons r w) g (Fin.cons (!u) x) =
      sliceAction (tailAction w) r r (fun t => g (Fin.cons (!t.1) t.2)) (u, x)
    have hs (v : Bool) :
        slice v (fun t => g (Fin.cons (!t.1) t.2)) = fun y => g (Fin.cons (!v) y) := rfl
    cases u <;>
      simp only [tailAction_cons, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        sliceAction, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
        Pi.neg_apply, smul_eq_mul, hs] <;> ring
  refine ⟨D.trans E.symm, fun f => E.injective ?_⟩
  change E (tailAction (Fin.cons r w) (E.symm (D f))) =
    E (E.symm (D (sliceAction (tailAction w) c 1 f)))
  simpa only [hrow, LinearEquiv.apply_symm_apply] using hD f

/-- Put the two distinguished coordinates first. -/
def pairVertex {n : ℕ} : Bool × Bool × Q n ≃ Q (n + 2) :=
  (Equiv.prodCongr (Equiv.refl Bool) (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))).trans
    (Fin.consEquiv (fun _ : Fin (n + 2) => Bool))

/-- The mask on actual nine-cube vertices with the distinguished coordinates first. -/
def cubeMask (M S : Set (Q 7)) : Set (Q 9) := pairVertex.symm ⁻¹' pairMask M S

private theorem weighted_row (a b : F) (w : Fin 7 → F) (f : Q 9 → F)
    (z : Bool × Bool × Q 7) :
    weightedLinear (Fin.cons a (Fin.cons b w)) f (pairVertex z) =
      pairAction (tailAction w) a b (fun t => f (pairVertex t)) z := by
  rcases z with ⟨u, v, x⟩
  have hopen : weightedLinear (Fin.cons a (Fin.cons b w)) f =
      tailAction (Fin.cons a (Fin.cons b w)) f := by
    funext y
    simp only [weightedLinear_apply, weightedAction, tailAction_apply]
  rw [hopen]
  change tailAction (Fin.cons a (Fin.cons b w)) f (Fin.cons u (Fin.cons v x)) =
    pairAction (tailAction w) a b (fun t => f (Fin.cons t.1 (Fin.cons t.2.1 t.2.2))) (u, v, x)
  have hs (s t : Bool) :
      pairSlice s t (fun z => f (Fin.cons z.1 (Fin.cons z.2.1 z.2.2))) =
        fun y => f (Fin.cons s (Fin.cons t y)) := rfl
  cases u <;> cases v <;>
    simp only [tailAction_cons, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      pairAction, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      hs] <;> ring

/-- The reduction for the actual weighted Huang operator when the pair is first. -/
def weightedBoundaryKernelEquiv (a b : F) (w : Fin 7 → F) (hc : a ^ 2 + b ^ 2 ≠ 0)
    (M S M' S' : Set (Q 7)) :
    boundaryKernel (sliceAction (tailAction w) (a ^ 2 + b ^ 2) 1)
        (sliceMask M S) (sliceMask M' S') ≃ₗ[F]
      boundaryKernel (weightedLinear (Fin.cons a (Fin.cons b w)))
        (cubeMask M S) (cubeMask M' S') := by
  let E := LinearEquiv.funCongrLeft F F (pairVertex (n := 7))
  have hvanish (P T : Set (Q 7)) (g : Q 9 → F) :
      (∀ z ∉ pairMask P T, g (pairVertex z) = 0) ↔ ∀ y ∉ cubeMask P T, g y = 0 := by
    constructor
    · intro h y hy
      obtain ⟨z, rfl⟩ := (pairVertex (n := 7)).surjective y
      exact h z (by simpa [cubeMask] using hy)
    · intro h z hz
      exact h _ (by simpa [cubeMask] using hz)
  have hcomap :
      (boundaryKernel (pairAction (tailAction w) a b) (pairMask M S) (pairMask M' S')).comap
        E.toLinearMap = boundaryKernel (weightedLinear (Fin.cons a (Fin.cons b w)))
          (cubeMask M S) (cubeMask M' S') := by
    apply Submodule.ext
    intro f
    change ((∀ z ∉ pairMask M S, f (pairVertex z) = 0) ∧
      (∀ z ∉ pairMask M' S', pairAction (tailAction w) a b (fun t => f (pairVertex t)) z = 0)) ↔
      ((∀ y ∉ cubeMask M S, f y = 0) ∧
        (∀ y ∉ cubeMask M' S', weightedLinear (Fin.cons a (Fin.cons b w)) f y = 0))
    simp only [← weighted_row a b w f]
    exact and_congr (hvanish M S f) (hvanish M' S' _)
  exact (boundaryKernelEquiv (tailAction w) a b hc M S M' S').trans
    ((LinearEquiv.ofSubmodule' E _).symm.trans (LinearEquiv.ofEq _ _ hcomap))

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PairBoundaryKernel
