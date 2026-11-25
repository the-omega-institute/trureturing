/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identify actual finite-field diagonal code marginals from column-span ranks, and prove physical separability. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
noncomputable section

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
def pushed (f : X → Y) (y : Y) : ℝ :=
  ((univ.filter (fun x => f x=y)).card : ℝ) / Fintype.card X

theorem pushed_nonneg (f : X → Y) (y : Y) : 0 ≤ pushed f y := by
  unfold pushed
  positivity

theorem pushed_sum [Nonempty X] (f : X → Y) :
    ∑ y, pushed f y = 1 := by
  unfold pushed
  rw [←sum_div]
  have h : (Fintype.card X) = ∑ y : Y, (univ.filter (fun x : X => f x=y)).card :=
    card_eq_sum_card_fiberwise (fun x (_ : x ∈ (univ : Finset X)) => mem_univ (f x))
  rw [←Nat.cast_sum,←h]
  exact div_self (by positivity)

def density (f : X → Y) : Matrix Y Y ℂ :=
  diagonal (fun y => (pushed f y : ℂ))

theorem density_psd (f : X → Y) : (density f).PosSemidef := by
  unfold density
  exact posSemidef_diagonal_iff.mpr (fun y => by exact_mod_cast pushed_nonneg f y)

theorem density_trace [Nonempty X] (f : X → Y) : (density f).trace=1 := by
  unfold density Matrix.trace
  simp only [diag_diagonal, ←Complex.ofReal_sum, pushed_sum, Complex.ofReal_one]

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem projected_weight (f : X → A × B) (b : B) :
    ∑ a, pushed f (a,b) = pushed (Prod.snd ∘ f) b := by
  classical
  unfold pushed
  rw [←sum_div,←Nat.cast_sum]
  apply congrArg (fun n : ℕ => (n : ℝ) / Fintype.card X)
  have h := sum_card_fiberwise_eq_card_filter (univ.filter (fun x : X => (f x).2=b))
      (univ : Finset A) (fun x => (f x).1)
  calc
    _ = ∑ a : A, ((univ.filter (fun x : X => (f x).2=b)).filter
        (fun x => (f x).1=a)).card := by
      apply sum_congr rfl
      intro a _
      congr 1
      ext x
      simp only [mem_filter,mem_univ,true_and,Prod.ext_iff]
      tauto
    _ = _ := by simpa using h


section
private theorem scaled_rpow_pointwise {c x K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hx : x = 0 ∨ x = c) :
    x ^ K = c ^ (K - 1) * x := by
  rcases hx with rfl | hx
  · simp [Real.zero_rpow hK.ne']
  · subst x
    calc
      c ^ K = c ^ ((K - 1) + 1) := by rw [sub_add_cancel]
      _ = c ^ (K - 1) * c := by rw [Real.rpow_add hc,Real.rpow_one]
end
section
variable {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A]
  [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
private theorem spectrum_of_scaled_idempotent {a : A} (ha : IsSelfAdjoint a)
    {c : ℝ} (hp : a * a = c • a) :
    ∀ x ∈ spectrum ℝ a, x = 0 ∨ x = c := by
  have hcf : cfc (fun x : ℝ => x ^ 2) a = cfc (fun x : ℝ => c * x) a := by
    rw [cfc_pow_id a 2 ha, cfc_const_mul_id c a ha,pow_two,hp]
  have hpt := eqOn_of_cfc_eq_cfc hcf (by fun_prop) (by fun_prop) ha
  intro x hx
  have hh : x ^ 2 = c * x := hpt hx
  have hz : x * (x - c) = 0 := by
    rw [mul_sub,← pow_two,mul_comm x c,hh,sub_self]
  exact (mul_eq_zero.mp hz).imp id sub_eq_zero.mp
end
section
variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsSemitopologicalRing A] [T2Space A]
private theorem cfc_rpow_of_two_spectrum {a : A} (ha : 0 ≤ a)
    {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (he : ∀ x ∈ spectrum ℝ a, x = 0 ∨ x = c) :
    CFC.rpow a K = (c ^ (K - 1)) • a := by
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real ha]
  calc
    _ = cfc (fun x : ℝ => c ^ (K - 1) * x) a :=
      cfc_congr (fun x hx => scaled_rpow_pointwise hc hK (he x hx))
    _ = _ := cfc_const_mul_id _ _ ha.isSelfAdjoint
private theorem cfc_rpow_of_scaled_idempotent {a : A} (ha : 0 ≤ a)
    {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (hp : a * a = c • a) :
    CFC.rpow a K = (c ^ (K - 1)) • a :=
  cfc_rpow_of_two_spectrum ha hc hK (spectrum_of_scaled_idempotent ha.isSelfAdjoint hp)
end
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The same exact CFC moment directly from a scaled-idempotent identity;
neither a basis construction nor a separate eigenvalue enumeration is needed. -/
private theorem trace_rpow_of_scaled_projection {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef)
    {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hp : ρ * ρ = c • ρ) (ht : ρ.trace = 1) :
    (trace (ρ ^ K)).re = c ^ (K - 1) := by
  rw [show ρ ^ K = (c ^ (K - 1)) • ρ from
    cfc_rpow_of_scaled_idempotent hρ.nonneg hc hK hp,
    trace_smul, ht, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]
end

end

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder Classical
section
variable {F X Y : Type*} [Field F] [Fintype F]
  [AddCommGroup X] [Module F X] [Fintype X]
  [AddCommGroup Y] [Module F Y] [Fintype Y] [DecidableEq Y]

private theorem fiber_size (f : X →ₗ[F] Y) {y : Y} (hy : y ∈ f.range) :
    (univ.filter (fun x : X => f x=y)).card = (univ.filter (fun x : X => f x=0)).card := by
  classical
  obtain ⟨a,ha⟩ := hy
  let e : {x : X // x ∈ univ.filter (fun x => f x=y)} ≃
      {x : X // x ∈ univ.filter (fun x => f x=0)} :=
    ⟨fun x => ⟨x.val-a,by have hx := (mem_filter.mp x.property).2; simp [map_sub,hx,ha]⟩,
     fun x => ⟨x.val+a,by have hx := (mem_filter.mp x.property).2; simp [map_add,hx,ha]⟩,
     fun x => Subtype.ext (sub_add_cancel _ _),fun x => Subtype.ext (add_sub_cancel_right _ _)⟩
  simpa only [Fintype.card_coe] using Fintype.card_congr e

theorem uniform_range (f : X →ₗ[F] Y) (y : Y) :
    pushed f y = if y ∈ f.range then (Fintype.card f.range : ℝ)⁻¹ else 0 := by
  classical
  let c := pushed f 0
  have h (z : Y) : pushed f z = if z ∈ f.range then c else 0 := by
    by_cases hz : z ∈ f.range
    · rw [if_pos hz]
      unfold c pushed
      rw [fiber_size f hz]
    · rw [if_neg hz]
      unfold pushed
      have he : univ.filter (fun x : X => f x=z) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hz ⟨x,(mem_filter.mp hx).2⟩
      simp [he]
  have hsum := pushed_sum (f : X → Y)
  have hcard : (univ.filter (fun z : Y => z ∈ f.range)).card = Fintype.card f.range := by
    exact (Fintype.card_of_subtype _ (fun i => by simp)).symm
  simp_rw [h] at hsum
  rw [←sum_filter, sum_const, hcard, nsmul_eq_mul] at hsum
  have hc : c = (Fintype.card f.range : ℝ)⁻¹ := by
    rw [←one_div, eq_div_iff (by positivity)]
    simpa [mul_comm] using hsum
  rw [h,hc]

theorem linear_power (f : X →ₗ[F] Y) {K : ℝ} (hK : 0<K) :
    (((density f) ^ K).trace).re = ((Fintype.card F : ℝ)^(1-K))^(Module.finrank F f.range) := by
  classical
  let n : ℝ := Fintype.card f.range
  have hn : 0<n := by dsimp [n]; positivity
  have hp : density f * density f = n⁻¹ • density f := by
    unfold density
    rw [Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases h : a=b
    · subst b
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply]
      rw [uniform_range f]
      by_cases ha : a ∈ f.range <;> simp [ha,n,Algebra.smul_def]
    · simp [Matrix.diagonal_apply_ne _ h,Matrix.smul_apply]
  rw [trace_rpow_of_scaled_projection (density_psd f) (inv_pos.mpr hn) hK hp (density_trace f),
    Real.inv_rpow hn.le,←Real.rpow_neg hn.le]
  have hsub : -(K-1)=1-K := by ring
  rw [hsub]
  dsimp [n]
  rw [Module.card_eq_pow_finrank (K:=F), Nat.cast_pow]
  let a : ℝ := Fintype.card F
  let r := Module.finrank F f.range
  change (a^r)^(1-K)=(a^(1-K))^r
  have ha : 0≤a := by positivity
  calc
    _ = a ^ ((r:ℝ)*(1-K)) := by rw [Real.rpow_mul ha,Real.rpow_natCast]
    _ = a ^ ((1-K)*(r:ℝ)) := by rw [mul_comm]
    _ = _ := by rw [Real.rpow_mul ha,Real.rpow_natCast]

end

open Finset Matrix
open scoped BigOperators MatrixOrder ComplexOrder
section
variable {F V I : Type*} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [Fintype I] [DecidableEq I]

/-- A word is obtained by evaluating one linear functional on every column. -/
def encoder (v : I → V) : Module.Dual F V →ₗ[F] (I → F) where
  toFun f i := f (v i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def columns (v : I → V) (S : Finset I) : Submodule F V :=
  Submodule.span F (v '' (S : Set I))

def project (v : I → V) (S : Finset I) : Module.Dual F V →ₗ[F] (S → F) :=
  encoder (fun i : S => v i)

omit [Fintype F] [DecidableEq F] [Fintype I] [DecidableEq I] in
theorem projected_rank (v : I → V) (S : Finset I) :
    Module.finrank F (project (F:=F) v S).range = Module.finrank F (columns (F:=F) v S) := by
  let P : Submodule F V := columns (F:=F) v S
  let w (i : S) : P := ⟨v i,Submodule.subset_span ⟨i,i.property,rfl⟩⟩
  let g : Module.Dual F P →ₗ[F] (S → F) := encoder w
  have hg : Function.Injective g := by
    intro a b h
    ext ⟨x,hx⟩
    change a ⟨x,hx⟩ = b ⟨x,hx⟩
    change x ∈ Submodule.span F (v '' (S : Set I)) at hx
    apply Submodule.span_induction (p := fun z hz => a ⟨z,hz⟩ = b ⟨z,hz⟩) _ _ _ _ hx
    · intro z hz
      obtain ⟨i,hi,rfl⟩ := hz
      exact congrFun h ⟨i,hi⟩
    · exact (a.map_zero).trans b.map_zero.symm
    · intro x y hx hy h₁ h₂
      change a ((⟨x,hx⟩ : P) + ⟨y,hy⟩) = b ((⟨x,hx⟩ : P) + ⟨y,hy⟩)
      rw [map_add,map_add,h₁,h₂]
    · intro r x hx h₁
      change a (r • (⟨x,hx⟩ : P)) = b (r • (⟨x,hx⟩ : P))
      rw [map_smul,map_smul,h₁]
  have he : project v S = g.comp P.subtype.dualMap := rfl
  rw [he, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (LinearMap.dualMap_surjective_of_injective P.injective_subtype)),
    LinearMap.finrank_range_of_inj hg, Subspace.dual_finrank_eq]

def splitWord (S : Finset I) : (I → F) ≃ (({i // i ∉ S} → F) × (S → F)) :=
  (Equiv.piEquivPiSubtypeProd (· ∈ S) (fun _ => F)).trans (Equiv.prodComm _ _)

def mixedMarginal [Fintype (Module.Dual F V)] (v : I → V) (S : Finset I) :
    Matrix (S → F) (S → F) ℂ :=
  Matrix.of fun b c => Matrix.trace (Matrix.of fun a d =>
    density (splitWord S ∘ (encoder v : Module.Dual F V → (I → F))) (a,b) (d,c))

theorem marginal_matrix [Fintype (Module.Dual F V)] (v : I → V) (S : Finset I) :
    mixedMarginal v S = density (project v S : Module.Dual F V → (S → F)) := by
  ext b c
  let f : Module.Dual F V → (({i // i ∉ S} → F) × (S → F)) := splitWord S ∘ encoder v
  change (∑ a, density f (a,b) (a,c)) = density (project v S : Module.Dual F V → (S → F)) b c
  by_cases h : b=c
  · subst c
    simp only [density, diagonal_apply_eq, ←Complex.ofReal_sum]
    exact congrArg (fun w : ℝ => (w : ℂ)) (projected_weight f b)
  · have hd (a : {i // i ∉ S} → F) : (a,b)≠(a,c) := fun hh => h (congrArg Prod.snd hh)
    rw [show density (project v S : Module.Dual F V → (S → F)) b c=0 from diagonal_apply_ne _ h]
    apply Finset.sum_eq_zero
    intro a _
    exact diagonal_apply_ne _ (hd a)

theorem actual_column_moment [Fintype (Module.Dual F V)] (v : I → V) (S : Finset I)
    {K : ℝ} (hK : 0<K) :
    (((mixedMarginal (F:=F) v S) ^ K).trace).re =
      ((Fintype.card F : ℝ)^(1-K))^(Module.finrank F (columns (F:=F) v S)) := by
  rw [marginal_matrix, linear_power (project (F:=F) v S) hK, projected_rank]

end

open Finset Matrix
open scoped BigOperators MatrixOrder ComplexOrder
section
variable {F V I : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup V]
  [Module F V] [Fintype (Module.Dual F V)] [Fintype I] [DecidableEq I]

/-- The computational-basis projector of a word is a tensor of single-site
basis projectors. This uses its entries, not a separability hypothesis. -/
theorem product_basis_projector (w a b : I → F) :
    (∏ i : I, if a i=w i ∧ b i=w i then (1:ℂ) else 0) =
    if a=w ∧ b=w then 1 else 0 := by
  by_cases h : a=w ∧ b=w
  · rcases h with ⟨rfl,rfl⟩
    simp
  · have hn : ∃ i, ¬(a i=w i ∧ b i=w i) := by
      by_contra! he
      exact h ⟨funext fun i => (he i).1,funext fun i => (he i).2⟩
    obtain ⟨i,hi⟩ := hn
    rw [if_neg h]
    exact prod_eq_zero (mem_univ i) (if_neg hi)

/-- The full, normalized mixed state is explicitly a uniform sum of
tensor products of rank-one local diagonal projectors. -/
theorem actual_product_mixture (v : I → V) (a b : I → F) :
    density (encoder (F:=F) v : Module.Dual F V → (I → F)) a b =
    (∑ f : Module.Dual F V, ∏ i : I,
      if a i=f (v i) ∧ b i=f (v i) then (1:ℂ) else 0) /
      (Fintype.card (Module.Dual F V) : ℂ) := by
  have h (f : Module.Dual F V) := product_basis_projector ((encoder (F:=F) v) f) a b
  change ∀ f : Module.Dual F V, _ at h
  simp_rw [show ∀ f : Module.Dual F V,
    (∏ i : I, if a i=f (v i) ∧ b i=f (v i) then (1:ℂ) else 0) =
    if a=encoder (F:=F) v f ∧ b=encoder (F:=F) v f then 1 else 0 from h]
  by_cases hab : a=b
  · subst b
    simp only [density,diagonal_apply_eq,pushed,Complex.ofReal_div,Complex.ofReal_natCast,and_self]
    have ef (f : Module.Dual F V) : a=encoder (F:=F) v f ↔ encoder (F:=F) v f=a := eq_comm
    simp_rw [ef,←sum_filter,sum_const,nsmul_eq_mul,mul_one]
  · have he (f : Module.Dual F V) : ¬(a=encoder (F:=F) v f ∧ b=encoder (F:=F) v f) :=
      fun g => hab (g.1.trans g.2.symm)
    simp [density,diagonal_apply_ne _ hab,he]

end

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
