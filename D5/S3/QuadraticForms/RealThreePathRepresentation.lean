/- GID: D5/S3/QuadraticForms/RealThreePathRepresentation
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/RealThreePathRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original real-linear Hilbert models of arbitrary-marker three-path balance. -/

module

public import D5.S3.QuadraticForms.RealThreePathPolar
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Tactic

/-! Radical descent retains the original real scalar action and labels in the Hilbert model. -/

public section

noncomputable section

namespace D5.S3.QuadraticForms.RealThreePathRepresentation

open RealThreePathPolar
open ThreeWayPositiveKernel
open scoped ComplexConjugate

universe u v w

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- A minimal complete Hilbert model with the original real-linear label map. -/
structure HilbertModel (U : V → V) (q : V → ℝ) where
  carrier : Type v
  [normed : NormedAddCommGroup carrier]
  [innerProduct : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]
  label : V →ₗ[ℝ] carrier
  normSq : ∀ x, q x = q 0 + ‖label x‖ ^ 2
  phase : ∀ x, label (U x) = omega • label x
  minimal : (Submodule.span ℂ (Set.range label)).topologicalClosure = ⊤

attribute [instance] HilbertModel.normed HilbertModel.innerProduct HilbertModel.complete

-- proof_shape: bind-only; live consumer: original_visible_quotient.
private theorem marker_descent (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (U : V → V)
    (ht : ∀ x y, B x y + B x (U y) + B (U x) y = 0) :
    ∃ T : (V ⧸ B.ker) →ₗ[ℝ] (V ⧸ B.ker),
      ∀ x, T (B.ker.mkQ x) = B.ker.mkQ (U x) := by
  let N := B.ker
  let π := N.mkQ
  have heq (x y : V) (hxy : π x = π y) : π (U x) = π (U y) := by
    apply (Submodule.Quotient.eq N).mpr
    have hh := (Submodule.Quotient.eq N).mp hxy
    change B (x - y) = 0 at hh
    change B (U x - U y) = 0
    ext z
    have hz := congrArg (fun f => f z) hh
    simp only [map_sub, LinearMap.sub_apply, LinearMap.zero_apply] at hz ⊢
    have hUz := congrArg (fun f => f (U z)) hh
    simp only [map_sub, LinearMap.sub_apply, LinearMap.zero_apply] at hUz
    linarith [ht x z, ht y z]
  let f : V ⧸ N → V ⧸ N := fun z => Quotient.liftOn z (fun x => π (U x))
    (fun x y hxy => heq x y ((Submodule.Quotient.eq N).mpr
      ((Submodule.quotientRel_def N).mp hxy)))
  have hf (x : V) : f (π x) = π (U x) := rfl
  have ha (x y : V) : π (U (x + y)) = π (U x) + π (U y) := by
    rw [← map_add]
    apply (Submodule.Quotient.eq N).mpr
    change B (U (x + y) - (U x + U y)) = 0
    ext z
    simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.zero_apply]
    have hh := ht (x + y) z
    simp only [map_add, LinearMap.add_apply] at hh
    linarith [ht x z, ht y z]
  have hs (t : ℝ) (x : V) : π (U (t • x)) = t • π (U x) := by
    rw [← map_smul]
    apply (Submodule.Quotient.eq N).mpr
    change B (U (t • x) - t • U x) = 0
    ext z
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, LinearMap.zero_apply]
    have hh := ht (t • x) z
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at hh
    have hh' := congrArg (fun r : ℝ => t * r) (ht x z)
    nlinarith [hh']
  refine ⟨{ toFun := f
            map_add' := ?_
            map_smul' := ?_ }, hf⟩
  · intro x y
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    rw [← map_add, hf, hf, hf]
    exact ha x y
  · intro t x
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    rw [← map_smul, hf, hf]
    exact hs t x

-- proof_shape: bind-only; live consumer: original_models.
private theorem additive_label_real {W : Type*} [AddCommGroup W] [Module ℝ W]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (g : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : W →+ H)
    (hn : ∀ x, g x x = ‖f x‖ ^ 2) : ∀ (t : ℝ) (x : W), f (t • x) = t • f x := by
  intro t x
  let a : ℝ →+ H := AddMonoidHom.mk' (fun s => f (s • x)) (by
    intro s t; simp [add_smul, map_add])
  have hb (s : ℝ) : ‖a s‖ ≤ ‖f x‖ * ‖s‖ := by
    have he := hn (s • x)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hn] at he
    have hs : ‖s‖ ^ 2 = s ^ 2 := Real.norm_eq_abs s ▸ sq_abs s
    change ‖f (s • x)‖ ≤ ‖f x‖ * ‖s‖
    nlinarith [norm_nonneg (f (s • x)), norm_nonneg (f x), norm_nonneg s,
      mul_nonneg (norm_nonneg (f x)) (norm_nonneg s)]
  have hc : Continuous a := AddMonoidHomClass.continuous_of_bound a ‖f x‖ hb
  simpa [a] using map_real_smul a hc t (1 : ℝ)

/-- The original readout derives its actual radical quotient and a real-linear,
isometric three-phase marker there. Every original real-linear Hilbert model
factors through this same radical. -/
-- proof_shape: content; live consumer: original_models.
-- admission_basis: escape-witness; live raw lower-bound/Archimedean scalar construction.
theorem original_visible_quotient (U : V → V) (q : V → ℝ)
    (hq : ∀ x, 0 ≤ q x) (h : Balance U q) :
    ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
      (∀ x y, B x y = (q (x + y) - q (x - y)) / 4) ∧
      (∀ x y, B x y = B y x) ∧
      (∀ x, q x = q 0 + B x x) ∧
      (∀ x, B x x = 0 ↔ x ∈ B.ker) ∧
      ∃ (g : (V ⧸ B.ker) →ₗ[ℝ] (V ⧸ B.ker) →ₗ[ℝ] ℝ)
        (T : (V ⧸ B.ker) →ₗ[ℝ] (V ⧸ B.ker)),
        (∀ x y, g (B.ker.mkQ x) (B.ker.mkQ y) = B x y) ∧
        (∀ z, 0 ≤ g z z) ∧ (∀ z, g z z = 0 ↔ z = 0) ∧
        (∀ x, T (B.ker.mkQ x) = B.ker.mkQ (U x)) ∧
        (∀ z w, g (T z) (T w) = g z w) ∧
        (∀ z, z + T z + T (T z) = 0) ∧
        (∀ R : HilbertModel.{u, v} U q,
          ∃ F : (V ⧸ B.ker) →ₗ[ℝ] R.carrier, ∀ x, F (B.ker.mkQ x) = R.label x) := by
  obtain ⟨B, hb, hs, hd, hp, hi, ht, hv, hn, hc⟩ := raw_real_polar U q hq h
  let N := B.ker
  let π := N.mkQ
  have hN : N ≤ B.flip.ker := by
    intro x hx
    ext y
    change B y x = 0
    rw [hs]
    exact congrArg (fun f => f y) hx
  let g := B.liftQ₂ N N le_rfl hN
  have hg (x y : V) : g (π x) (π y) = B x y := rfl
  obtain ⟨T, hT⟩ := marker_descent B U ht
  refine ⟨B, hb, hs, hd, hn, g, T, hg, ?_, ?_, hT, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨x, rfl⟩ := N.mkQ_surjective z
    exact hp x
  · intro z
    obtain ⟨x, rfl⟩ := N.mkQ_surjective z
    rw [hg, hn]
    exact (Submodule.Quotient.mk_eq_zero N).symm
  · intro z w
    obtain ⟨x, rfl⟩ := N.mkQ_surjective z
    obtain ⟨y, rfl⟩ := N.mkQ_surjective w
    rw [hT, hT, hg, hg, hv]
  · intro z
    obtain ⟨x, rfl⟩ := N.mkQ_surjective z
    change B.ker.mkQ x + T (B.ker.mkQ x) + T (T (B.ker.mkQ x)) = 0
    simp only [hT]
    change π x + π (U x) + π (U (U x)) = 0
    rw [← map_add, ← map_add]
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hc x)
  · intro R
    have hker : N ≤ R.label.ker := by
      intro x hx
      have hbx : B x x = 0 := (hn x).mpr hx
      have hnorm : ‖R.label x‖ ^ 2 = 0 := by linarith [R.normSq x, hd x]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    exact ⟨N.liftQ R.label hker, fun _ => rfl⟩

-- proof_shape: bind-only; live consumer: original_models.
private theorem quotient_balance {W : Type*} [AddCommGroup W] [Module ℝ W]
    (g : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (T : W →ₗ[ℝ] W)
    (hs : ∀ x y, g x y = g y x)
    (hv : ∀ x y, g (T x) (T y) = g x y)
    (hc : ∀ x, x + T x + T (T x) = 0) :
    ∀ x y, g (x + y) (x + y) + g (x + T y) (x + T y) +
      g (x + T (T y)) (x + T (T y)) = 3 * g x x + 3 * g y y := by
  intro x y
  have hh := congrArg (fun z => g x z) (hc y)
  simp only [map_add, map_zero] at hh
  simp only [map_add, LinearMap.add_apply, hv]
  rw [hs y x, hs (T y) x, hs (T (T y)) x]
  linarith

-- proof_shape: bind-only; live consumer: original_models.
private def quotient_model (U : V → V) (q : V → ℝ)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (g : (V ⧸ B.ker) →ₗ[ℝ] (V ⧸ B.ker) →ₗ[ℝ] ℝ)
    (T : (V ⧸ B.ker) →ₗ[ℝ] (V ⧸ B.ker))
    (hg : ∀ x y, g (B.ker.mkQ x) (B.ker.mkQ y) = B x y)
    (hd : ∀ x, q x = q 0 + B x x)
    (hT : ∀ x, T (B.ker.mkQ x) = B.ker.mkQ (U x))
    (M : HilbertModel.{u, v} U q)
    (F : (V ⧸ B.ker) →ₗ[ℝ] M.carrier)
    (hF : ∀ x, F (B.ker.mkQ x) = M.label x) :
    HilbertRepresentation T.toAddMonoidHom (fun z => g z z) :=
        { carrier := M.carrier
          label := F.toAddMonoidHom
          normSq := by
            intro z
            obtain ⟨x, rfl⟩ := B.ker.mkQ_surjective z
            change g (B.ker.mkQ x) (B.ker.mkQ x) = ‖F (B.ker.mkQ x)‖ ^ 2
            rw [hg, hF]
            linarith [hd x, M.normSq x]
          phase := by
            intro z
            obtain ⟨x, rfl⟩ := B.ker.mkQ_surjective z
            change F (T (B.ker.mkQ x)) = omega • F (B.ker.mkQ x)
            rw [hT, hF, hF]
            exact M.phase x
          minimal := by
            have hrange : Set.range F.toAddMonoidHom = Set.range M.label := by
              ext z
              constructor
              · rintro ⟨x, rfl⟩
                obtain ⟨y, rfl⟩ := B.ker.mkQ_surjective x
                exact ⟨y, (hF y).symm⟩
              · rintro ⟨x, rfl⟩
                exact ⟨B.ker.mkQ x, hF x⟩
            rw [hrange]
            exact M.minimal }

-- proof_shape: content; live consumer: original_hilbert_characterization.
-- admission_basis: escape-witness; live raw lower-bound/Archimedean scalar construction.
private theorem original_models (U : V → V) (q : V → ℝ)
    (hq : ∀ x, 0 ≤ q x) (h : Balance U q) :
    Nonempty (HilbertModel.{u, u} U q) ∧
    (∀ (R : HilbertModel.{u, v} U q) (S : HilbertModel.{u, w} U q),
      ∃! e : R.carrier ≃ₗᵢ[ℂ] S.carrier, ∀ x, e (R.label x) = S.label x) ∧
    (∀ x, q 0 ≤ q x) := by
  classical
  obtain ⟨B, hb, hs, hd, hn, g, T, hg, hp, hdef, hT, hv, hc, hfactor⟩ :=
    original_visible_quotient.{u, v} U q hq h
  let N := B.ker
  let π := N.mkQ
  let f := fun z => g z z
  have hsym (z w : V ⧸ N) : g z w = g w z := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective z
    obtain ⟨y, rfl⟩ := N.mkQ_surjective w
    rw [hg, hg, hs]
  have hlaw := quotient_balance g T hsym hv hc
  have hsupplier := three_way_hilbert_characterization.{u, v, w} T.toAddMonoidHom f hp
  constructor
  · obtain ⟨R⟩ := hsupplier.1.mp hlaw
    let F : (V ⧸ N) →ₗ[ℝ] R.carrier :=
      { toFun := R.label
        map_add' := R.label.map_add
        map_smul' := additive_label_real g R.label R.normSq }
    refine ⟨{ carrier := R.carrier
              label := F.comp π
              normSq := ?_
              phase := ?_
              minimal := ?_ }⟩
    · intro x
      change q x = q 0 + ‖R.label (π x)‖ ^ 2
      rw [← R.normSq, show f (π x) = B x x from hg x x]
      exact hd x
    · intro x
      change R.label (π (U x)) = omega • R.label (π x)
      rw [← hT]
      exact R.phase (π x)
    · have hrange : Set.range (F.comp π) = Set.range R.label := by
        ext z
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨π x, rfl⟩
        · rintro ⟨x, rfl⟩
          obtain ⟨y, rfl⟩ := N.mkQ_surjective x
          exact ⟨y, rfl⟩
      rw [hrange]
      exact R.minimal
  · constructor
    · intro R S
      -- Both competing original models descend through the derived radical.
      have descent (M : HilbertModel.{u, v} U q) :
          ∃ F : (V ⧸ N) →ₗ[ℝ] M.carrier, ∀ x, F (π x) = M.label x := hfactor M
      obtain ⟨FR, hFR⟩ := descent R
      have hkerS : N ≤ S.label.ker := by
        intro x hx
        have hh := (hn x).mpr hx
        have hz : ‖S.label x‖ ^ 2 = 0 := by linarith [S.normSq x, hd x]
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
      let FS := N.liftQ S.label hkerS
      have hFS (x : V) : FS (π x) = S.label x := rfl
      let RR := quotient_model U q B g T hg hd hT R FR hFR
      let SS := quotient_model U q B g T hg hd hT S FS hFS
      obtain ⟨e, he, hu⟩ := (three_way_hilbert_characterization
        T.toAddMonoidHom f hp).2.2 RR SS
      refine ⟨e, ?_, ?_⟩
      · intro x
        have hh := he (π x)
        change e (FR (π x)) = FS (π x) at hh
        rw [hFR, hFS] at hh
        change e (R.label x) = S.label x at hh
        exact hh
      · intro e' he'
        apply hu e'
        intro z
        obtain ⟨x, rfl⟩ := N.mkQ_surjective z
        change e' (FR (π x)) = FS (π x)
        rw [hFR, hFS]
        exact he' x
    · intro x
      rw [hd x]
      exact le_add_of_nonneg_right (by rw [← hg x x]; exact hp _)

-- proof_shape: bind-only; live consumer: linear_balance.
private theorem norm_original_balance {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (x y : H) (t : ℝ) :
    ‖x + t • y‖ ^ 2 + ‖x + t • (omega • y)‖ ^ 2 +
      ‖t • (omega • x) + y‖ ^ 2 =
      2 * ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖t • x‖ ^ 2 + 2 * ‖t • y‖ ^ 2 := by
  have hm : conj omega * omega = 1 := by
    apply Complex.ext <;> simp [omega, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hs : 1 + omega + conj omega = 0 := by
    apply Complex.ext <;> simp [omega] <;> norm_num
  have hi : inner ℂ (x + t • y) (x + t • y) +
      inner ℂ (x + t • (omega • y)) (x + t • (omega • y)) +
      inner ℂ (t • (omega • x) + y) (t • (omega • x) + y) =
      (2 : ℂ) * inner ℂ x x + inner ℂ y y + inner ℂ (t • x) (t • x) +
        (2 : ℂ) * inner ℂ (t • y) (t • y) := by
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, RCLike.ofReal_eq_complex_ofReal, Complex.conj_ofReal]
    calc
      _ = (2 + (t : ℂ)^2 * (conj omega * omega)) * inner ℂ x x +
          (1 + (t : ℂ)^2 + (t : ℂ)^2 * (conj omega * omega)) * inner ℂ y y +
          (t : ℂ) * (1 + omega + conj omega) * inner ℂ x y +
          (t : ℂ) * (1 + omega + conj omega) * inner ℂ y x := by ring
      _ = _ := by rw [hs, hm]; ring
  have hn (z : H) : (inner ℂ z z).re = ‖z‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hh := congrArg Complex.re hi
  simp only [Complex.add_re, Complex.mul_re, hn] at hh
  norm_num at hh
  exact hh

/-- Original-domain converse for every complete minimal real-linear model. -/
-- proof_shape: bind-only; live consumer: original_hilbert_characterization.
private theorem linear_balance (U : V → V) (q : V → ℝ)
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F : V →ₗ[ℝ] H) (hFnorm : ∀ x, q x = q 0 + ‖F x‖ ^ 2)
    (hFphase : ∀ x, F (U x) = omega • F x) : Balance U q := by
  dsimp only [Balance]
  intro x y t
  have hn (x : V) : q x - q 0 = ‖F x‖ ^ 2 := by rw [hFnorm]; ring
  change (q (x + t • y) - q 0) + (q (x + t • U y) - q 0) +
      (q (t • U x + y) - q 0) =
      2 * (q x - q 0) + (q y - q 0) + (q (t • x) - q 0) +
        2 * (q (t • y) - q 0)
  simp only [hn, map_add, map_smul, hFphase]
  exact norm_original_balance (F x) (F y) t

-- proof_shape: bind-only; live consumer: original_hilbert_characterization.
private theorem model_balance (U : V → V) (q : V → ℝ)
    (R : HilbertModel.{u, v} U q) : Balance U q :=
  linear_balance U q R.label R.normSq R.phase

/-- The original arbitrary-marker relation is equivalent to a complete minimal
complex Hilbert model with original real-linear labels. All minimal original
models are uniquely related by a complex-linear label-preserving unitary, and
the retained baseline is the global minimum. -/
-- proof_shape: content; live consumer: original C140 Theorem 3.2.
-- admission_basis: escape-witness; live raw lower-bound/Archimedean scalar construction.
theorem original_hilbert_characterization (U : V → V) (q : V → ℝ)
    (hq : ∀ x, 0 ≤ q x) :
    (Balance U q ↔ Nonempty (HilbertModel.{u, u} U q)) ∧
    (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (F : V →ₗ[ℝ] H),
      (∀ x, q x = q 0 + ‖F x‖ ^ 2) →
      (∀ x, F (U x) = omega • F x) → Balance U q) ∧
    (∀ (R : HilbertModel.{u, v} U q) (S : HilbertModel.{u, w} U q),
      ∃! e : R.carrier ≃ₗᵢ[ℂ] S.carrier, ∀ x, e (R.label x) = S.label x) ∧
    (Balance U q → ∀ x, q 0 ≤ q x) := by
  refine ⟨⟨fun h => (original_models.{u, v, w} U q hq h).1,
    fun ⟨R⟩ => model_balance U q R⟩,
    fun H _ _ _ F hn hp => linear_balance U q F hn hp, ?_, ?_⟩
  · intro R S
    exact (original_models U q hq (model_balance U q R)).2.1 R S
  · intro h
    exact (original_models.{u, v, w} U q hq h).2.2

end D5.S3.QuadraticForms.RealThreePathRepresentation
