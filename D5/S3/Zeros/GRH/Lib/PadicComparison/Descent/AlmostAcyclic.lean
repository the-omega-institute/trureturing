/- GID: D5/S3/Zeros/GRH/Lib/PadicComparison/Descent/AlmostAcyclic
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicComparison/Descent/AlmostAcyclic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicComparison.Descent.AlmostAcyclic. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicComparison/Descent/AlmostAcyclic.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicComparison.Descent.VDescent
import D5.S3.Zeros.GRH.Lib.PadicComparison.Crystalline.PeriodLifting
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Almost acyclicity of the structure sheaf for the v-topology. It is stated here for
any perfect algebra over the tilt of O_C, as cohomology on products of complete absolutely
integrally closed valuation rings, modulo p♭. The maximal ideal is put into the coefficients so that
the result is exact, and the proof passes to a valuation ring. Source: P. Scholze, Étale cohomology
of diamonds, arXiv 1709.07343 (2017), Theorem 8.7, Proposition 8.8; for perfect rings B. Bhatt, P.
Scholze, Projectivity of the Witt vector affine Grassmannian, Invent. Math. 209 (2017), Theorem 4.1;
for the points argument O. Gabber, S. Kelly, Points in algebraic geometry, J. Pure Appl. Algebra 219
(2015), Theorem 2.3.

This file: Almost acyclicity of the tilted structure sheaf for perfect algebras on p-adic tests. -/


open CategoryTheory ObjectProperty TensorProduct Function Comparison freeAb Category PadicTest
  IsCohomEquiv Eqv
variable {C C' D} [Category C] [Category C'] [Category D] {F : AbFunctor C} {F' : AbFunctor C'} {G :
  AbFunctor D} {p} [ThePrime p] {N} [AddCommGroup N] [Module OFlat N] (hN : ∀ x : N, pFlat • x = 0)

/-- Let c, c' be comparisons from F, F' to G, with u: Y → h_B, v: Y → h_B' over them, and γ:
F(B) → F'(B') a bijection such that x and γx give the same section of G at each point of Y.
If c is bijective along u, then c' is along v. -/
lemma Comparison.IsBijective.transfer {Y B B'} {c : Comparison F G} {c' : Comparison F' G} {u :
  Y ⟶ _ ⋙ reprBy B} {v : Y ⟶ _ ⋙ reprBy B'} (k : c.IsBijective (freeAbMap u)) {γ} (hγ :
  Bijective γ) (h : ∀ A f x, c.coeffHom A (F.map (u A f).1 x) = c'.coeffHom A (F'.map (v A f).1
  (γ x)) := by aesop) : c'.IsBijective (freeAbMap v) := by rwa [isBijective_reprBy_iff,
  ← bijective_iff_of_comm_sq (fun _ ↦ hom_ext ?_) hγ bijective_id] at *; simp [homOfValue_app, h]

/-- For every perfect O^♭-algebra b, restriction along tilting identifies the cohomology of
Hom(b, S^♭) on p-adic tests S, coefficients F(S^♭), with that of h_b: F(b) in degree 0. -/
abbrev IsAcyclicOnPerfect F := ∀ (b : CommAlg _) [PerfectRing b p], IsAcyclicAt tilt F b

include hN

/-- Almost descent. Let N be an O^♭-module killed by π (`pFlat`) and b a perfect
O^♭-algebra. On p-adic tests S, Hom(b, S^♭) with coefficients S^♭ ⊗ N ⊗ 𝔪 has cohomology b ⊗
N ⊗ 𝔪, in degree 0; 𝔪 is the maximal ideal. -/
lemma isAcyclicAt_perfectTilt b : IsAcyclicAt perfectTilt (ι _ ⋙ moduleCoeff (almostCoeff N)) b :=
  forall_bijective_iff_bijectiveUpTo.2 (·.rec (by tauto) (fun _ ih b ↦
  (show ∃ b' y, _ ∧ IsAcyclicAt _ _ b' by
  obtain h | ⟨@⟨c, f⟩⟩ := isEmpty_or_nonempty (tilt ⋙ reprBy b.1).Elements
  use ⟨.of _ Unit, ⟨by simp⟩⟩, (by use! default),
    (h.elim <| Functor.elementsMk _ · ⟨·.1.1⟩), isBijective_reprBy_iff.2
    ⟨⟨@injective_of_subsingleton (ULift (Unit ⊗ _)) _ _ _, fun _ ↦ ⟨0, ?_⟩⟩, fun _ ↦
    _root_.H.subsingleton_of_id_eq_zero ?_ ..⟩
    <;> exact hom_ext (h.elim <| Functor.elementsMk _ · ⟨(by use! default) ≫ ·.1.1⟩)
  let ⟨_, _, hy⟩ := HasCoveringPoints.exists_surjective_point _ (homTiltIso.1.1 c f)
  exact ⟨_, ⟨_⟩, fun d f ↦ ((surjective_of_epi (homTiltIso.2.1 _)).comp (hy d) ⟨_⟩).elim
    (⟨⟨perfectTilt.map ·.1⟩, congr(⟨⟨$((homTiltIso.2.naturality_apply ..).symm.trans ·).1⟩⟩)⟩),
    isBijective_of_repr _ (pointMap_id_bijective_of_fullyFaithful
    (lift ..) _) (ConcreteCategory.bijective_of_isIso ((moduleCoeff _).map (𝟙 _)))⟩).elim fun _ ⟨y,
  h, H⟩ ↦ bijectiveUpTo_of_cech_pred rfl (isCover_of_points hN _ h) h.isCover H
  (exists_repr_cech y · |>.elim fun D ⟨_, e⟩ ↦
  (bijectiveUpTo_congr (comp_id _) (of_bijective e) (of_bijective (by tauto))).2 (ih D))) b)

/-- Almost descent: if π = ξ mod p kills the O^♭-module N and b is a perfect O^♭-algebra, then
on p-adic tests S the functor Hom(b, S^♭) with coefficients S^♭ ⊗ N ⊗ 𝔪 has cohomology b ⊗ N
⊗ 𝔪, in degree 0.

Known result: Almost acyclicity of the structure sheaf for the v-topology. -/
lemma isAcyclicAt_almostCoeff : IsAcyclicOnPerfect (moduleCoeff (almostCoeff N)) := fun b h ↦
  .transfer (.precomp_of_bijective (isAcyclicAt_perfectTilt hN ⟨b, h⟩) (.mk fun _ ↦
  ↾(⟨⟨·.1⟩⟩)) rfl fun _ ↦ (Equiv.mk _ (⟨·.1.1⟩)).bijective) bijective_id (by tauto)
