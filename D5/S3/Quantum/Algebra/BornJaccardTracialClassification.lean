/- GID: D5/S3/Quantum/Algebra/BornJaccardTracialClassification
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/BornJaccardTracialClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Born-weighted Jaccard distances satisfy every triangle exactly for tracial states. -/

import D5.S3.Combinatorics.Lattices.BadicaJaccardArbitraryLattices
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Module
import Mathlib.Analysis.InnerProductSpace.Positive

/-! Born trace weights on actual complex subspaces, including the zero-offset boundary. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace D5.S3.Quantum.Algebra.BornJaccardTracialClassification
open LinearMap ContinuousLinearMap
variable {n : ℕ}
/-- The usual complex Euclidean space of dimension n. -/
abbrev H (n : ℕ) := EuclideanSpace ℂ (Fin n)
/-- The actual orthogonal projection onto a linear subspace. -/
def projection (X : Submodule ℂ (H n)) : Module.End ℂ (H n) :=
  X.starProjection.toLinearMap
/-- The real trace pairing with the same state operator. -/
def weight (rho : Module.End ℂ (H n)) (X : Submodule ℂ (H n)) : ℝ :=
  (LinearMap.trace ℂ (H n) (rho * projection X)).re
/-- Meet-over-join Jaccard distance, with zero at a vanishing denominator. -/
def distance (rho : Module.End ℂ (H n)) (c : ℝ)
    (X Z : Submodule ℂ (H n)) : ℝ :=
  if c + weight rho (X ⊔ Z) = 0 then 0
  else 1 - (c + weight rho (X ⊓ Z)) / (c + weight rho (X ⊔ Z))

open D5.S3.Combinatorics.Lattices.BadicaJaccardArbitraryLattices
open Filter Topology
variable {L : Type*} [Lattice L]

private theorem modular_positive_triangle (f : L → ℝ) (hp : ∀ X, 0 < f X)
    (hm : Monotone f) (hmod : ∀ X Y, f (X ⊔ Y) + f (X ⊓ Y) = f X + f Y) :
    ∀ X Y Z, jaccardDist f X Z ≤ jaccardDist f X Y + jaccardDist f Y Z := by
  apply result L f hp hm
  · intro X Y
    exact le_of_eq (hmod X Y).symm
  · refine ⟨hp, ?_⟩
    intro X Y
    change Real.log (f (X ⊔ Y)) + Real.log (f (X ⊓ Y)) ≤
      Real.log (f X) + Real.log (f Y)
    rw [← Real.log_mul (ne_of_gt (hp _)) (ne_of_gt (hp _)),
      ← Real.log_mul (ne_of_gt (hp _)) (ne_of_gt (hp _))]
    apply (Real.log_le_log_iff (mul_pos (hp _) (hp _)) (mul_pos (hp _) (hp _))).2
    have hprod := mul_nonneg (sub_nonneg.mpr (hm (inf_le_left : X ⊓ Y ≤ X)))
      (sub_nonneg.mpr (hm (inf_le_right : X ⊓ Y ≤ Y)))
    nlinarith [congrArg (fun t : ℝ => t * f (X ⊓ Y)) (hmod X Y)]

private def jd (f : L → ℝ) (X Z : L) : ℝ :=
  if f (X ⊔ Z) = 0 then 0 else jaccardDist f X Z

private theorem shifted_jd_limit (f : L → ℝ) (hn : ∀ X, 0 ≤ f X)
    (hm : Monotone f) (X Z : L) :
    Tendsto (fun e : ℝ => jaccardDist (fun A => e + f A) X Z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (jd f X Z)) := by
  by_cases hz : f (X ⊔ Z) = 0
  · have hi : f (X ⊓ Z) = 0 := le_antisymm
      ((hm (inf_le_left.trans le_sup_left)).trans hz.le) (hn _)
    have heq : (fun e : ℝ => jaccardDist (fun A => e + f A) X Z) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with e he
      have he0 : e ≠ 0 := ne_of_gt he
      simp [jaccardDist, hz, hi, he0]
    simpa [jd, hz] using tendsto_const_nhds.congr' heq.symm
  · have he : Tendsto (fun e : ℝ => e) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left inf_le_left
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((he.add_const (f (X ⊓ Z))).div (he.add_const (f (X ⊔ Z))) (by simpa using hz))
    simpa [jaccardDist, jd, hz] using hh

private theorem modular_nonnegative_triangle (f : L → ℝ) (hn : ∀ X, 0 ≤ f X)
    (hm : Monotone f) (hmod : ∀ X Y, f (X ⊔ Y) + f (X ⊓ Y) = f X + f Y)
    (X Y Z : L) : jd f X Z ≤ jd f X Y + jd f Y Z := by
  have hi : ∀ᶠ e : ℝ in nhdsWithin 0 (Set.Ioi 0),
      jaccardDist (fun A => e + f A) X Z ≤
        jaccardDist (fun A => e + f A) X Y + jaccardDist (fun A => e + f A) Y Z := by
    filter_upwards [self_mem_nhdsWithin] with e he
    apply modular_positive_triangle (fun A => e + f A)
    · intro A
      exact add_pos_of_pos_of_nonneg he (hn A)
    · intro A B hAB
      dsimp
      linarith [hm hAB]
    · intro A B
      linarith [hmod A B]
  exact le_of_tendsto_of_tendsto (shifted_jd_limit f hn hm X Z)
    ((shifted_jd_limit f hn hm X Y).add (shifted_jd_limit f hn hm Y Z)) hi

private theorem scalar_triangle (hn : 2 ≤ n) (c : ℝ) (hc : 0 ≤ c) (X Y Z : Submodule ℂ (H n)) :
    distance (((n : ℂ)⁻¹) • (1 : Module.End ℂ (H n))) c X Z ≤
      distance (((n : ℂ)⁻¹) • (1 : Module.End ℂ (H n))) c X Y +
      distance (((n : ℂ)⁻¹) • (1 : Module.End ℂ (H n))) c Y Z := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let f : Submodule ℂ (H n) → ℝ := fun A => c + (Module.finrank ℂ A : ℝ) / n
  have hf : ∀ A, 0 ≤ f A := fun A => add_nonneg hc (div_nonneg (Nat.cast_nonneg _) hn0.le)
  have hm : Monotone f := by
    intro A B hAB
    have hd : (Module.finrank ℂ A : ℝ) ≤ (Module.finrank ℂ B : ℝ) := by
      exact_mod_cast Submodule.finrank_mono hAB
    dsimp [f]
    linarith [div_le_div_of_nonneg_right hd hn0.le]
  have hmod : ∀ A B, f (A ⊔ B) + f (A ⊓ B) = f A + f B := by
    intro A B
    have h := Submodule.finrank_sup_add_finrank_inf_eq A B
    have hr : (Module.finrank ℂ ↥(A ⊔ B) : ℝ) + Module.finrank ℂ ↥(A ⊓ B) =
      Module.finrank ℂ A + Module.finrank ℂ B := by exact_mod_cast h
    dsimp [f]
    linear_combination hr / (n : ℝ)
  have hscalar (A : Submodule ℂ (H n)) :
      weight (((n : ℂ)⁻¹) • (1 : Module.End ℂ (H n))) A =
        (Module.finrank ℂ A : ℝ) / n := by
    have ht : LinearMap.trace ℂ (H n) (projection A) = (Module.finrank ℂ A : ℂ) := by
      have hp : LinearMap.IsProj A (projection A) :=
        ⟨fun x => (A.orthogonalProjectionOnto x).property,
        fun x hx => Submodule.starProjection_eq_self_iff.mpr hx⟩
      exact hp.trace
    simp only [weight, smul_mul_assoc, one_mul, map_smul, ht, smul_eq_mul,
      ← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re, div_eq_mul_inv, mul_comm]
  simpa [distance, jd, jaccardDist, f, hscalar] using
    modular_nonnegative_triangle f hf hm hmod X Y Z


private theorem weight_eq_sum (rho : Module.End ℂ (H n))
    (X : Submodule ℂ (H n))
    (b : OrthonormalBasis (Fin (Module.finrank ℂ X)) ℂ X) :
    weight rho X = ∑ i, (inner ℂ (b i : H n) (rho (b i : H n))).re := by
  change (LinearMap.trace ℂ (H n)
    ((rho ∘ₗ X.subtype) ∘ₗ X.orthogonalProjectionOnto.toLinearMap)).re = _
  rw [LinearMap.trace_comp_comm', LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact X.inner_orthogonalProjectionOnto_eq_of_mem_left (b i) (rho (b i))

theorem weight_nonneg (rho : Module.End ℂ (H n))
    (hp : ∀ v : H n, 0 ≤ (inner ℂ v (rho v)).re) (X : Submodule ℂ (H n)) :
    0 ≤ weight rho X := by
  rw [weight_eq_sum rho X (stdOrthonormalBasis ℂ X)]
  exact Finset.sum_nonneg fun i _ => hp _

private theorem weight_pos (rho : Module.End ℂ (H n))
    (hp : ∀ v : H n, v ≠ 0 → 0 < (inner ℂ v (rho v)).re)
    (X : Submodule ℂ (H n)) (hX : X ≠ ⊥) : 0 < weight rho X := by
  have hd : 0 < Module.finrank ℂ X :=
    Nat.pos_of_ne_zero (fun h => hX (Submodule.finrank_eq_zero.mp h))
  letI : Nonempty (Fin (Module.finrank ℂ X)) := Fin.pos_iff_nonempty.mp hd
  rw [weight_eq_sum rho X (stdOrthonormalBasis ℂ X)]
  apply Finset.sum_pos
  · intro i _
    apply hp
    exact_mod_cast (stdOrthonormalBasis ℂ X).toBasis.ne_zero i
  · exact Finset.univ_nonempty

private theorem projection_injective :
    Function.Injective (projection (n := n)) := by
  intro X Z h
  apply Submodule.starProjection_inj.mp
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun f : Module.End ℂ (H n) => f v) h

private theorem weight_strictMono (rho : Module.End ℂ (H n))
    (hp : ∀ v : H n, v ≠ 0 → 0 < (inner ℂ v (rho v)).re) :
    StrictMono (weight rho) := by
  intro X Z hXZ
  have hproj : (projection Z - projection X).IsSymmetricProjection := by
    apply (Submodule.isSymmetricProjection_starProjection X).sub_of_range_le_range
      (Submodule.isSymmetricProjection_starProjection Z)
    simpa only [Submodule.range_starProjection] using hXZ.le
  obtain ⟨U, hU, heq⟩ :=
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection.mp hproj
  have hUn : U ≠ ⊥ := by
    intro hz
    have hP : projection Z = projection X := by
      apply sub_eq_zero.mp
      rw [heq]
      apply LinearMap.ext
      intro v
      have hv : U.starProjection v ∈ U := (U.orthogonalProjectionOnto v).property
      change U.starProjection v = (0 : H n)
      simpa only [Submodule.mem_bot] using ((le_of_eq hz : U ≤ ⊥) hv)
    exact hXZ.ne (projection_injective hP).symm
  have hpos := weight_pos rho hp U hUn
  have hw : weight rho Z - weight rho X = weight rho U := by
    unfold weight
    rw [← Complex.sub_re, ← map_sub, ← mul_sub, heq]
    rfl
  linarith

private theorem faithful_separation (rho : Module.End ℂ (H n))
    (hp : ∀ v : H n, v ≠ 0 → 0 < (inner ℂ v (rho v)).re)
    (c : ℝ) (hc : 0 ≤ c) (X Z : Submodule ℂ (H n)) :
    distance rho c X Z = 0 ↔ X = Z := by
  have hnon : ∀ v : H n, 0 ≤ (inner ℂ v (rho v)).re := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hp v hv).le
  have hw := weight_nonneg rho hnon
  have hm := (weight_strictMono rho hp).monotone
  by_cases hden : c + weight rho (X ⊔ Z) = 0
  · have hzero : weight rho (X ⊔ Z) = 0 := by linarith [hw (X ⊔ Z)]
    have hbot : X ⊔ Z = ⊥ := by
      by_contra hb
      linarith [weight_pos rho hp (X ⊔ Z) hb]
    have hX : X = ⊥ := le_antisymm (hbot ▸ le_sup_left) bot_le
    have hZ : Z = ⊥ := le_antisymm (hbot ▸ le_sup_right) bot_le
    exact iff_of_true (by simp only [distance, ite_eq_left hden]) (hX.trans hZ.symm)
  · constructor
    · intro hd
      have hfrac : (c + weight rho (X ⊓ Z)) / (c + weight rho (X ⊔ Z)) = 1 := by
        simp only [distance, ite_eq_right hden] at hd
        linarith
      have heq : weight rho (X ⊓ Z) = weight rho (X ⊔ Z) := by
        have hh := (div_eq_one_iff_eq hden).mp hfrac
        linarith
      have hxz : X ⊓ Z = X ⊔ Z := by
        by_contra hne
        have hlt := weight_strictMono rho hp (lt_of_le_of_ne inf_le_sup hne)
        linarith
      exact le_antisymm
        ((le_sup_left : X ≤ X ⊔ Z).trans (hxz ▸ inf_le_right))
        ((le_sup_right : Z ≤ X ⊔ Z).trans (hxz ▸ inf_le_left))
    · rintro rfl
      simp only [distance, sup_idem, inf_idem]
      split_ifs with hz
      · rfl
      · simp [div_self hz]



theorem native_matrix_faithfulness
    (rho : Matrix (Fin n) (Fin n) ℂ) (hp : rho.PosDef)
    (v : H n) (hv : v ≠ 0) :
    0 < (inner ℂ v (rho.toEuclideanLin v)).re := by
  have hv' : WithLp.ofLp v ≠ 0 := by
    intro h
    apply hv
    exact (WithLp.ofLp_injective 2) (by simpa using h)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, WithLp.ofLp_toLp, dotProduct_comm,
    RCLike.re_to_complex] using hp.re_dotProduct_pos hv'

private theorem distance_properties (rho : Module.End ℂ (H n))
    (hp : ∀ v : H n, v ≠ 0 → 0 < (inner ℂ v (rho v)).re)
    (c : ℝ) (hc : 0 ≤ c) :
    (∀ X Z, 0 ≤ distance rho c X Z ∧ distance rho c X Z ≤ 1) ∧
    (∀ X Z, distance rho c X Z = distance rho c Z X) ∧
    (∀ X, distance rho c X X = 0) := by
  have hnon : ∀ v : H n, 0 ≤ (inner ℂ v (rho v)).re := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hp v hv).le
  have hw := weight_nonneg rho hnon
  have hm := (weight_strictMono rho hp).monotone
  refine ⟨?_, ?_, ?_⟩
  · intro X Z
    unfold distance
    split_ifs with hz
    · norm_num
    · have hd : 0 < c + weight rho (X ⊔ Z) := lt_of_le_of_ne
        (add_nonneg hc (hw _)) (Ne.symm hz)
      have hi : 0 ≤ c + weight rho (X ⊓ Z) := add_nonneg hc (hw _)
      have hle : c + weight rho (X ⊓ Z) ≤ c + weight rho (X ⊔ Z) := by
        linarith [hm (inf_le_sup : X ⊓ Z ≤ X ⊔ Z)]
      constructor
      · exact sub_nonneg.mpr ((div_le_one hd).mpr hle)
      · linarith [div_nonneg hi hd.le]
  · intro X Z
    simp only [distance, sup_comm X Z, inf_comm X Z]
  · intro X
    exact (faithful_separation rho hp c hc X X).mpr rfl



theorem trace_mul_rank (rho : Module.End ℂ (H n)) (u v : H n) :
    LinearMap.trace ℂ (H n) (rho * (InnerProductSpace.rankOne ℂ u v).toLinearMap) =
      inner ℂ v (rho u) := by
  have heq : rho * (InnerProductSpace.rankOne ℂ u v).toLinearMap =
      (innerₛₗ ℂ v).smulRight (rho u) := by
    ext w
    simp [Module.End.mul_apply, InnerProductSpace.rankOne_apply]
  rw [heq, LinearMap.trace_smulRight]
  rfl

private theorem projection_pair (e f : H n)
    (hee : inner ℂ e e = 1) (hff : inner ℂ f f = 1)
    (hef : inner ℂ e f = 0) :
    projection ((ℂ ∙ e) ⊔ (ℂ ∙ f)) =
      (InnerProductSpace.rankOne ℂ e e).toLinearMap +
      (InnerProductSpace.rankOne ℂ f f).toLinearMap := by
  classical
  have hfe : inner ℂ f e = 0 := by rw [← inner_conj_symm, hef, map_zero]
  let v : Bool → H n := fun i => if i then e else f
  have hv : Orthonormal ℂ v := orthonormal_iff_ite.mpr (by
    intro i j
    cases i <;> cases j
    · exact hff
    · exact hfe
    · exact hef
    · exact hee)
  have hh := (OrthonormalBasis.span hv Finset.univ).starProjection_eq_sum_rankOne
  simp only [OrthonormalBasis.span_apply] at hh
  rw [Finset.sum_coe_sort (s := (Finset.univ : Finset Bool))
    (f := fun i : Bool => InnerProductSpace.rankOne ℂ (v i) (v i))] at hh
  have hS : Submodule.span ℂ (↑(Finset.univ.image v) : Set (H n)) =
      (ℂ ∙ e) ⊔ (ℂ ∙ f) := by
    simp [v, Fintype.univ_bool, Submodule.span_insert, sup_comm]
  simp only [hS] at hh
  have hx := congrArg ContinuousLinearMap.toLinearMap hh
  simpa [projection, v, Fintype.sum_bool, add_comm] using hx


private theorem weight_line_five (rho : Module.End ℂ (H n)) (w : H n)
    (hw : inner ℂ w w = 5) :
    weight rho (ℂ ∙ w) = (inner ℂ w (rho w)).re / 5 := by
  have hn : ‖w‖ ^ 2 = (5 : ℝ) := by
    rw [inner_self_eq_norm_sq_to_K] at hw
    have hr := congrArg Complex.re hw
    norm_num [pow_two, Complex.mul_re] at hr
    nlinarith
  have hP : projection (ℂ ∙ w) =
      (5 : ℂ)⁻¹ • (InnerProductSpace.rankOne ℂ w w).toLinearMap := by
    apply LinearMap.ext
    intro v
    simp [projection, Submodule.starProjection_singleton, hn,
      InnerProductSpace.rankOne_apply, smul_smul, div_eq_mul_inv, mul_comm]
  rw [weight, hP, mul_smul_comm, map_smul, trace_mul_rank]
  norm_num [smul_eq_mul, Complex.mul_re, div_eq_mul_inv]
  ring

private theorem unequal_pair_obstruction
    (rho : Module.End ℂ (H n)) (e f : H n)
    (hee : inner ℂ e e = 1) (hff : inner ℂ f f = 1) (hef : inner ℂ e f = 0)
    (M m : ℝ) (hM : rho e = (M : ℂ) • e) (hm : rho f = (m : ℂ) • f)
    (hm0 : 0 < m) (hmM : m < M) (c : ℝ) (hc : 0 ≤ c) :
    ∃ X Y Z : Submodule ℂ (H n),
      distance rho c X Z > distance rho c X Y + distance rho c Y Z := by
  have hfe : inner ℂ f e = 0 := by rw [← inner_conj_symm, hef, map_zero]
  let u : H n := (2 : ℂ) • e + f
  let v : H n := (2 : ℂ) • e - f
  let L : Submodule ℂ (H n) := ℂ ∙ u
  let N : Submodule ℂ (H n) := ℂ ∙ v
  let T : Submodule ℂ (H n) := (ℂ ∙ e) ⊔ (ℂ ∙ f)
  have hu : inner ℂ u u = 5 := by
    simp only [u, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, hee, hff, hef, hfe]
    norm_num [map_ofNat]
  have hv : inner ℂ v v = 5 := by
    simp only [v, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, hee, hff, hef, hfe]
    norm_num [map_ofNat]
  have hLT : L ≤ T := by
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact T.add_mem
      (Submodule.mem_sup_left ((ℂ ∙ e).smul_mem 2 (Submodule.mem_span_singleton_self e)))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self f))
  have hNT : N ≤ T := by
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact T.sub_mem
      (Submodule.mem_sup_left ((ℂ ∙ e).smul_mem 2 (Submodule.mem_span_singleton_self e)))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self f))
  have hjoin : L ⊔ N = T := by
    apply le_antisymm (sup_le hLT hNT)
    apply sup_le
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      have h := (L ⊔ N).smul_mem (1 / 4 : ℂ)
        ((L ⊔ N).add_mem
          (Submodule.mem_sup_left (Submodule.mem_span_singleton_self u))
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
      convert h using 1
      dsimp [u, v]
      module
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      have h := (L ⊔ N).smul_mem (1 / 2 : ℂ)
        ((L ⊔ N).sub_mem
          (Submodule.mem_sup_left (Submodule.mem_span_singleton_self u))
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
      convert h using 1
      dsimp [u, v]
      module
  have hinf : L ⊓ N = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rcases Submodule.mem_span_singleton.mp hx.1 with ⟨a, ha⟩
    rcases Submodule.mem_span_singleton.mp hx.2 with ⟨b, hb⟩
    have heq := ha.trans hb.symm
    have h1 := congrArg (fun w : H n => inner ℂ e w) heq
    have h2 := congrArg (fun w : H n => inner ℂ f w) heq
    simp only [u, v, inner_add_right, inner_sub_right, inner_smul_right,
      hee, hff, hef, hfe, mul_one, mul_zero, add_zero, zero_add, sub_zero] at h1 h2
    have ha0 : a = 0 := by linear_combination h1 / 4 + h2 / 2
    have hx0 : x = 0 := by rw [← ha, ha0, zero_smul]
    simpa only [Submodule.mem_bot] using hx0
  have hweightL : weight rho L = (4 * M + m) / 5 := by
    rw [weight_line_five rho u hu]
    simp only [u, map_add, map_smul, hM, hm, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, hee, hff, hef, hfe]
    norm_num [Complex.mul_re, Complex.add_re]
    ring
  have hweightN : weight rho N = (4 * M + m) / 5 := by
    rw [weight_line_five rho v hv]
    simp only [v, map_sub, map_smul, hM, hm, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, hee, hff, hef, hfe]
    norm_num [Complex.mul_re, Complex.sub_re]
    ring
  have hweightT : weight rho T = M + m := by
    rw [weight, projection_pair e f hee hff hef, mul_add, map_add,
      trace_mul_rank, trace_mul_rank, Complex.add_re]
    simp only [hM, hm, inner_smul_right, hee, hff, mul_one, Complex.ofReal_re]
  have hbot : weight rho (⊥ : Submodule ℂ (H n)) = 0 := by
    simp [weight, projection]
  have hden : 0 < c + (M + m) := by linarith
  have hdef : distance rho c L N - distance rho c L T - distance rho c T N =
      (3 * (M - m) / 5) / (c + (M + m)) := by
    simp only [distance, hjoin, hinf, sup_eq_right.mpr hLT,
      inf_eq_left.mpr hLT, sup_eq_left.mpr hNT, inf_eq_right.mpr hNT,
      hbot, hweightL, hweightN, hweightT, if_neg (ne_of_gt hden)]
    field_simp
    ring
  refine ⟨L, T, N, ?_⟩
  have hpos : 0 < (3 * (M - m) / 5) / (c + (M + m)) :=
    div_pos (div_pos (mul_pos (by norm_num) (sub_pos.mpr hmM)) (by norm_num)) hden
  linarith


private theorem operator_classification (hn : 2 ≤ n)
    (rho : Module.End ℂ (H n)) (hsym : rho.IsSymmetric)
    (hp : ∀ v : H n, v ≠ 0 → 0 < (inner ℂ v (rho v)).re)
    (ht : LinearMap.trace ℂ (H n) rho = 1) (c : ℝ) (hc : 0 ≤ c) :
    (∀ X Y Z : Submodule ℂ (H n),
      distance rho c X Z ≤ distance rho c X Y + distance rho c Y Z) ↔
      rho = (n : ℂ)⁻¹ • (1 : Module.End ℂ (H n)) := by
  constructor
  · intro htri
    let b := hsym.eigenvectorBasis (show Module.finrank ℂ (H n) = n by simp [H])
    let lam := hsym.eigenvalues (show Module.finrank ℂ (H n) = n by simp [H])
    have heig (i : Fin n) : rho (b i) = (lam i : ℂ) • b i :=
      hsym.apply_eigenvectorBasis _ i
    have hlam (i : Fin n) : 0 < lam i := by
      have h := hp (b i) (b.toBasis.ne_zero i)
      rw [heig] at h
      simpa only [inner_smul_right, b.inner_eq_one, mul_one, Complex.ofReal_re] using h
    have hle (i j : Fin n) : lam i ≤ lam j := by
      by_contra h
      have hlt : lam j < lam i := lt_of_not_ge h
      have hij : i ≠ j := by rintro rfl; exact (lt_irrefl _ hlt)
      obtain ⟨X, Y, Z, hbad⟩ := unequal_pair_obstruction rho (b i) (b j)
        (b.inner_eq_one i) (b.inner_eq_one j) (b.inner_eq_zero hij)
        (lam i) (lam j) (heig i) (heig j) (hlam j) hlt c hc
      linarith [htri X Y Z]
    have hall (i j : Fin n) : lam i = lam j := le_antisymm (hle i j) (hle j i)
    let i0 : Fin n := ⟨0, by omega⟩
    have hs : rho = (lam i0 : ℂ) • (1 : Module.End ℂ (H n)) := by
      apply b.toBasis.ext
      intro i
      change rho (b i) = ((lam i0 : ℂ) • (1 : Module.End ℂ (H n))) (b i)
      rw [heig, hall i i0]
      rfl
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have htrace : (lam i0 : ℂ) * (n : ℂ) = 1 := by
      simpa only [hs, map_smul, LinearMap.trace_one, finrank_euclideanSpace, Fintype.card_fin,
        smul_eq_mul] using ht
    have hval : (lam i0 : ℂ) = (n : ℂ)⁻¹ := by
      calc
        (lam i0 : ℂ) = ((lam i0 : ℂ) * n) * (n : ℂ)⁻¹ := by field_simp
        _ = (n : ℂ)⁻¹ := by rw [htrace, one_mul]
    rw [hs, hval]
  · rintro rfl
    exact scalar_triangle hn c hc

private theorem metric_of_triangle (rho : Module.End ℂ (H n))
    (hp : ∀ v : H n, v ≠ 0 → 0 < (inner ℂ v (rho v)).re)
    (c : ℝ) (hc : 0 ≤ c)
    (htri : ∀ X Y Z : Submodule ℂ (H n),
      distance rho c X Z ≤ distance rho c X Y + distance rho c Y Z) :
    ∃ m : MetricSpace (Submodule ℂ (H n)),
      ∀ X Z, @dist _ m.toDist X Z = distance rho c X Z := by
  obtain ⟨_, hcomm, hself⟩ := distance_properties rho hp c hc
  let m : MetricSpace (Submodule ℂ (H n)) := {
    dist := distance rho c
    dist_self := hself
    dist_comm := hcomm
    dist_triangle := htri
    eq_of_dist_eq_zero := fun {X Z} h => (faithful_separation rho hp c hc X Z).mp h }
  exact ⟨m, fun _ _ => rfl⟩

/-- Tracial classification, metricity and faithful separation on the full native
subspace lattice. -/
theorem tracial_classification (hn : 2 ≤ n)
    (rho : Matrix (Fin n) (Fin n) ℂ) (hp : rho.PosDef) (ht : Matrix.trace rho = 1)
    (c : ℝ) (hc : 0 ≤ c) :
    ((∀ X Y Z : Submodule ℂ (H n),
        distance rho.toEuclideanLin c X Z ≤
          distance rho.toEuclideanLin c X Y + distance rho.toEuclideanLin c Y Z) ↔
      rho = (n : ℂ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ)) ∧
    (rho = (n : ℂ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ) →
      ∃ m : MetricSpace (Submodule ℂ (H n)),
        ∀ X Z, @dist _ m.toDist X Z = distance rho.toEuclideanLin c X Z) ∧
    (∀ X Z : Submodule ℂ (H n), distance rho.toEuclideanLin c X Z = 0 ↔ X = Z) := by
  have hfaith := native_matrix_faithfulness rho hp
  have htrace : LinearMap.trace ℂ (H n) rho.toEuclideanLin = 1 := by
    simpa only [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq] using ht
  have hone : Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℂ) =
      (1 : Module.End ℂ (H n)) := by
    simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_one,
      Module.End.one_eq_id]
  have hscalar : rho.toEuclideanLin = (n : ℂ)⁻¹ • (1 : Module.End ℂ (H n)) ↔
      rho = (n : ℂ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    constructor
    · intro h
      apply Matrix.toEuclideanLin.injective
      simpa only [map_smul, hone] using h
    · intro h
      rw [h, map_smul, hone]
  have hi := (operator_classification hn rho.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hp.isHermitian) hfaith htrace c hc).trans hscalar
  exact ⟨hi, fun h => metric_of_triangle _ hfaith c hc (hi.mpr h),
    faithful_separation _ hfaith c hc⟩


#print axioms tracial_classification

end D5.S3.Quantum.Algebra.BornJaccardTracialClassification
