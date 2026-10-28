/- GID: D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Rank-three nonmodular matroids have nonzero J-Moebius value at minus one. -/
/- admission_basis: open-problem-resolution (#19762; Proved)
   Direct frozen dependencies: none.
   Escape audit: unfinished; https://github.com/the-omega-institute/trureturing/issues/21453.
   Module escape_witness: none; the settling result uses open-problem-resolution.
   The literal source definitions and claim are retained; the proofs use ordinary
   Mobius inversion and finite-configuration theorems from pinned Mathlib.
   Flats: proof_shape: bind-only; escape_witness: none; consumers: IsJFunction,Lines,MoebiusPoly,Points,bottomFlat,bottom_le,claim,distinct_points_join_rank_two,distinct_points_unique_line,eq_of_le_rk_eq,eval_as_mu_sum,exists_line_misses_point,exists_point_outside,inter_isFlat,j_eq_mu_product,joinFlat,join_le,le_join_left,le_join_right,le_meet,le_top,meetFlat,meet_le_left,meet_le_right,moebius_eval_neg_one,mu_isJ,nonmodular_disjoint_lines,nonmodular_more_lines,point_of_element_outside,rankThreeFrame,result,rk_join_le,rk_lt_of_lt,topFlat.
   rk: proof_shape: bind-only; escape_witness: none; consumers: Lines,MoebiusPoly,Points,distinct_points_join_rank_two,distinct_points_unique_line,eq_of_le_rk_eq,eval_as_mu_sum,exists_line_misses_point,exists_point_outside,moebius_eval_neg_one,natCast_rk,nonmodular_disjoint_lines,nonmodular_more_lines,point_of_element_outside,rankThreeFrame,result,rk_bottom,rk_join_le,rk_le_three,rk_lt_of_lt,rk_mono,rk_top.
   IsJFunction: proof_shape: bind-only; escape_witness: none; consumers: claim,eval_as_mu_sum,j_eq_mu_product,moebius_eval_neg_one,mu_isJ,result.
   MoebiusPoly: proof_shape: bind-only; escape_witness: none; consumers: claim,eval_as_mu_sum,moebius_eval_neg_one,result.
   Connected: proof_shape: bind-only; escape_witness: none; consumers: claim,result.
   Modular: proof_shape: bind-only; escape_witness: none; consumers: claim,nonmodular_disjoint_lines,nonmodular_more_lines,result.
   claim: proof_shape: bind-only; escape_witness: none; consumers: result.
   interval_finsum: proof_shape: bind-only; escape_witness: none; consumers: j_eq_mu_product,mu_isJ.
   mu_product_equation: proof_shape: bind-only; escape_witness: none; consumers: mu_isJ.
   rectangle_unique: proof_shape: bind-only; escape_witness: none; consumers: j_eq_mu_product.
   mu_isJ: proof_shape: bind-only; escape_witness: none; consumers: j_eq_mu_product.
   j_eq_mu_product: proof_shape: bind-only; escape_witness: none; consumers: eval_as_mu_sum.
   bottomFlat: proof_shape: bind-only; escape_witness: none; consumers: bottom_le,rankThreeFrame,rk_bottom.
   topFlat: proof_shape: bind-only; escape_witness: none; consumers: exists_point_outside,le_top,rankThreeFrame,rk_top.
   joinFlat: proof_shape: bind-only; escape_witness: none; consumers: distinct_points_join_rank_two,distinct_points_unique_line,exists_line_misses_point,join_le,le_join_left,le_join_right,nonmodular_disjoint_lines,nonmodular_more_lines,rk_join_le.
   inter_isFlat: proof_shape: bind-only; escape_witness: none; consumers: meetFlat,nonmodular_more_lines.
   meetFlat: proof_shape: bind-only; escape_witness: none; consumers: le_meet,meet_le_left,meet_le_right,nonmodular_disjoint_lines,nonmodular_more_lines.
   natCast_rk: proof_shape: bind-only; escape_witness: none; consumers: eq_of_le_rk_eq,nonmodular_disjoint_lines,rk_join_le.
   rk_mono: proof_shape: bind-only; escape_witness: none; consumers: distinct_points_join_rank_two,nonmodular_more_lines,rk_lt_of_lt.
   bottom_le: proof_shape: bind-only; escape_witness: none; consumers: point_of_element_outside,rankThreeFrame.
   le_top: proof_shape: bind-only; escape_witness: none; consumers: rankThreeFrame.
   rk_bottom: proof_shape: bind-only; escape_witness: none; consumers: rankThreeFrame.
   rk_top: proof_shape: bind-only; escape_witness: none; consumers: eval_as_mu_sum,exists_point_outside,rankThreeFrame.
   rk_le_three: proof_shape: bind-only; escape_witness: none; consumers: nonmodular_disjoint_lines.
   eq_of_le_rk_eq: proof_shape: bind-only; escape_witness: none; consumers: distinct_points_join_rank_two,distinct_points_unique_line,exists_line_misses_point,rk_lt_of_lt.
   rk_lt_of_lt: proof_shape: bind-only; escape_witness: none; consumers: nonmodular_disjoint_lines,rankThreeFrame.
   le_join_left: proof_shape: bind-only; escape_witness: none; consumers: distinct_points_join_rank_two,exists_line_misses_point,nonmodular_disjoint_lines,nonmodular_more_lines.
   le_join_right: proof_shape: bind-only; escape_witness: none; consumers: distinct_points_join_rank_two,exists_line_misses_point,nonmodular_disjoint_lines,nonmodular_more_lines.
   join_le: proof_shape: bind-only; escape_witness: none; consumers: distinct_points_unique_line,exists_line_misses_point.
   meet_le_left: proof_shape: bind-only; escape_witness: none; consumers: nonmodular_disjoint_lines.
   meet_le_right: proof_shape: bind-only; escape_witness: none; consumers: nonmodular_disjoint_lines.
   le_meet: proof_shape: bind-only; escape_witness: none; consumers: nonmodular_more_lines.
   rk_join_le: proof_shape: bind-only; escape_witness: none; consumers: distinct_points_join_rank_two,nonmodular_disjoint_lines.
   distinct_points_join_rank_two: proof_shape: bind-only; escape_witness: none; consumers: distinct_points_unique_line,exists_line_misses_point,nonmodular_more_lines.
   distinct_points_unique_line: proof_shape: bind-only; escape_witness: none; consumers: nonmodular_more_lines.
   point_of_element_outside: proof_shape: bind-only; escape_witness: none; consumers: exists_point_outside.
   exists_point_outside: proof_shape: bind-only; escape_witness: none; consumers: exists_line_misses_point,nonmodular_more_lines.
   exists_line_misses_point: proof_shape: bind-only; escape_witness: none; consumers: nonmodular_more_lines.
   nonmodular_disjoint_lines: proof_shape: bind-only; escape_witness: none; consumers: nonmodular_more_lines.
   Points: proof_shape: bind-only; escape_witness: none; consumers: moebius_eval_neg_one,nonmodular_more_lines,result.
   Lines: proof_shape: bind-only; escape_witness: none; consumers: moebius_eval_neg_one,nonmodular_more_lines,result.
   nonmodular_more_lines: proof_shape: bind-only; escape_witness: none; consumers: result.
   Graded.RankThreeFrame: proof_shape: bind-only; escape_witness: none; consumers: Graded.endpoint_sum,Graded.eq_bot_iff,Graded.eq_top_iff,Graded.ico_bot_line,Graded.incidence_count,Graded.ioc_point_top,Graded.lines,Graded.mu_adjacent,Graded.mu_bot_line,Graded.mu_bot_point,Graded.mu_line_top,Graded.mu_lines_sum,Graded.mu_point_line,Graded.mu_point_line_all,Graded.mu_point_top,Graded.mu_points_sum,Graded.mu_rank_sum_left,Graded.mu_rank_sum_right,Graded.mu_same_rank,Graded.mu_zero_of_rank_gt,Graded.points,Graded.rank_cases,Graded.rank_le_three,Graded.rank_mono,Graded.rank_three_mu_evaluation,Graded.sign_exponent,Graded.signedLower,Graded.signedLower_bot,Graded.signedLower_layers,Graded.signedLower_line,Graded.signedLower_point,Graded.signedUpper,Graded.signedUpper_layers,Graded.signedUpper_line,Graded.signedUpper_point,Graded.signedUpper_top,Graded.signed_middle_factor,Graded.sum_layers,moebius_eval_neg_one,rankThreeFrame.
   Graded.rank_mono: proof_shape: bind-only; escape_witness: none; consumers: Graded.mu_zero_of_rank_gt,Graded.rank_le_three.
   Graded.rank_le_three: proof_shape: bind-only; escape_witness: none; consumers: Graded.ioc_point_top,Graded.rank_cases,Graded.sign_exponent.
   Graded.eq_bot_iff: proof_shape: bind-only; escape_witness: none; consumers: Graded.ico_bot_line,Graded.rank_cases.
   Graded.eq_top_iff: proof_shape: bind-only; escape_witness: none; consumers: Graded.ioc_point_top,Graded.rank_cases.
   Graded.rank_cases: proof_shape: bind-only; escape_witness: none; consumers: Graded.sum_layers.
   Graded.points: proof_shape: bind-only; escape_witness: none; consumers: Graded.endpoint_sum,Graded.ico_bot_line,Graded.incidence_count,Graded.mu_bot_line,Graded.mu_points_sum,Graded.rank_three_mu_evaluation,Graded.signedLower_layers,Graded.signedLower_line,Graded.signedLower_point,Graded.signedUpper_layers,Graded.signedUpper_line,Graded.signedUpper_point,Graded.sum_layers,moebius_eval_neg_one.
   Graded.lines: proof_shape: bind-only; escape_witness: none; consumers: Graded.endpoint_sum,Graded.incidence_count,Graded.ioc_point_top,Graded.mu_lines_sum,Graded.mu_point_top,Graded.rank_three_mu_evaluation,Graded.signedLower_layers,Graded.signedLower_line,Graded.signedLower_point,Graded.signedUpper_layers,Graded.signedUpper_line,Graded.signedUpper_point,Graded.sum_layers,moebius_eval_neg_one.
   Graded.sum_layers: proof_shape: bind-only; escape_witness: none; consumers: Graded.rank_three_mu_evaluation,Graded.signedLower_layers,Graded.signedUpper_layers.
   Graded.mu_adjacent: proof_shape: bind-only; escape_witness: none; consumers: Graded.mu_bot_point,Graded.mu_line_top,Graded.mu_point_line.
   Graded.mu_bot_point: proof_shape: bind-only; escape_witness: none; consumers: Graded.endpoint_sum,Graded.mu_bot_line,Graded.signedLower_point.
   Graded.mu_line_top: proof_shape: bind-only; escape_witness: none; consumers: Graded.endpoint_sum,Graded.mu_point_top,Graded.signedUpper_line.
   Graded.mu_point_line: proof_shape: bind-only; escape_witness: none; consumers: Graded.mu_point_line_all.
   Graded.ico_bot_line: proof_shape: bind-only; escape_witness: none; consumers: Graded.mu_bot_line.
   Graded.ioc_point_top: proof_shape: bind-only; escape_witness: none; consumers: Graded.mu_point_top.
   Graded.mu_bot_line: proof_shape: bind-only; escape_witness: none; consumers: Graded.endpoint_sum,Graded.signedLower_line.
   Graded.mu_point_top: proof_shape: bind-only; escape_witness: none; consumers: Graded.endpoint_sum,Graded.signedUpper_point.
   Graded.incidence_count: proof_shape: bind-only; escape_witness: none; consumers: Graded.endpoint_sum,Graded.rank_three_mu_evaluation.
   Graded.mu_zero_of_rank_gt: proof_shape: bind-only; escape_witness: none; consumers: Graded.signedLower_line,Graded.signedLower_point,Graded.signedUpper_line,Graded.signedUpper_point.
   Graded.mu_same_rank: proof_shape: bind-only; escape_witness: none; consumers: Graded.mu_rank_sum_left,Graded.mu_rank_sum_right.
   Graded.mu_point_line_all: proof_shape: bind-only; escape_witness: none; consumers: Graded.mu_lines_sum,Graded.mu_points_sum.
   Graded.sign_exponent: proof_shape: bind-only; escape_witness: none; consumers: Graded.signed_middle_factor.
   Graded.signedLower: proof_shape: bind-only; escape_witness: none; consumers: Graded.endpoint_sum,Graded.rank_three_mu_evaluation,Graded.signedLower_bot,Graded.signedLower_layers,Graded.signedLower_line,Graded.signedLower_point,Graded.signed_middle_factor.
   Graded.signedUpper: proof_shape: bind-only; escape_witness: none; consumers: Graded.endpoint_sum,Graded.rank_three_mu_evaluation,Graded.signedUpper_layers,Graded.signedUpper_line,Graded.signedUpper_point,Graded.signedUpper_top,Graded.signed_middle_factor.
   Graded.signed_middle_factor: proof_shape: bind-only; escape_witness: none; consumers: Graded.rank_three_mu_evaluation.
   Graded.signedLower_bot: proof_shape: bind-only; escape_witness: none; consumers: Graded.rank_three_mu_evaluation.
   Graded.signedUpper_top: proof_shape: bind-only; escape_witness: none; consumers: Graded.rank_three_mu_evaluation.
   Graded.signedLower_layers: proof_shape: bind-only; escape_witness: none; consumers: Graded.endpoint_sum,Graded.signedLower_line,Graded.signedLower_point.
   Graded.signedUpper_layers: proof_shape: bind-only; escape_witness: none; consumers: Graded.endpoint_sum,Graded.signedUpper_line,Graded.signedUpper_point.
   Graded.mu_rank_sum_left: proof_shape: bind-only; escape_witness: none; consumers: Graded.signedLower_line,Graded.signedLower_point.
   Graded.mu_rank_sum_right: proof_shape: bind-only; escape_witness: none; consumers: Graded.signedUpper_line,Graded.signedUpper_point.
   Graded.mu_lines_sum: proof_shape: bind-only; escape_witness: none; consumers: Graded.signedUpper_point.
   Graded.mu_points_sum: proof_shape: bind-only; escape_witness: none; consumers: Graded.signedLower_line.
   Graded.signedLower_point: proof_shape: bind-only; escape_witness: none; consumers: Graded.rank_three_mu_evaluation.
   Graded.signedUpper_line: proof_shape: bind-only; escape_witness: none; consumers: Graded.rank_three_mu_evaluation.
   Graded.signedUpper_point: proof_shape: bind-only; escape_witness: none; consumers: Graded.rank_three_mu_evaluation.
   Graded.signedLower_line: proof_shape: bind-only; escape_witness: none; consumers: Graded.rank_three_mu_evaluation.
   Graded.endpoint_sum: proof_shape: bind-only; escape_witness: none; consumers: Graded.rank_three_mu_evaluation.
   Graded.rank_three_mu_evaluation: proof_shape: bind-only; escape_witness: none; consumers: moebius_eval_neg_one.
   rankThreeFrame: proof_shape: bind-only; escape_witness: none; consumers: moebius_eval_neg_one.
   eval_as_mu_sum: proof_shape: bind-only; escape_witness: none; consumers: moebius_eval_neg_one.
   moebius_eval_neg_one: proof_shape: bind-only; escape_witness: none; consumers: result.
   result: proof_shape: bind-only; escape_witness: none; consumers: terminal settling result.
-/
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Combinatorics.Configuration
import Mathlib.Combinatorics.Matroid.Rank.ENat

attribute [local instance] Fintype.ofFinite Fintype.toLocallyFiniteOrder Classical.propDecidable
/-! Binding conventions for J. Johnson and M. Wakefield, "A non-associative incidence near-ring with a generalized
Möbius function", Ars Math. Contemp. 24 (2024) #P2.03 (arXiv:2204.07158v1): the lattice of flats `L(M)` of a matroid,
the partial flags `Fl₃(L)`, the function `J` of Definition 5.1, the J-Möbius polynomial `𝓜(L, t)` of Definition 6.2,
connected and modular matroids, and Question 6.19: "Is there a rank 3 non-modular connected matroid `M` such that
`𝓜(M, −1) = 0`?" -/
namespace D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius
open Polynomial
variable {α : Type*}
/-- The lattice of flats `L(M)`: the flats of `M`, ordered by inclusion. -/
abbrev Flats (M : Matroid α) := {F : Set α // M.IsFlat F}
/-- The rank of a flat of a finite matroid, as a natural number. -/
noncomputable def rk (M : Matroid α) (F : Set α) : ℕ := (M.eRk F).toNat
/-- Definition 5.1: `J : Fl₃(L) → ℤ` is defined by `∑_{(a, b) ⊴ (x, y, z)} J(a, y, b) = δ₃(x, y, z)` for every
partial flag `x ≤ y ≤ z`, where `(a, b) ⊴ (x, y, z)` means `x ≤ a ≤ y ≤ b ≤ z`. -/
def IsJFunction (M : Matroid α) (J : Flats M → Flats M → Flats M → ℤ) : Prop :=
  ∀ x y z : Flats M, x ≤ y → y ≤ z →
    (∑ᶠ (a : Flats M) (_ : x ≤ a ∧ a ≤ y) (b : Flats M) (_ : y ≤ b ∧ b ≤ z), J a y b) =
      if x = y ∧ y = z then 1 else 0
/-- Definition 6.2: the J-Möbius polynomial `𝓜(L, t) = ∑_{(x, y, z) ∈ Fl₃(L)} J(x, y, z) t^{ρ(x, y, z)}`, with
`ρ(x, y, z) = 3 rk(L) − rk(x) − rk(y) − rk(z)`. -/
noncomputable def MoebiusPoly (M : Matroid α) (J : Flats M → Flats M → Flats M → ℤ) : ℤ[X] :=
  ∑ᶠ (x : Flats M) (y : Flats M) (z : Flats M) (_ : x ≤ y ∧ y ≤ z),
    C (J x y z) * X ^ (3 * rk M M.E - rk M x.1 - rk M y.1 - rk M z.1)
/-- A connected matroid: every two distinct elements of the ground set lie in a common circuit. -/
def Connected (M : Matroid α) : Prop :=
  ∀ e ∈ M.E, ∀ f ∈ M.E, e ≠ f → ∃ C, M.IsCircuit C ∧ e ∈ C ∧ f ∈ C
/-- A modular matroid: every two flats form a modular pair, `r(F) + r(G) = r(F ∪ G) + r(F ∩ G)`. -/
def Modular (M : Matroid α) : Prop :=
  ∀ F G : Set α, M.IsFlat F → M.IsFlat G → M.eRk F + M.eRk G = M.eRk (F ∪ G) + M.eRk (F ∩ G)
/-- Question 6.19, answered negatively: no finite rank-3 non-modular connected matroid has `𝓜(M, −1) = 0`. -/
def claim : Prop :=
  ∀ (α : Type) [Finite α] (M : Matroid α), M.eRank = 3 → Connected M → ¬ Modular M →
    ∀ J, IsJFunction M J → (MoebiusPoly M J).eval (-1) ≠ 0
end D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius
namespace D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius
section
open Finset
variable {β : Type*} [PartialOrder β] [Fintype β] [DecidableEq β]
  [LocallyFiniteOrder β] [DecidableLE β]

private lemma interval_finsum (f : β → ℤ) (x y : β) :
    (∑ᶠ (a : β) (_ : x ≤ a ∧ a ≤ y), f a) = ∑ a ∈ Icc x y, f a := by
  rw [finsum_eq_sum_of_fintype]
  simp_rw [finsum_eq_if, ← mem_Icc]
  have hs : (univ.filter (fun a => a ∈ Icc x y)) = Icc x y := by ext a; simp
  calc
    (∑ a, if a ∈ Icc x y then f a else 0) =
        ∑ a ∈ univ.filter (fun a => a ∈ Icc x y), f a := (Finset.sum_filter _ _).symm
    _ = _ := by rw [hs]

private lemma mu_product_equation (x y z : β) :
    (∑ a ∈ Icc x y, ∑ b ∈ Icc y z,
       IncidenceAlgebra.mu ℤ a y * IncidenceAlgebra.mu ℤ y b) =
       if x = y ∧ y = z then 1 else 0 := by
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, IncidenceAlgebra.sum_Icc_mu_left,
    IncidenceAlgebra.sum_Icc_mu_right]
  split_ifs <;> simp_all

private lemma rectangle_unique (f g : β → β → β → ℤ)
    (heq : ∀ x y z, x ≤ y → y ≤ z →
      (∑ a ∈ Icc x y, ∑ b ∈ Icc y z, f a y b) =
      (∑ a ∈ Icc x y, ∑ b ∈ Icc y z, g a y b))
    (x y z : β) (hxy : x ≤ y) (hyz : y ≤ z) : f x y z = g x y z := by
  classical
  have htop (k : β → ℤ) (a : Set.Iic y) :
      (∑ t ∈ Ici a, k t.1) = ∑ t ∈ Icc a.1 y, k t := by
    apply Finset.sum_bij (fun t _ => t.1)
    · intro t ht
      exact mem_Icc.mpr ⟨((mem_Ici (α := Set.Iic y)).mp ht), t.2⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro b hb
      exact ⟨⟨b,(mem_Icc.mp hb).2⟩,mem_Ici.mpr (mem_Icc.mp hb).1,rfl⟩
    · intro t ht
      rfl
  have hbot (k : β → ℤ) (a : Set.Ici y) :
      (∑ t ∈ Iic a, k t.1) = ∑ t ∈ Icc y a.1, k t := by
    apply Finset.sum_bij (fun t _ => t.1)
    · intro t ht
      exact mem_Icc.mpr ⟨t.2,((mem_Iic (α := Set.Ici y)).mp ht)⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro b hb
      exact ⟨⟨b,(mem_Icc.mp hb).1⟩,mem_Iic.mpr (mem_Icc.mp hb).2,rfl⟩
    · intro t ht
      rfl
  have hleft (b : β) (hyb : y ≤ b) :
      (∑ t ∈ Icc y b, f x y t) = ∑ t ∈ Icc y b, g x y t := by
    let F : Set.Iic y → ℤ := fun a => ∑ t ∈ Icc y b, f a.1 y t
    let G : Set.Iic y → ℤ := fun a => ∑ t ∈ Icc y b, g a.1 y t
    have hsum : ∀ a : Set.Iic y, (∑ t ∈ Ici a, F t) = ∑ t ∈ Ici a, G t := by
      intro a
      rw [htop (fun a => ∑ t ∈ Icc y b, f a y t), htop (fun a => ∑ t ∈ Icc y b, g a y t)]
      exact heq a.1 y b a.2 hyb
    have hf := IncidenceAlgebra.moebius_inversion_top F (fun a => ∑ t ∈ Ici a, F t) (fun _ => rfl) ⟨x,hxy⟩
    have hg := IncidenceAlgebra.moebius_inversion_top G (fun a => ∑ t ∈ Ici a, G t) (fun _ => rfl) ⟨x,hxy⟩
    exact hf.trans ((by simp_rw [hsum] : _ = _).trans hg.symm)
  let F : Set.Ici y → ℤ := fun a => f x y a.1
  let G : Set.Ici y → ℤ := fun a => g x y a.1
  have hsum : ∀ a : Set.Ici y, (∑ t ∈ Iic a, F t) = ∑ t ∈ Iic a, G t := by
    intro a
    rw [hbot (fun t => f x y t), hbot (fun t => g x y t)]
    exact hleft a.1 a.2
  have hf := IncidenceAlgebra.moebius_inversion_bot F (fun a => ∑ t ∈ Iic a, F t) (fun _ => rfl) ⟨z,hyz⟩
  have hg := IncidenceAlgebra.moebius_inversion_bot G (fun a => ∑ t ∈ Iic a, G t) (fun _ => rfl) ⟨z,hyz⟩
  exact hf.trans ((by simp_rw [hsum] : _ = _).trans hg.symm)

end
end D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius
namespace D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius
noncomputable section
variable {α : Type*} [Finite α] (M : Matroid α)
private theorem mu_isJ : IsJFunction M (fun x y z => IncidenceAlgebra.mu ℤ x y * IncidenceAlgebra.mu ℤ y z) := by
  intro x y z hxy hyz
  rw [interval_finsum]
  simp_rw [interval_finsum]
  by_cases hh : x = y ∧ y = z
  · simpa only [if_pos hh] using mu_product_equation x y z
  · simpa only [if_neg hh] using mu_product_equation x y z
private theorem j_eq_mu_product (J : Flats M → Flats M → Flats M → ℤ) (hJ : IsJFunction M J)
    (x y z : Flats M) (hxy : x ≤ y) (hyz : y ≤ z) :
    J x y z = IncidenceAlgebra.mu ℤ x y * IncidenceAlgebra.mu ℤ y z := by
  apply rectangle_unique J (fun x y z => IncidenceAlgebra.mu ℤ x y * IncidenceAlgebra.mu ℤ y z) _ x y z hxy hyz
  intro a b c hab hbc
  have h1 := hJ a b c hab hbc
  have h2 := mu_isJ M a b c hab hbc
  rw [interval_finsum] at h1 h2
  simp_rw [interval_finsum] at h1 h2
  exact h1.trans h2.symm
end
end D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius
namespace D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius
noncomputable section
open Set
variable {α : Type*} [Finite α] (M : Matroid α)
private def bottomFlat : Flats M := ⟨M.closure ∅, M.isFlat_closure _⟩
private def topFlat : Flats M := ⟨M.E, M.ground_isFlat⟩
private def joinFlat (F G : Flats M) : Flats M := ⟨M.closure (F.1 ∪ G.1), M.isFlat_closure _⟩
private lemma inter_isFlat (F G : Flats M) : M.IsFlat (F.1 ∩ G.1) := by
  rw [Set.inter_eq_iInter]
  exact Matroid.IsFlat.iInter (fun b => by cases b <;> first | exact F.2 | exact G.2)
private def meetFlat (F G : Flats M) : Flats M := ⟨F.1 ∩ G.1, inter_isFlat M F G⟩
private lemma natCast_rk (X : Set α) : (rk M X : ℕ∞) = M.eRk X :=
  ENat.natCast_toNat (M.isRkFinite_set X).eRk_lt_top.ne
private lemma rk_mono {X Y : Set α} (h : X ⊆ Y) : rk M X ≤ rk M Y := by
  exact ENat.toNat_le_toNat (M.eRk_mono h) (M.isRkFinite_set Y).eRk_lt_top.ne
private lemma bottom_le (F : Flats M) : bottomFlat M ≤ F := by
  change M.closure ∅ ⊆ F.1
  simpa only [F.2.closure] using M.closure_subset_closure (empty_subset F.1)
private lemma le_top (F : Flats M) : F ≤ topFlat M := F.2.subset_ground
private lemma rk_bottom : rk M (bottomFlat M).1 = 0 := by
  simp [rk,bottomFlat, M.eRk_closure_eq]
private lemma rk_top (hM : M.eRank = 3) : rk M (topFlat M).1 = 3 := by
  simp [rk,topFlat,Matroid.eRk_ground,hM]
private lemma rk_le_three (hM : M.eRank = 3) (X : Set α) : rk M X ≤ 3 := by
  apply ENat.toNat_le_of_le_natCast
  simpa [hM] using M.eRk_le_eRank X
private lemma eq_of_le_rk_eq {F G : Flats M} (hFG : F ≤ G) (hr : rk M F.1 = rk M G.1) : F = G := by
  have he : M.eRk G.1 ≤ M.eRk F.1 := by rw [← natCast_rk M G.1, ← natCast_rk M F.1,hr]
  have hc := (M.isRkFinite_set F.1).closure_eq_closure_of_subset_of_eRk_ge_eRk hFG he
  apply Subtype.ext
  simpa only [F.2.closure,G.2.closure] using hc
private lemma rk_lt_of_lt {F G : Flats M} (hFG : F < G) : rk M F.1 < rk M G.1 := by
  exact lt_of_le_of_ne (rk_mono M hFG.le) (fun h => hFG.ne (eq_of_le_rk_eq M hFG.le h))
private lemma le_join_left (F G : Flats M) : F ≤ joinFlat M F G :=
  subset_union_left.trans (M.subset_closure _ (union_subset F.2.subset_ground G.2.subset_ground))
private lemma le_join_right (F G : Flats M) : G ≤ joinFlat M F G :=
  subset_union_right.trans (M.subset_closure _ (union_subset F.2.subset_ground G.2.subset_ground))
private lemma join_le {F G H : Flats M} (hF : F ≤ H) (hG : G ≤ H) : joinFlat M F G ≤ H := by
  change M.closure (F.1 ∪ G.1) ⊆ H.1
  simpa only [H.2.closure] using M.closure_subset_closure (union_subset hF hG)
private lemma meet_le_left (F G : Flats M) : meetFlat M F G ≤ F := inter_subset_left
private lemma meet_le_right (F G : Flats M) : meetFlat M F G ≤ G := inter_subset_right
private lemma le_meet {F G H : Flats M} (hF : F ≤ G) (hG : F ≤ H) : F ≤ meetFlat M G H :=
  subset_inter hF hG
private lemma rk_join_le (F G : Flats M) : rk M (joinFlat M F G).1 ≤ rk M F.1 + rk M G.1 := by
  have h := M.eRk_union_le_eRk_add_eRk F.1 G.1
  rw [← natCast_rk M F.1, ← natCast_rk M G.1] at h
  have ht : M.eRk (joinFlat M F G).1 = M.eRk (F.1 ∪ G.1) := M.eRk_closure_eq _
  rw [← ht, ← natCast_rk M (joinFlat M F G).1, ← Nat.cast_add] at h
  exact_mod_cast h
private lemma distinct_points_join_rank_two (P Q : Flats M) (hP : rk M P.1 = 1)
    (hQ : rk M Q.1 = 1) (hne : P ≠ Q) : rk M (joinFlat M P Q).1 = 2 := by
  have hle : rk M (joinFlat M P Q).1 ≤ 2 := by simpa [hP,hQ] using rk_join_le M P Q
  have hp : rk M P.1 ≤ rk M (joinFlat M P Q).1 := rk_mono M (le_join_left M P Q)
  by_contra hh
  have hr : rk M (joinFlat M P Q).1 = 1 := by omega
  have heP := eq_of_le_rk_eq M (le_join_left M P Q) (hP.trans hr.symm)
  have heQ := eq_of_le_rk_eq M (le_join_right M P Q) (hQ.trans hr.symm)
  exact hne (heP.trans heQ.symm)
private lemma distinct_points_unique_line (P Q H K : Flats M)
    (hP : rk M P.1 = 1) (hQ : rk M Q.1 = 1) (hne : P ≠ Q)
    (hH : rk M H.1 = 2) (hK : rk M K.1 = 2)
    (hPH : P ≤ H) (hQH : Q ≤ H) (hPK : P ≤ K) (hQK : Q ≤ K) : H = K := by
  have hr := distinct_points_join_rank_two M P Q hP hQ hne
  exact (eq_of_le_rk_eq M (join_le M hPH hQH) (hr.trans hH.symm)).symm.trans
    (eq_of_le_rk_eq M (join_le M hPK hQK) (hr.trans hK.symm))
private lemma point_of_element_outside (F : Flats M) (e : α) (he : e ∈ M.E) (heF : e ∉ F.1) :
    ∃ P : Flats M, rk M P.1 = 1 ∧ ¬ P ≤ F := by
  let P : Flats M := ⟨M.closure {e}, M.isFlat_closure _⟩
  have hebot : e ∉ M.closure ∅ := fun h => heF (bottom_le M F h)
  have h1 : M.eRk {e} = 1 := by
    simpa using M.eRk_insert_eq_add_one (X := ∅) ⟨he,hebot⟩
  have heP : e ∈ P.1 := M.subset_closure {e} (singleton_subset_iff.mpr he) (mem_singleton e)
  refine ⟨P, ?_, fun h => heF (h heP)⟩
  simp [P,rk,Matroid.eRk_closure_eq,h1]
private lemma exists_point_outside (hM : M.eRank = 3) (F : Flats M) (hF : rk M F.1 < 3) :
    ∃ P : Flats M, rk M P.1 = 1 ∧ ¬ P ≤ F := by
  have hn : ¬ M.E ⊆ F.1 := by
    intro hh
    have hEq : F = topFlat M := Subtype.ext (F.2.subset_ground.antisymm hh)
    have ht := rk_top M hM
    rw [← hEq] at ht
    omega
  obtain ⟨e,he,heF⟩ := Set.not_subset.mp hn
  exact point_of_element_outside M F e he heF
private lemma exists_line_misses_point (hM : M.eRank = 3) (P : Flats M) (hP : rk M P.1 = 1) :
    ∃ H : Flats M, rk M H.1 = 2 ∧ ¬ P ≤ H := by
  obtain ⟨Q,hQ,hQP⟩ := exists_point_outside M hM P (by omega)
  have hnePQ : P ≠ Q := fun h => hQP (h ▸ le_rfl)
  have hPQ := distinct_points_join_rank_two M P Q hP hQ hnePQ
  obtain ⟨R,hR,hRPQ⟩ := exists_point_outside M hM (joinFlat M P Q) (by omega)
  have hneQR : Q ≠ R := by
    intro h
    apply hRPQ
    rw [←h]
    exact le_join_right M P Q
  have hQR := distinct_points_join_rank_two M Q R hQ hR hneQR
  refine ⟨joinFlat M Q R,hQR,?_⟩
  intro hPQR
  have hle : joinFlat M P Q ≤ joinFlat M Q R := join_le M hPQR (le_join_left M Q R)
  have heq := eq_of_le_rk_eq M hle (hPQ.trans hQR.symm)
  exact hRPQ (heq.symm ▸ le_join_right M Q R)
private lemma nonmodular_disjoint_lines (hM : M.eRank = 3) (hmod : ¬ Modular M) :
    ∃ F G : Flats M, rk M F.1 = 2 ∧ rk M G.1 = 2 ∧ rk M (meetFlat M F G).1 = 0 := by
  have hex : ∃ F G : Set α, M.IsFlat F ∧ M.IsFlat G ∧
      M.eRk F + M.eRk G ≠ M.eRk (F ∪ G) + M.eRk (F ∩ G) := by
    simpa only [Modular,not_forall,not_imp,exists_prop] using hmod
  obtain ⟨F,G,hF,hG,hneq⟩ := hex
  have hFG : ¬ F ⊆ G := by
    intro hh
    apply hneq
    rw [union_eq_self_of_subset_left hh,inter_eq_self_of_subset_left hh,add_comm]
  have hGF : ¬ G ⊆ F := by
    intro hh
    apply hneq
    rw [union_eq_self_of_subset_right hh,inter_eq_self_of_subset_right hh]
  let f : Flats M := ⟨F,hF⟩
  let g : Flats M := ⟨G,hG⟩
  have hIlF : meetFlat M f g < f := lt_of_le_not_ge (meet_le_left M f g) (fun hh => hFG
    (hh.trans (meet_le_right M f g)))
  have hIlG : meetFlat M f g < g := lt_of_le_not_ge (meet_le_right M f g) (fun hh => hGF
    (hh.trans (meet_le_left M f g)))
  have hFlJ : f < joinFlat M f g := lt_of_le_not_ge (le_join_left M f g) (fun hh => hGF
    ((le_join_right M f g).trans hh))
  have hGlJ : g < joinFlat M f g := lt_of_le_not_ge (le_join_right M f g) (fun hh => hFG
    ((le_join_left M f g).trans hh))
  have hiF := rk_lt_of_lt M hIlF
  have hiG := rk_lt_of_lt M hIlG
  have hFj := rk_lt_of_lt M hFlJ
  have hGj := rk_lt_of_lt M hGlJ
  have hj3 := rk_le_three M hM (joinFlat M f g).1
  have hjoin := rk_join_le M f g
  have hnat : rk M F + rk M G ≠ rk M (joinFlat M f g).1 + rk M (meetFlat M f g).1 := by
    intro heq
    apply hneq
    have hc := congrArg (fun n : ℕ => (n : ℕ∞)) heq
    simpa only [Nat.cast_add,natCast_rk,joinFlat,meetFlat,Matroid.eRk_closure_eq] using hc
  refine ⟨f,g,?_,?_,?_⟩ <;> dsimp [f,g] at * <;> omega
end
end D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius
namespace D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius
noncomputable section
variable {α : Type*} [Finite α] (M : Matroid α)
private abbrev Points := {P : Flats M // rk M P.1 = 1}
private abbrev Lines := {H : Flats M // rk M H.1 = 2}
private theorem nonmodular_more_lines (hM : M.eRank = 3) (hmod : ¬Modular M) :
    Fintype.card (Points M) < Fintype.card (Lines M) := by
  letI : Membership (Points M) (Lines M) := ⟨fun h p => p.1 ≤ h.1⟩
  letI : Configuration.HasLines (Points M) (Lines M) := {
    exists_point := by
      intro H
      obtain ⟨P,hP,hPH⟩ := exists_point_outside M hM H.1 (by rw [H.2]; omega)
      exact ⟨⟨P,hP⟩,hPH⟩
    exists_line := by
      intro P
      obtain ⟨H,hH,hPH⟩ := exists_line_misses_point M hM P.1 P.2
      exact ⟨⟨H,hH⟩,hPH⟩
    eq_or_eq := by
      intro P Q H K hPH hQH hPK hQK
      by_cases he : P = Q
      · exact Or.inl he
      right
      apply Subtype.ext
      exact distinct_points_unique_line M P.1 Q.1 H.1 K.1 P.2 Q.2
        (fun h => he (Subtype.ext h)) H.2 K.2 hPH hQH hPK hQK
    mkLine := fun {P Q} hPQ => ⟨joinFlat M P.1 Q.1,
      distinct_points_join_rank_two M P.1 Q.1 P.2 Q.2 (fun h => hPQ (Subtype.ext h))⟩
    mkLine_ax := fun {P Q} _ => ⟨le_join_left M P.1 Q.1,le_join_right M P.1 Q.1⟩ }
  have hle := Configuration.HasLines.card_le (Points M) (Lines M)
  by_contra hn
  have heq : Fintype.card (Points M) = Fintype.card (Lines M) := by omega
  letI : Configuration.HasPoints (Points M) (Lines M) := Configuration.HasLines.hasPoints heq
  obtain ⟨H,K,hH,hK,hHK⟩ := nonmodular_disjoint_lines M hM hmod
  have hne : (⟨H,hH⟩ : Lines M) ≠ ⟨K,hK⟩ := by
    intro he
    have h : H = K := congrArg Subtype.val he
    have hi : meetFlat M H K = H := Subtype.ext (by simp [meetFlat,h])
    rw [hi,hH] at hHK
    omega
  obtain ⟨P,⟨hPH,hPK⟩,_⟩ := Configuration.HasPoints.existsUnique_point
    (Points M) (Lines M) ⟨H,hH⟩ ⟨K,hK⟩ hne
  have hr := rk_mono M (le_meet M hPH hPK)
  rw [P.2,hHK] at hr
  omega
end
end D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius

namespace D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius.Graded
open Finset
private structure RankThreeFrame (β : Type*) [PartialOrder β] where
  rank : β → ℕ
  bot : β
  top : β
  bot_le : ∀ x, bot ≤ x
  le_top : ∀ x, x ≤ top
  rank_bot : rank bot = 0
  rank_top : rank top = 3
  strict : StrictMono rank
variable {β : Type*} [PartialOrder β] [Fintype β] [DecidableEq β]
  [LocallyFiniteOrder β] [DecidableLE β]
variable (R : RankThreeFrame β)
private lemma rank_mono {x y : β} (h : x ≤ y) : R.rank x ≤ R.rank y :=
  R.strict.monotone h
private lemma rank_le_three (x : β) : R.rank x ≤ 3 := by
  simpa [R.rank_top] using rank_mono R (R.le_top x)
private lemma eq_bot_iff (x : β) : x = R.bot ↔ R.rank x = 0 := by
  constructor
  · rintro rfl; exact R.rank_bot
  · intro h
    by_contra hn
    have hlt := R.strict (lt_of_le_of_ne (R.bot_le x) (Ne.symm hn))
    rw [R.rank_bot,h] at hlt
    omega
private lemma eq_top_iff (x : β) : x = R.top ↔ R.rank x = 3 := by
  constructor
  · rintro rfl; exact R.rank_top
  · intro h
    by_contra hn
    have hlt := R.strict (lt_of_le_of_ne (R.le_top x) hn)
    rw [R.rank_top,h] at hlt
    omega
private lemma rank_cases (x : β) : x = R.bot ∨ R.rank x = 1 ∨ R.rank x = 2 ∨ x = R.top := by
  have hh := rank_le_three R x
  by_cases h0 : R.rank x = 0
  · exact Or.inl ((eq_bot_iff R x).mpr h0)
  by_cases h3 : R.rank x = 3
  · exact Or.inr (Or.inr (Or.inr ((eq_top_iff R x).mpr h3)))
  have h12 : R.rank x = 1 ∨ R.rank x = 2 := by omega
  rcases h12 with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
private def points : Finset β := univ.filter (fun x => R.rank x = 1)
private def lines : Finset β := univ.filter (fun x => R.rank x = 2)
private lemma sum_layers (f : β → ℤ) :
    (∑ x, f x) = f R.bot + ∑ x ∈ points R, f x + ∑ x ∈ lines R, f x + f R.top := by
  have hb : R.bot ≠ R.top := by
    intro hh
    have hr := R.rank_bot
    rw [hh,R.rank_top] at hr
    omega
  calc
    _ = ∑ x, ((if x = R.bot then f x else 0) +
        (if R.rank x = 1 then f x else 0) +
        (if R.rank x = 2 then f x else 0) +
        (if x = R.top then f x else 0)) := by
      apply sum_congr rfl
      intro x _
      rcases rank_cases R x with h | h | h | h
      · subst x
        simp [R.rank_bot,hb]
      · have h0 : x ≠ R.bot := by intro he; rw [he,R.rank_bot] at h; omega
        have h3 : x ≠ R.top := by intro he; rw [he,R.rank_top] at h; omega
        simp [h,h0,h3]
      · have h0 : x ≠ R.bot := by intro he; rw [he,R.rank_bot] at h; omega
        have h3 : x ≠ R.top := by intro he; rw [he,R.rank_top] at h; omega
        simp [h,h0,h3]
      · subst x
        simp [R.rank_top,Ne.symm hb]
    _ = _ := by simp [sum_add_distrib,points,lines,Finset.sum_filter]
private lemma mu_adjacent (x y : β) (hxy : x < y) (hr : R.rank y = R.rank x + 1) :
    IncidenceAlgebra.mu ℤ x y = -1 := by
  have hi : Ico x y = {x} := by
    ext a
    simp only [mem_Ico,mem_singleton]
    constructor
    · intro ha
      by_contra hn
      have hx := R.strict (lt_of_le_of_ne ha.1 (Ne.symm hn))
      have hy := R.strict ha.2
      omega
    · rintro rfl
      exact ⟨le_rfl,hxy⟩
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hxy.ne,hi]
  simp
private lemma mu_bot_point (p : β) (hp : R.rank p = 1) :
    IncidenceAlgebra.mu ℤ R.bot p = -1 := by
  apply mu_adjacent R
  · refine lt_of_le_of_ne (R.bot_le p) ?_
    intro he
    have h0 := R.rank_bot
    rw [he,hp] at h0
    omega
  · simp [R.rank_bot,hp]
private lemma mu_line_top (h : β) (hh : R.rank h = 2) :
    IncidenceAlgebra.mu ℤ h R.top = -1 := by
  apply mu_adjacent R
  · refine lt_of_le_of_ne (R.le_top h) ?_
    intro he
    rw [he,R.rank_top] at hh
    omega
  · rw [R.rank_top,hh]
private lemma mu_point_line (p h : β) (hp : R.rank p = 1) (hh : R.rank h = 2) (hle : p ≤ h) :
    IncidenceAlgebra.mu ℤ p h = -1 := by
  apply mu_adjacent R
  · refine lt_of_le_of_ne hle ?_
    intro he; rw [he,hh] at hp; omega
  · omega
private lemma ico_bot_line (h : β) (hh : R.rank h = 2) :
    Ico R.bot h = insert R.bot ((points R).filter (fun p => p ≤ h)) := by
  ext a
  simp only [mem_Ico,mem_insert,mem_filter,points,mem_univ,true_and]
  constructor
  · intro ha
    by_cases hb : a = R.bot
    · exact Or.inl hb
    right
    have h1 := R.strict ha.2
    have h0 : R.rank a ≠ 0 := by intro hz; exact hb ((eq_bot_iff R a).mpr hz)
    exact ⟨by omega,ha.2.le⟩
  · rintro (rfl | ⟨ha,hle⟩)
    · exact ⟨le_rfl,lt_of_le_of_ne (R.bot_le h) (by
        intro he; have h0:=R.rank_bot; rw [he,hh] at h0; omega)⟩
    · exact ⟨R.bot_le a,lt_of_le_of_ne hle (by intro he; rw [he,hh] at ha; omega)⟩
private lemma ioc_point_top (p : β) (hp : R.rank p = 1) :
    Ioc p R.top = insert R.top ((lines R).filter (fun h => p ≤ h)) := by
  ext a
  simp only [mem_Ioc,mem_insert,mem_filter,lines,mem_univ,true_and]
  constructor
  · intro ha
    by_cases ht : a = R.top
    · exact Or.inl ht
    right
    have h1 := R.strict ha.1
    have h3 := rank_le_three R a
    have h0 : R.rank a ≠ 3 := by intro hz; exact ht ((eq_top_iff R a).mpr hz)
    exact ⟨by omega,ha.1.le⟩
  · rintro (rfl | ⟨ha,hle⟩)
    · exact ⟨lt_of_le_of_ne (R.le_top p) (by intro he; rw [he,R.rank_top] at hp; omega),le_rfl⟩
    · exact ⟨lt_of_le_of_ne hle (by intro he; rw [he,ha] at hp; omega),R.le_top a⟩
private lemma mu_bot_line (h : β) (hh : R.rank h = 2) :
    IncidenceAlgebra.mu ℤ R.bot h = (((points R).filter (fun p => p ≤ h)).card : ℤ) - 1 := by
  have hn : R.bot ≠ h := by intro he; have h0:=R.rank_bot; rw [he,hh] at h0; omega
  have hmem : R.bot ∉ (points R).filter (fun p => p ≤ h) := by simp [points,R.rank_bot]
  have hs : (∑ p ∈ (points R).filter (fun p => p ≤ h), IncidenceAlgebra.mu ℤ R.bot p) =
      -(((points R).filter (fun p => p ≤ h)).card : ℤ) := by
    calc
      _ = ∑ p ∈ (points R).filter (fun p => p ≤ h), (-1 : ℤ) := by
        apply sum_congr rfl
        intro p hp
        apply mu_bot_point R
        simpa [points] using (mem_filter.mp hp).1
      _ = _ := by simp
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hn,ico_bot_line R h hh,sum_insert hmem,hs]
  simp only [IncidenceAlgebra.mu_self]
  ring
private lemma mu_point_top (p : β) (hp : R.rank p = 1) :
    IncidenceAlgebra.mu ℤ p R.top = (((lines R).filter (fun h => p ≤ h)).card : ℤ) - 1 := by
  have hn : p ≠ R.top := by intro he; rw [he,R.rank_top] at hp; omega
  have hmem : R.top ∉ (lines R).filter (fun h => p ≤ h) := by simp [lines,R.rank_top]
  have hs : (∑ h ∈ (lines R).filter (fun h => p ≤ h), IncidenceAlgebra.mu ℤ h R.top) =
      -(((lines R).filter (fun h => p ≤ h)).card : ℤ) := by
    calc
      _ = ∑ h ∈ (lines R).filter (fun h => p ≤ h), (-1 : ℤ) := by
        apply sum_congr rfl
        intro h hh
        apply mu_line_top R
        simpa [lines] using (mem_filter.mp hh).1
      _ = _ := by simp
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne hn,ioc_point_top R p hp,sum_insert hmem,hs]
  simp only [IncidenceAlgebra.mu_self]
  ring
private lemma incidence_count : (∑ p ∈ points R, (((lines R).filter (fun h => p ≤ h)).card : ℤ)) =
    ∑ h ∈ lines R, (((points R).filter (fun p => p ≤ h)).card : ℤ) := by
  simp only [Finset.card_eq_sum_ones]
  push_cast
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
private lemma mu_zero_of_rank_gt (x y : β) (hr : R.rank y < R.rank x) :
    IncidenceAlgebra.mu ℤ x y = 0 :=
  IncidenceAlgebra.apply_eq_zero_of_not_le (fun h => by have hm := rank_mono R h; omega) _
private lemma mu_same_rank (x y : β) (hr : R.rank x = R.rank y) :
    IncidenceAlgebra.mu ℤ x y = if x = y then 1 else 0 := by
  by_cases he : x = y
  · subst y; simp
  · rw [if_neg he]
    apply IncidenceAlgebra.apply_eq_zero_of_not_le
    intro hle
    have hh := R.strict (lt_of_le_of_ne hle he)
    omega
private lemma mu_point_line_all (p h : β) (hp : R.rank p = 1) (hh : R.rank h = 2) :
    IncidenceAlgebra.mu ℤ p h = if p ≤ h then -1 else 0 := by
  by_cases he : p ≤ h
  · rw [if_pos he]; exact mu_point_line R p h hp hh he
  · rw [if_neg he]; exact IncidenceAlgebra.apply_eq_zero_of_not_le he _
private lemma sign_exponent (x y z : β) :
    (-1 : ℤ) ^ (9 - R.rank x - R.rank y - R.rank z) =
      -((-1 : ℤ) ^ R.rank x * (-1 : ℤ) ^ R.rank y * (-1 : ℤ) ^ R.rank z) := by
  have hx:=rank_le_three R x
  have hy:=rank_le_three R y
  have hz:=rank_le_three R z
  interval_cases R.rank x <;> interval_cases R.rank y <;> interval_cases R.rank z <;> norm_num
private def signedLower (y : β) : ℤ := ∑ x, IncidenceAlgebra.mu ℤ x y * (-1 : ℤ)^R.rank x
private def signedUpper (y : β) : ℤ := ∑ z, IncidenceAlgebra.mu ℤ y z * (-1 : ℤ)^R.rank z
private lemma signed_middle_factor :
    (∑ x, ∑ y, ∑ z, IncidenceAlgebra.mu ℤ x y * IncidenceAlgebra.mu ℤ y z *
       (-1 : ℤ) ^ (9 - R.rank x - R.rank y - R.rank z)) =
    ∑ y, -((-1 : ℤ)^R.rank y * signedLower R y * signedUpper R y) := by
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro y _
  simp only [signedLower,signedUpper,sign_exponent]
  simp only [Finset.mul_sum,Finset.sum_mul,←Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro z _
  ring
private lemma signedLower_bot : signedLower R R.bot = 1 := by
  unfold signedLower
  rw [sum_eq_single R.bot]
  · simp [R.rank_bot]
  · intro x _ hx
    have hn : ¬x ≤ R.bot := by intro he; exact hx (he.antisymm (R.bot_le x))
    simp [IncidenceAlgebra.apply_eq_zero_of_not_le hn]
  · simp
private lemma signedUpper_top : signedUpper R R.top = -1 := by
  unfold signedUpper
  rw [sum_eq_single R.top]
  · simp [R.rank_top]
  · intro z _ hz
    have hn : ¬R.top ≤ z := by intro he; exact hz ((R.le_top z).antisymm he)
    simp [IncidenceAlgebra.apply_eq_zero_of_not_le hn]
  · simp
private lemma signedLower_layers (y : β) : signedLower R y =
    IncidenceAlgebra.mu ℤ R.bot y - (∑ p ∈ points R, IncidenceAlgebra.mu ℤ p y) +
    (∑ h ∈ lines R, IncidenceAlgebra.mu ℤ h y) - IncidenceAlgebra.mu ℤ R.top y := by
  unfold signedLower
  rw [sum_layers R]
  have hP : (∑ p ∈ points R, IncidenceAlgebra.mu ℤ p y * (-1 : ℤ)^R.rank p) =
      -(∑ p ∈ points R, IncidenceAlgebra.mu ℤ p y) := by
    rw [←sum_neg_distrib]
    apply sum_congr rfl
    intro p hp
    have hr : R.rank p = 1 := by simpa [points] using hp
    simp [hr]
  have hH : (∑ h ∈ lines R, IncidenceAlgebra.mu ℤ h y * (-1 : ℤ)^R.rank h) =
      ∑ h ∈ lines R, IncidenceAlgebra.mu ℤ h y := by
    apply sum_congr rfl
    intro h hh
    have hr : R.rank h = 2 := by simpa [lines] using hh
    simp [hr]
  rw [hP,hH]
  simp [R.rank_bot,R.rank_top,sub_eq_add_neg]
private lemma signedUpper_layers (y : β) : signedUpper R y =
    IncidenceAlgebra.mu ℤ y R.bot - (∑ p ∈ points R, IncidenceAlgebra.mu ℤ y p) +
    (∑ h ∈ lines R, IncidenceAlgebra.mu ℤ y h) - IncidenceAlgebra.mu ℤ y R.top := by
  unfold signedUpper
  rw [sum_layers R]
  have hP : (∑ p ∈ points R, IncidenceAlgebra.mu ℤ y p * (-1 : ℤ)^R.rank p) =
      -(∑ p ∈ points R, IncidenceAlgebra.mu ℤ y p) := by
    rw [←sum_neg_distrib]
    apply sum_congr rfl
    intro p hp
    have hr : R.rank p = 1 := by simpa [points] using hp
    simp [hr]
  have hH : (∑ h ∈ lines R, IncidenceAlgebra.mu ℤ y h * (-1 : ℤ)^R.rank h) =
      ∑ h ∈ lines R, IncidenceAlgebra.mu ℤ y h := by
    apply sum_congr rfl
    intro h hh
    have hr : R.rank h = 2 := by simpa [lines] using hh
    simp [hr]
  rw [hP,hH]
  simp [R.rank_bot,R.rank_top,sub_eq_add_neg]
private lemma mu_rank_sum_left (k : ℕ) (y : β) (hy : R.rank y = k) :
    (∑ x ∈ univ.filter (fun x => R.rank x = k), IncidenceAlgebra.mu ℤ x y) = 1 := by
  calc
    _ = ∑ x ∈ univ.filter (fun x => R.rank x = k), if x = y then (1 : ℤ) else 0 := by
      apply sum_congr rfl
      intro x hx
      apply mu_same_rank R
      simpa using ((mem_filter.mp hx).2.trans hy.symm)
    _ = 1 := by simp [hy]
private lemma mu_rank_sum_right (k : ℕ) (y : β) (hy : R.rank y = k) :
    (∑ x ∈ univ.filter (fun x => R.rank x = k), IncidenceAlgebra.mu ℤ y x) = 1 := by
  calc
    _ = ∑ x ∈ univ.filter (fun x => R.rank x = k), if y = x then (1 : ℤ) else 0 := by
      apply sum_congr rfl
      intro x hx
      apply mu_same_rank R
      simpa using (hy.trans (mem_filter.mp hx).2.symm)
    _ = 1 := by simp [hy]
private lemma mu_lines_sum (p : β) (hp : R.rank p = 1) :
    (∑ h ∈ lines R, IncidenceAlgebra.mu ℤ p h) = -(((lines R).filter (fun h => p ≤ h)).card : ℤ) := by
  calc
    _ = ∑ h ∈ lines R, if p ≤ h then (-1 : ℤ) else 0 := by
      apply sum_congr rfl
      intro h hh
      exact mu_point_line_all R p h hp (by simpa [lines] using hh)
    _ = ∑ h ∈ (lines R).filter (fun h => p ≤ h), (-1 : ℤ) := (Finset.sum_filter _ _).symm
    _ = _ := by simp
private lemma mu_points_sum (h : β) (hh : R.rank h = 2) :
    (∑ p ∈ points R, IncidenceAlgebra.mu ℤ p h) = -(((points R).filter (fun p => p ≤ h)).card : ℤ) := by
  calc
    _ = ∑ p ∈ points R, if p ≤ h then (-1 : ℤ) else 0 := by
      apply sum_congr rfl
      intro p hp
      exact mu_point_line_all R p h (by simpa [points] using hp) hh
    _ = ∑ p ∈ (points R).filter (fun p => p ≤ h), (-1 : ℤ) := (Finset.sum_filter _ _).symm
    _ = _ := by simp
private lemma signedLower_point (p : β) (hp : R.rank p = 1) : signedLower R p = -2 := by
  rw [signedLower_layers,mu_bot_point R p hp]
  have hs : (∑ x ∈ points R, IncidenceAlgebra.mu ℤ x p) = 1 := mu_rank_sum_left R 1 p hp
  have ht : IncidenceAlgebra.mu ℤ R.top p = 0 := mu_zero_of_rank_gt R _ _ (by rw [R.rank_top,hp]; omega)
  have hh : (∑ h ∈ lines R, IncidenceAlgebra.mu ℤ h p) = 0 := by
    apply sum_eq_zero
    intro h hh
    apply mu_zero_of_rank_gt R
    have hr : R.rank h = 2 := by simpa [lines] using hh
    omega
  rw [hs,ht,hh]
  norm_num
private lemma signedUpper_line (h : β) (hh : R.rank h = 2) : signedUpper R h = 2 := by
  rw [signedUpper_layers,mu_line_top R h hh]
  have hs : (∑ x ∈ lines R, IncidenceAlgebra.mu ℤ h x) = 1 := mu_rank_sum_right R 2 h hh
  have hb : IncidenceAlgebra.mu ℤ h R.bot = 0 := mu_zero_of_rank_gt R _ _ (by rw [R.rank_bot,hh]; omega)
  have hp : (∑ p ∈ points R, IncidenceAlgebra.mu ℤ h p) = 0 := by
    apply sum_eq_zero
    intro p hp
    apply mu_zero_of_rank_gt R
    have hr : R.rank p = 1 := by simpa [points] using hp
    omega
  rw [hs,hb,hp]
  norm_num
private lemma signedUpper_point (p : β) (hp : R.rank p = 1) :
    signedUpper R p = -2 * (((lines R).filter (fun h => p ≤ h)).card : ℤ) := by
  rw [signedUpper_layers,mu_lines_sum R p hp,mu_point_top R p hp]
  have hs : (∑ x ∈ points R, IncidenceAlgebra.mu ℤ p x) = 1 := mu_rank_sum_right R 1 p hp
  have hb : IncidenceAlgebra.mu ℤ p R.bot = 0 := mu_zero_of_rank_gt R _ _ (by rw [R.rank_bot,hp]; omega)
  rw [hs,hb]
  ring
private lemma signedLower_line (h : β) (hh : R.rank h = 2) :
    signedLower R h = 2 * (((points R).filter (fun p => p ≤ h)).card : ℤ) := by
  rw [signedLower_layers,mu_points_sum R h hh,mu_bot_line R h hh]
  have hs : (∑ x ∈ lines R, IncidenceAlgebra.mu ℤ x h) = 1 := mu_rank_sum_left R 2 h hh
  have ht : IncidenceAlgebra.mu ℤ R.top h = 0 := mu_zero_of_rank_gt R _ _ (by rw [R.rank_top,hh]; omega)
  rw [hs,ht]
  ring
private lemma endpoint_sum : signedUpper R R.bot + signedLower R R.top =
    2 * ((points R).card : ℤ) - 2 * ((lines R).card : ℤ) := by
  rw [signedUpper_layers,signedLower_layers]
  have hP : (∑ p ∈ points R, IncidenceAlgebra.mu ℤ R.bot p) = -((points R).card : ℤ) := by
    calc
      _ = ∑ p ∈ points R, (-1 : ℤ) := by
        apply sum_congr rfl
        intro p hp
        exact mu_bot_point R p (by simpa [points] using hp)
      _ = _ := by simp
  have hH : (∑ h ∈ lines R, IncidenceAlgebra.mu ℤ h R.top) = -((lines R).card : ℤ) := by
    calc
      _ = ∑ h ∈ lines R, (-1 : ℤ) := by
        apply sum_congr rfl
        intro h hh
        exact mu_line_top R h (by simpa [lines] using hh)
      _ = _ := by simp
  have hBH : (∑ h ∈ lines R, IncidenceAlgebra.mu ℤ R.bot h) =
      (∑ h ∈ lines R, (((points R).filter (fun p => p ≤ h)).card : ℤ)) - ((lines R).card : ℤ) := by
    calc
      _ = ∑ h ∈ lines R, ((((points R).filter (fun p => p ≤ h)).card : ℤ) - 1) := by
        apply sum_congr rfl
        intro h hh
        exact mu_bot_line R h (by simpa [lines] using hh)
      _ = _ := by simp [sum_sub_distrib]
  have hPT : (∑ p ∈ points R, IncidenceAlgebra.mu ℤ p R.top) =
      (∑ p ∈ points R, (((lines R).filter (fun h => p ≤ h)).card : ℤ)) - ((points R).card : ℤ) := by
    calc
      _ = ∑ p ∈ points R, ((((lines R).filter (fun h => p ≤ h)).card : ℤ) - 1) := by
        apply sum_congr rfl
        intro p hp
        exact mu_point_top R p (by simpa [points] using hp)
      _ = _ := by simp [sum_sub_distrib]
  rw [hP,hH,hBH,hPT,incidence_count]
  simp only [IncidenceAlgebra.mu_self]
  ring
private theorem rank_three_mu_evaluation :
    (∑ x, ∑ y, ∑ z, IncidenceAlgebra.mu ℤ x y * IncidenceAlgebra.mu ℤ y z *
       (-1 : ℤ) ^ (9 - R.rank x - R.rank y - R.rank z)) =
    2 * (((lines R).card : ℤ) - ((points R).card : ℤ)) := by
  rw [signed_middle_factor,sum_layers R]
  have hP : (∑ p ∈ points R, -((-1 : ℤ)^R.rank p * signedLower R p * signedUpper R p)) =
      4 * ∑ p ∈ points R, (((lines R).filter (fun h => p ≤ h)).card : ℤ) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro p hp
    have hr : R.rank p = 1 := by simpa [points] using hp
    rw [signedLower_point R p hr,signedUpper_point R p hr,hr]
    ring
  have hH : (∑ h ∈ lines R, -((-1 : ℤ)^R.rank h * signedLower R h * signedUpper R h)) =
      -4 * ∑ h ∈ lines R, (((points R).filter (fun p => p ≤ h)).card : ℤ) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro h hh
    have hr : R.rank h = 2 := by simpa [lines] using hh
    rw [signedLower_line R h hr,signedUpper_line R h hr,hr]
    ring
  rw [hP,hH,signedLower_bot,signedUpper_top,R.rank_bot,R.rank_top,incidence_count]
  have hs := endpoint_sum R
  norm_num
  linarith
end D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius.Graded
namespace D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius
noncomputable section
open Finset Polynomial
variable {α : Type*} [Finite α] (M : Matroid α)
private def rankThreeFrame (hM : M.eRank = 3) : D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius.Graded.RankThreeFrame (Flats M) where
  rank F := rk M F.1
  bot := bottomFlat M
  top := topFlat M
  bot_le := bottom_le M
  le_top := le_top M
  rank_bot := rk_bottom M
  rank_top := rk_top M hM
  strict := fun _ _ h => rk_lt_of_lt M h
private lemma eval_as_mu_sum (hM : M.eRank = 3)
    (J : Flats M → Flats M → Flats M → ℤ) (hJ : IsJFunction M J) :
    (MoebiusPoly M J).eval (-1) =
    ∑ x : Flats M, ∑ y : Flats M, ∑ z : Flats M, IncidenceAlgebra.mu ℤ x y * IncidenceAlgebra.mu ℤ y z *
      (-1 : ℤ)^(9 - rk M x.1 - rk M y.1 - rk M z.1) := by
  have ht : rk M M.E = 3 := rk_top M hM
  simp only [MoebiusPoly,finsum_eq_sum_of_fintype,finsum_eq_if,
    Polynomial.eval_finsetSum,apply_ite,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_zero,ht]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro z _
  by_cases hf : x ≤ y ∧ y ≤ z
  · rw [if_pos hf,j_eq_mu_product M J hJ x y z hf.1 hf.2]
  · rw [if_neg hf]
    by_cases hxy : x ≤ y
    · have hyz : ¬y ≤ z := fun hh => hf ⟨hxy,hh⟩
      simp [IncidenceAlgebra.apply_eq_zero_of_not_le hyz]
    · simp [IncidenceAlgebra.apply_eq_zero_of_not_le hxy]
private theorem moebius_eval_neg_one (hM : M.eRank = 3)
    (J : Flats M → Flats M → Flats M → ℤ) (hJ : IsJFunction M J) :
    (MoebiusPoly M J).eval (-1) =
      2 * ((Fintype.card (Lines M) : ℤ) - (Fintype.card (Points M) : ℤ)) := by
  rw [eval_as_mu_sum M hM J hJ]
  have hs := D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius.Graded.rank_three_mu_evaluation (rankThreeFrame M hM)
  convert hs using 1 <;> simp only [rankThreeFrame,D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius.Graded.points,D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius.Graded.lines,Fintype.card_subtype]
  all_goals congr 1
theorem result : claim := by
  intro α _ M hM _ hmod J hJ
  classical
  have he := moebius_eval_neg_one M hM J hJ
  have hi := nonmodular_more_lines M hM hmod
  have hiz : (Fintype.card (Points M) : ℤ) < Fintype.card (Lines M) := by exact_mod_cast hi
  omega
end
end D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius
