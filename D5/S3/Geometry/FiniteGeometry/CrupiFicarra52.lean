/- GID: D5/S3/Geometry/FiniteGeometry/CrupiFicarra52
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGeometry/CrupiFicarra52
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Crupi–Ficarra Question 5.2 has sharp maximum q² − q + 1 over finite fields, q ≥ 5. -/

import Mathlib.Combinatorics.Configuration
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import D5.S3.Geometry.FiniteGeometry.AffinePlaneLines

import OmegaBuild.Commands

compile_only_with_mathlib

/- proof_shape: result: content
   admission_basis: open-problem-resolution (#34623)
   The construction omits an affine parabola, using a polynomial root bound on
   nonvertical lines. The upper bound injects two disjoint families of omissions
   from the tangent and the other lines through the point of tangency. -/

/-! Crupi–Ficarra, arXiv:2507.05037v2, Definitions 2.1 and 3.1 and Question 5.2. -/

set_option autoImplicit false

open scoped LinearAlgebra.Projectivization Polynomial
open Configuration Projectivization Finset
open D5.S3.Geometry.FiniteGeometry.AffinePlaneLines

namespace D5.S3.Geometry.FiniteGeometry.CrupiFicarra52

variable {F : Type*} [Field F]

/-- Definition 2.1. -/
def BlockingSet (B : Finset (ℙ F (Fin 3 → F))) : Prop :=
  (∀ l : ℙ F (Fin 3 → F), ∃ p ∈ B, p ∈ l) ∧
  (∀ l : ℙ F (Fin 3 → F), ¬ ∀ p : ℙ F (Fin 3 → F), p ∈ l → p ∈ B)

/-- A line through `p` such that any point of `B` on the line equals `p`.
    Membership `p ∈ B` is supplied by `RInfinity`. -/
def TangentAt (B : Finset (ℙ F (Fin 3 → F))) (p l : ℙ F (Fin 3 → F)) : Prop :=
  p ∈ l ∧ ∀ x ∈ B, x ∈ l → x = p

/-- Definition 3.1, with the secant clause stated explicitly. -/
def RInfinity (B : Finset (ℙ F (Fin 3 → F))) : Prop :=
  ∃ p ∈ B, ∃ t : ℙ F (Fin 3 → F), TangentAt B p t ∧
    ∀ l : ℙ F (Fin 3 → F), p ∈ l → l ≠ t → ∃ x ∈ B, x ∈ l ∧ x ≠ p

private def affine (x y : F) : ℙ F (Fin 3 → F) :=
  mk F ![x, y, 1] (by
    intro h
    have h2 := congrFun h (2 : Fin 3)
    simp at h2)

private def verticalPoint : ℙ F (Fin 3 → F) :=
  mk F ![0, 1, 0] (by
    intro h
    have h1 := congrFun h (1 : Fin 3)
    simp at h1)

private def infinity : ℙ F (Fin 3 → F) :=
  mk F ![0, 0, 1] (by
    intro h
    have h2 := congrFun h (2 : Fin 3)
    simp at h2)

private def direction (m : F) : ℙ F (Fin 3 → F) :=
  mk F ![1, m, 0] (by
    intro h
    have h0 := congrFun h (0 : Fin 3)
    simp at h0)

/-- Extend the repository's affine lines into Mathlib's projective plane. -/
private def closeLine : AffineLine F → ℙ F (Fin 3 → F)
  | .vertical c => mk F ![1, 0, -c] (by
      intro h
      have h0 := congrFun h (0 : Fin 3)
      simp at h0)
  | .graph m b => mk F ![-m, 1, -b] (by
      intro h
      have h1 := congrFun h (1 : Fin 3)
      simp at h1)

private theorem affine_incidence (p : F × F) (l : AffineLine F) :
    affine p.1 p.2 ∈ closeLine l ↔ p ∈ l := by
  cases l with
  | vertical c =>
    change (_ ∈ _) ↔ p.1 = c
    simp [affine, closeLine, ofField.mem_iff, orthogonal_mk, dotProduct, Fin.sum_univ_succ,
      ← sub_eq_add_neg, sub_eq_zero]
  | graph m b =>
    change (_ ∈ _) ↔ p.2 = m * p.1 + b
    simp only [affine, closeLine, ofField.mem_iff, orthogonal_mk, dotProduct, Fin.sum_univ_succ]
    simp
    constructor <;> intro h <;> linear_combination h

private theorem affine_not_infinity (x y : F) : affine x y ∉ (infinity : ℙ F (Fin 3 → F)) := by
  simp [affine, infinity, ofField.mem_iff, orthogonal_mk, dotProduct, Fin.sum_univ_succ]

private theorem verticalPoint_infinity : (verticalPoint : ℙ F (Fin 3 → F)) ∈ (infinity : ℙ F (Fin 3 → F)) := by
  simp [verticalPoint, infinity, ofField.mem_iff, orthogonal_mk, dotProduct, Fin.sum_univ_succ]

private theorem direction_infinity (m : F) : direction m ∈ (infinity : ℙ F (Fin 3 → F)) := by
  simp [direction, infinity, ofField.mem_iff, orthogonal_mk, dotProduct, Fin.sum_univ_succ]

private theorem direction_ne_verticalPoint (m : F) : direction m ≠ verticalPoint := by
  intro h
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff' _ _ _ _ _).mp h
  have h0 := congrFun ha (0 : Fin 3)
  simp at h0

private theorem verticalPoint_not_graph (m b : F) :
    (verticalPoint : ℙ F (Fin 3 → F)) ∉ closeLine (.graph m b) := by
  simp [verticalPoint, closeLine, ofField.mem_iff, orthogonal_mk, dotProduct, Fin.sum_univ_succ]

private theorem direction_graph (m b : F) : direction m ∈ closeLine (.graph m b) := by
  simp [direction, closeLine, ofField.mem_iff, orthogonal_mk, dotProduct, Fin.sum_univ_succ]

/-- Every projective line is infinity or the closure of an affine line. -/
private theorem classify_line (l : ℙ F (Fin 3 → F)) : l = infinity ∨ ∃ a : AffineLine F, l = closeLine a := by
  induction l using Projectivization.ind with
  | h v hv =>
    by_cases hb : v 1 = 0
    · by_cases ha : v 0 = 0
      · have hc : v 2 ≠ 0 := by
          intro hc
          apply hv
          funext i
          fin_cases i <;> simp [ha, hb, hc]
        left
        apply (mk_eq_mk_iff' _ _ _ _ _).mpr
        refine ⟨v 2, ?_⟩
        funext i
        fin_cases i <;> simp [ha, hb]
      · right
        refine ⟨.vertical (-(v 2 / v 0)), ?_⟩
        apply (mk_eq_mk_iff' _ _ _ _ _).mpr
        refine ⟨v 0, ?_⟩
        funext i
        fin_cases i <;> simp [hb, ha, mul_div_cancel₀, mul_comm]
    · right
      refine ⟨.graph (-(v 0 / v 1)) (-(v 2 / v 1)), ?_⟩
      apply (mk_eq_mk_iff' _ _ _ _ _).mpr
      refine ⟨v 1, ?_⟩
      funext i
      fin_cases i <;> simp [hb, mul_div_cancel₀, mul_comm]

private theorem affine_injective : Function.Injective (fun p : F × F => affine p.1 p.2) := by
  intro p r h
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff' _ _ _ _ _).mp h
  have ha1 : a = 1 := by simpa using congrFun ha (2 : Fin 3)
  subst a
  exact Prod.ext (by simpa using (congrFun ha (0 : Fin 3)).symm)
    (by simpa using (congrFun ha (1 : Fin 3)).symm)

private theorem affine_ne_verticalPoint (x y : F) : affine x y ≠ verticalPoint :=
  fun h => affine_not_infinity x y (h.symm ▸ verticalPoint_infinity)

noncomputable section

attribute [local instance] Classical.propDecidable

variable [Fintype F]

private noncomputable local instance projectiveFintype : Fintype (ℙ F (Fin 3 → F)) := Fintype.ofFinite _

private abbrev q (F : Type*) [Fintype F] := Fintype.card F

/-- The point at infinity of the vertical direction and the complement of the
parabola in the affine chart. -/
private def parabolaComplement (F : Type*) [Field F] [Fintype F] : Finset (ℙ F (Fin 3 → F)) :=
  insert verticalPoint
    ((univ.filter fun p : F × F => p.2 ≠ p.1 ^ 2).image fun p => affine p.1 p.2)

private theorem mem_parabolaComplement (p : ℙ F (Fin 3 → F)) :
    p ∈ parabolaComplement F ↔ p = verticalPoint ∨
      ∃ x y : F, y ≠ x ^ 2 ∧ affine x y = p := by
  simp [parabolaComplement, Prod.exists]

private theorem affine_mem_parabolaComplement (x y : F) :
    affine x y ∈ parabolaComplement F ↔ y ≠ x ^ 2 := by
  rw [mem_parabolaComplement]
  constructor
  · rintro (he | ⟨u, v, huv, he⟩)
    · exact (affine_ne_verticalPoint x y he).elim
    · have hxy : (u, v) = (x, y) := affine_injective he
      cases hxy
      exact huv
  · exact fun h => Or.inr ⟨x, y, h, rfl⟩

private theorem direction_not_mem (m : F) : direction m ∉ parabolaComplement F := by
  intro h
  rcases (mem_parabolaComplement _).mp h with he | ⟨x, y, _, he⟩
  · exact direction_ne_verticalPoint m he
  · exact affine_not_infinity x y (he.symm ▸ direction_infinity m)

private theorem card_parabolaComplement :
    (parabolaComplement F).card = q F ^ 2 - q F + 1 := by
  let graph : Finset (F × F) := univ.image (fun x : F => (x, x ^ 2))
  have hg : graph.card = q F := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h), card_univ]
  have hc : (univ.filter fun p : F × F => p.2 ≠ p.1 ^ 2) = univ \ graph := by
    ext p
    obtain ⟨x, y⟩ := p
    simp [graph, eq_comm]
  have hcard := card_sdiff_add_card_eq_card (subset_univ graph)
  rw [hg, card_univ, Fintype.card_prod, ← pow_two, ← hc] at hcard
  change (univ.filter fun p : F × F => p.2 ≠ p.1 ^ 2).card + q F = q F ^ 2 at hcard
  unfold parabolaComplement
  rw [card_insert_of_notMem, card_image_of_injective _ affine_injective]
  · omega
  · rintro h
    obtain ⟨xy, _, hxy⟩ := mem_image.mp h
    exact affine_ne_verticalPoint _ _ hxy

private def quadratic (m b : F) : F[X] :=
  Polynomial.X ^ 2 - (Polynomial.C m * Polynomial.X + Polynomial.C b)

omit [Fintype F] in
private theorem quadratic_monic (m b : F) : (quadratic m b).Monic := by
  apply Polynomial.monic_X_pow_sub
  exact Polynomial.degree_linear_lt

private theorem card_quadratic_roots (m b : F) :
    (univ.filter fun x : F => x ^ 2 = m * x + b).card ≤ 2 := by
  let f := quadratic m b
  have hdeg : f.natDegree ≤ 2 := by
    unfold f quadratic
    apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_X_pow, max_le_iff, le_refl, true_and]
    exact Polynomial.natDegree_linear_le.trans (by decide)
  have hnonzero : f ≠ 0 := (quadratic_monic m b).ne_zero
  refine (Polynomial.card_le_degree_of_subset_roots (p := f) ?_).trans hdeg
  intro x hx
  rw [Polynomial.mem_roots hnonzero, Polynomial.IsRoot]
  have he := (mem_filter.mp (Finset.mem_def.mpr hx)).2
  simp [f, quadratic, he]

private theorem vertical_retained (hq : 5 ≤ q F) (c : F) :
    ∃ p ∈ parabolaComplement F, p ∈ closeLine (.vertical c) ∧ p ≠ verticalPoint := by
  have hcard : 0 < ((univ : Finset F).erase (c ^ 2)).card := by
    rw [card_erase_of_mem (mem_univ _), card_univ]
    change 0 < q F - 1
    omega
  obtain ⟨y, hy⟩ := card_pos.mp hcard
  exact ⟨affine c y, (affine_mem_parabolaComplement c y).mpr (mem_erase.mp hy).1,
    (affine_incidence (c, y) _).mpr rfl, affine_ne_verticalPoint _ _⟩

private theorem graph_retained (hq : 5 ≤ q F) (m b : F) :
    ∃ p ∈ parabolaComplement F, p ∈ closeLine (.graph m b) := by
  let roots : Finset F := univ.filter fun x : F => x ^ 2 = m * x + b
  have hroots : roots.card ≤ 2 := card_quadratic_roots m b
  have hcard := card_sdiff_add_card_eq_card (subset_univ roots)
  rw [card_univ] at hcard
  change _ + _ = q F at hcard
  have hc : 0 < (univ \ roots).card := by omega
  obtain ⟨x, hx⟩ := card_pos.mp hc
  have hx' : m * x + b ≠ x ^ 2 := by simpa [roots, ne_comm] using hx
  exact ⟨affine x (m * x + b), (affine_mem_parabolaComplement _ _).mpr hx',
    (affine_incidence (x, _) _).mpr rfl⟩

private theorem parabola_no_line (l : ℙ F (Fin 3 → F)) :
    ¬ ∀ p : ℙ F (Fin 3 → F), p ∈ l → p ∈ parabolaComplement F := by
  rcases classify_line l with rfl | ⟨a, rfl⟩
  · exact fun h => direction_not_mem 0 (h (direction 0) (direction_infinity 0))
  · cases a with
    | vertical c =>
      intro h
      have hc := h (affine c (c ^ 2)) ((affine_incidence (c, c ^ 2) _).mpr rfl)
      exact (affine_mem_parabolaComplement c (c ^ 2)).mp hc rfl
    | graph m b =>
      exact fun h => direction_not_mem m (h (direction m) (direction_graph m b))

private theorem parabola_tangent :
    TangentAt (parabolaComplement F) verticalPoint infinity := by
  refine ⟨verticalPoint_infinity, ?_⟩
  intro p hp ht
  rcases (mem_parabolaComplement _).mp hp with he | ⟨x, y, _, he⟩
  · exact he
  · exact (affine_not_infinity x y (he.symm ▸ ht)).elim

private theorem parabolaComplement_spec (hq : 5 ≤ Fintype.card F) :
    BlockingSet (parabolaComplement F) ∧ RInfinity (parabolaComplement F) ∧
      (parabolaComplement F).card = Fintype.card F ^ 2 - Fintype.card F + 1 := by
  have hP : (verticalPoint : ℙ F (Fin 3 → F)) ∈ parabolaComplement F :=
    (mem_parabolaComplement _).mpr (Or.inl rfl)
  refine ⟨⟨?_, parabola_no_line⟩, ⟨verticalPoint, hP, infinity, parabola_tangent, ?_⟩,
    card_parabolaComplement⟩
  · intro l
    rcases classify_line l with rfl | ⟨a, rfl⟩
    · exact ⟨verticalPoint, hP, verticalPoint_infinity⟩
    · cases a with
      | vertical c =>
        obtain ⟨p, hp, hl, _⟩ := vertical_retained hq c
        exact ⟨p, hp, hl⟩
      | graph m b => exact graph_retained hq m b
  · intro l hp hl
    rcases classify_line l with he | ⟨a, rfl⟩
    · exact (hl he).elim
    · cases a with
      | vertical c => exact vertical_retained hq c
      | graph m b => exact (verticalPoint_not_graph m b hp).elim

private theorem card_PG : Fintype.card (ℙ F (Fin 3 → F)) = q F ^ 2 + q F + 1 := by
  rw [Fintype.card_eq_nat_card, Projectivization.card_of_finrank F _
    (Module.finrank_fin_fun F)]
  simp [Finset.sum_range_succ, Nat.card_eq_fintype_card, q, add_comm, add_left_comm, add_assoc]

private theorem order_PG : ProjectivePlane.order (ℙ F (Fin 3 → F)) (ℙ F (Fin 3 → F)) = q F := by
  let n := ProjectivePlane.order (ℙ F (Fin 3 → F)) (ℙ F (Fin 3 → F))
  have h : n ^ 2 + n + 1 = q F ^ 2 + q F + 1 :=
    (ProjectivePlane.card_points (ℙ F (Fin 3 → F)) (ℙ F (Fin 3 → F))).symm.trans card_PG
  rcases lt_trichotomy n (q F) with hlt | heq | hgt
  · have hsq := Nat.pow_le_pow_left hlt.le 2
    omega
  · exact heq
  · have hsq := Nat.pow_le_pow_left hgt.le 2
    omega

/-- At a point of tangency the omitted points of the tangent and one omission
on each of the other pencil lines give two disjoint families of size q. -/
private theorem card_le_of_blockingSet_rInfinity {B : Finset (ℙ F (Fin 3 → F))}
    (hB : BlockingSet B) (hR : RInfinity B) :
    B.card ≤ Fintype.card F ^ 2 - Fintype.card F + 1 := by
  classical
  obtain ⟨p, hp, t, ht, _⟩ := hR
  let T := (univ.filter fun x : ℙ F (Fin 3 → F) => x ∈ t).erase p
  let K := (univ.filter fun l : ℙ F (Fin 3 → F) => p ∈ l).erase t
  have hT : ∀ x : ↥T, (x : ℙ F (Fin 3 → F)) ≠ p ∧ (x : ℙ F (Fin 3 → F)) ∈ t := by
    rintro ⟨x, hx⟩
    simpa [T] using hx
  have hK : ∀ l : ↥K, (l : ℙ F (Fin 3 → F)) ≠ t ∧ p ∈ (l : ℙ F (Fin 3 → F)) := by
    rintro ⟨l, hl⟩
    simpa [K] using hl
  have hTc : T.card = q F := by
    have h := ProjectivePlane.pointCount_eq (ℙ F (Fin 3 → F)) t
    rw [pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype, order_PG] at h
    dsimp only [T]
    rw [card_erase_of_mem (by simp [ht.1]), h, Nat.add_sub_cancel]
  have hKc : K.card = q F := by
    have h := ProjectivePlane.lineCount_eq (ℙ F (Fin 3 → F)) p
    rw [lineCount, Nat.card_eq_fintype_card, Fintype.card_subtype, order_PG] at h
    dsimp only [K]
    rw [card_erase_of_mem (by simp [ht.1]), h, Nat.add_sub_cancel]
  have hmiss (l : ↥K) : ∃ x : ℙ F (Fin 3 → F), x ∈ (l : ℙ F (Fin 3 → F)) ∧ x ∉ B := by
    by_contra! hn
    exact hB.2 l hn
  choose miss hmline hmout using hmiss
  have hm_ne (l : ↥K) : miss l ≠ p := fun he => hmout l (he.symm ▸ hp)
  let omitted : Finset (ℙ F (Fin 3 → F)) := univ \ B
  let f : (↥T ⊕ ↥K) → ↥omitted :=
    Sum.elim
      (fun x => ⟨x, mem_sdiff.mpr ⟨mem_univ _, fun hx => (hT x).1 (ht.2 x hx (hT x).2)⟩⟩)
      (fun l => ⟨miss l, mem_sdiff.mpr ⟨mem_univ _, hmout l⟩⟩)
  have hdis (x : ↥T) (l : ↥K) : (x : ℙ F (Fin 3 → F)) ≠ miss l := by
    intro he
    have hxline : (x : ℙ F (Fin 3 → F)) ∈ (l : ℙ F (Fin 3 → F)) := he.symm ▸ hmline l
    rcases Nondegenerate.eq_or_eq (hK l).2 hxline ht.1 (hT x).2 with h | h
    · exact (hT x).1 h.symm
    · exact (hK l).1 h
  have hinj : Function.Injective f := by
    intro x y he
    have hv := congrArg Subtype.val he
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (Subtype.ext hv)
    · exact (hdis x y hv).elim
    · exact (hdis y x hv.symm).elim
    · have hxy : miss x = miss y := hv
      have hline : miss x ∈ (y : ℙ F (Fin 3 → F)) := hxy.symm ▸ hmline y
      rcases Nondegenerate.eq_or_eq (hK x).2 (hmline x) (hK y).2 hline with h | h
      · exact (hm_ne x h.symm).elim
      · exact congrArg Sum.inr (Subtype.ext h)
  have hcard := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, Fintype.card_coe, hTc, hKc] at hcard
  have htotal := card_sdiff_add_card_eq_card (subset_univ B)
  rw [card_univ, card_PG] at htotal
  change omitted.card + B.card = _ at htotal
  change B.card ≤ q F ^ 2 - q F + 1
  omega

/-- Exact maximum and a positive answer to the literal Open Question 5.2,
uniform over every finite field in its stated range. -/
theorem result (hq : 5 ≤ Fintype.card F) :
    IsGreatest {n : ℕ | ∃ B : Finset (ℙ F (Fin 3 → F)),
      BlockingSet B ∧ RInfinity B ∧ B.card = n}
      (Fintype.card F ^ 2 - Fintype.card F + 1) ∧
    3 * (Fintype.card F - 1) < Fintype.card F ^ 2 - Fintype.card F + 1 := by
  refine ⟨⟨⟨parabolaComplement F, parabolaComplement_spec hq⟩, ?_⟩, ?_⟩
  · rintro n ⟨B, hB, hR, rfl⟩
    exact card_le_of_blockingSet_rInfinity hB hR
  · have hmul : 5 * q F ≤ q F * q F := Nat.mul_le_mul_right _ hq
    change 3 * (q F - 1) < q F ^ 2 - q F + 1
    rw [pow_two]
    omega

end

end D5.S3.Geometry.FiniteGeometry.CrupiFicarra52
