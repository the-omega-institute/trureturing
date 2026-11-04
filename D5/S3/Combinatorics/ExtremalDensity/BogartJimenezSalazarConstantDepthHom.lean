/- GID: D5/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom
   generality: I
   mirror-B: D5/B/S3/Combinatorics/ExtremalDensity/BogartJimenezSalazarConstantDepthHom
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Strongly polynomial graph families have constant depth one and growing degree. -/

/-
admission_basis: open-problem-resolution (#21296; Proved)
proof_shape: bind-only for result and every consumed supporting theorem.
escape_witness: none.
Direct frozen dependencies: D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.homCount
  statement_id: sha256:0e84d5e3b05f34e2e9c280199168c3111812f728a7dbd0257cbcd019ae75f97f.
The homCount declaration is reused without a duplicate count definition.
Complete bipartite and multipartite graphs and graph comap use their Mathlib owners directly.
The claim retains the source coefficient expression inline; no codegree alias is added.
The existing Polynomial.reverse coefficient gives the same guarded expression.
The depth is maximal among uniform integer constants, as specified in issue #21296;
it is not a pointwise greatest depth function. No every-tail maximality is asserted.
The only public theorem is result. Its four-slot escape audit is unfinished: https://github.com/the-omega-institute/trureturing/issues/21427.
Utility none: unbounded existence and symbolic counting, without a finite-instance deliverable.
exponential_not_polynomial: proof_shape: bind-only; escape_witness: none; consumers: no_larger_depth.
f_coeff: proof_shape: bind-only; escape_witness: none; consumers: f_degree, f_codegrees.
f_degree: proof_shape: bind-only; escape_witness: none; consumers: f_codegrees, depth_one.
reverse_coeff: proof_shape: bind-only; escape_witness: none; consumers: f_codegrees, depth_one, no_larger_depth.
f_codegrees: proof_shape: bind-only; escape_witness: none; consumers: depth_one, no_larger_depth.
g_nonnegative: proof_shape: bind-only; escape_witness: none; consumers: depth_one, no_larger_depth.
depth_one: proof_shape: bind-only; escape_witness: none; consumers: result.
no_larger_depth: proof_shape: bind-only; escape_witness: none; consumers: result.
count_relabel: proof_shape: bind-only; escape_witness: none; consumers: exact_count.
target_colour_sum: proof_shape: bind-only; escape_witness: none; consumers: multipartite_polynomial.
multipartite_polynomial: proof_shape: bind-only; escape_witness: none; consumers: source_polynomial, target_polynomial.
bipartite_common_neighbours: proof_shape: bind-only; escape_witness: none; consumers: exact_count.
common_card: proof_shape: bind-only; escape_witness: none; consumers: target_common_card.
target_common_card: proof_shape: bind-only; escape_witness: none; consumers: exact_count.
exact_count: proof_shape: bind-only; escape_witness: none; consumers: result.
target_relabel: proof_shape: bind-only; escape_witness: none; consumers: source_polynomial, target_polynomial.
source_polynomial: proof_shape: bind-only; escape_witness: none; consumers: result.
target_polynomial: proof_shape: bind-only; escape_witness: none; consumers: result.
result: proof_shape: bind-only; escape_witness: none; consumers: external settlement.
Numerical: proof_shape: bind-only; escape_witness: none; consumers: TwoLevel.
TwoLevel: proof_shape: bind-only; escape_witness: none; consumers: claim, depth_one, no_larger_depth.
constantDepth: proof_shape: bind-only; escape_witness: none; consumers: claim, depth_one, no_larger_depth.
StronglyPolynomial: proof_shape: bind-only; escape_witness: none; consumers: claim, source_polynomial, target_polynomial.
claim: proof_shape: bind-only; escape_witness: none; consumers: result.
f: proof_shape: bind-only; escape_witness: none; consumers: f_coeff, f_degree, f_codegrees, depth_one, no_larger_depth, result.
g: proof_shape: bind-only; escape_witness: none; consumers: g_nonnegative, depth_one, no_larger_depth, result.
sizes: proof_shape: bind-only; escape_witness: none; consumers: target_common_card, exact_count, target_polynomial, result.
-/


import D5.S3.Combinatorics.ExtremalDensity.ThreeClassHomomorphismLimit
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Group.ForwardDiff

/-! Polynomial graph families for arXiv:2609.32077v1, Definitions 1.1, 1.2, 3.2 and Question 3.19.
Finite simple graphs use the existing homCount owner, on Fin-labelled carriers.
Rational polynomials suffice for functions taking integer values on all natural parameters.
The question's constant depth is read as maximal uniform constant depth, avoiding the
vacuous choice of depth -1 allowed for every family by Definition 1.2.
-/
namespace D5.S3.Combinatorics.ExtremalDensity.BogartJimenezSalazarConstantDepthHom

open Polynomial
open D5.S3.Combinatorics.ExtremalDensity.ThreeClassHomomorphismLimit (homCount)

/-- Definition 1.1: integer values at every integer, including negative integers. -/
def Numerical (g : ℚ[X]) : Prop :=
  ∀ z : ℤ, ∃ k : ℤ, g.eval (z : ℚ) = (k : ℚ)

/-- Definition 1.2(a,b), including S and the prescribed extension outside S. -/
def TwoLevel (f : ℕ → ℚ[X]) (g : ℚ[X]) (e : ℕ → WithTop ℤ) : Prop :=
  Numerical g ∧ (∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → 0 ≤ g.eval (q : ℚ)) ∧
  (∀ q : ℕ, 0 ≤ g.eval (q : ℚ) → ((-1 : ℤ) : WithTop ℤ) ≤ e q) ∧
  (∀ q : ℕ, 0 ≤ g.eval (q : ℚ) →
    f q ≠ 0 ∧ ((f q).natDegree : ℚ) = g.eval (q : ℚ)) ∧
  (∀ q : ℕ, g.eval (q : ℚ) < 0 → f q = 0 ∧ e q = ((-1 : ℤ) : WithTop ℤ)) ∧
  ∃ φ : ℕ → ℚ[X], ∀ (q : ℕ) (r : ℕ),
    0 ≤ g.eval (q : ℚ) → (r : WithTop ℤ) ≤ e q →
      (if r ≤ (f q).natDegree then (f q).coeff ((f q).natDegree - r) else 0) =
        (φ r).eval (q : ℚ)

/-- A constant depth on S; Definition 1.2(b) prescribes -1 outside S. -/
noncomputable def constantDepth (g : ℚ[X]) (d : ℤ) (q : ℕ) : WithTop ℤ :=
  if 0 ≤ g.eval (q : ℚ) then (d : WithTop ℤ) else ((-1 : ℤ) : WithTop ℤ)

/-- Definition 3.2, quantified over every fixed finite simple graph, including the empty graph. -/
def StronglyPolynomial (v : ℕ → ℕ) (G : (q : ℕ) → SimpleGraph (Fin (v q))) : Prop :=
  ∀ (a : ℕ) (F : SimpleGraph (Fin a)), ∃ p : ℚ[X],
    ∀ q : ℕ, (homCount F (G q) : ℚ) = p.eval (q : ℚ)

/-- Question 3.19, affirmative existence assertion; no particular construction is built in. -/
def claim : Prop :=
  ∃ (v : ℕ → ℕ) (w : ℕ → ℕ)
    (G : (q : ℕ) → SimpleGraph (Fin (v q)))
    (H : (n : ℕ) → SimpleGraph (Fin (w n)))
    (f : ℕ → ℚ[X]) (g : ℚ[X]) (d : ℤ),
    -1 ≤ d ∧ StronglyPolynomial v G ∧ StronglyPolynomial w H ∧
    (∀ (q : ℕ) (n : ℕ), (homCount (G q) (H n) : ℚ) = (f q).eval (n : ℚ)) ∧
    0 < g.natDegree ∧ TwoLevel f g (constantDepth g d) ∧
    (∀ d' : ℤ, d < d' → ¬ TwoLevel f g (constantDepth g d'))

end D5.S3.Combinatorics.ExtremalDensity.BogartJimenezSalazarConstantDepthHom

open Polynomial
namespace D5.S3.Combinatorics.ExtremalDensity.BogartJimenezSalazarConstantDepthHom

private theorem exponential_not_polynomial (P : ℚ[X]) :
    ¬ ∀ n : ℕ, P.eval (n : ℚ) = (2 : ℚ) ^ (n + 3) := by
  intro hP
  have hdiff : ∀ k n : ℕ, (fwdDiff (1 : ℚ))^[k] P.eval (n : ℚ) = 2 ^ (n+3) := by
    intro k
    induction k with
    | zero => simpa using hP
    | succ k ih =>
      intro n
      rw [Function.iterate_succ_apply', fwdDiff]
      rw [show (n : ℚ) + 1 = ((n+1 : ℕ) : ℚ) by simp, ih (n+1), ih n]
      rw [show n+1+3 = n+3+1 by omega, pow_succ]
      ring
  have hz : (fwdDiff (1 : ℚ))^[P.natDegree+1] P.eval ((0 : ℕ) : ℚ) = 0 :=
    congrFun P.fwdDiff_iter_degree_add_one_eq_zero (0 : ℚ)
  have hh := (hdiff (P.natDegree+1) 0).symm.trans hz
  norm_num at hh

end D5.S3.Combinatorics.ExtremalDensity.BogartJimenezSalazarConstantDepthHom

noncomputable section
open Polynomial
namespace D5.S3.Combinatorics.ExtremalDensity.BogartJimenezSalazarConstantDepthHom

private def f (q : ℕ) : ℚ[X] :=
  C 2 * ((X+1)^(q+3) * X^2) + C 4 * X^(q+4) +
    C ((2 : ℚ)^(q+3)) * X^(q+3) + C 2 * X^2

private def g : ℚ[X] := X + C 5

private theorem f_coeff (q k : ℕ) :
    (f q).coeff k =
      2 * (if 2 ≤ k then ((q+3).choose (k-2) : ℚ) else 0) +
      (if k = q+4 then 4 else 0) +
      (if k = q+3 then (2 : ℚ)^(q+3) else 0) +
      (if k = 2 then 2 else 0) := by
  unfold f
  simp only [coeff_add]
  rw [coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_X_add_one_pow]

private theorem f_degree (q : ℕ) : (f q).natDegree = q+5 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [f_coeff]
    have hchoose : (q+3).choose (k-2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hchoose, show k ≠ q+4 by omega, show k ≠ q+3 by omega, show k ≠ 2 by omega]
  · rw [f_coeff]
    norm_num [show (q+5)-2 = q+3 by omega, show q+5 ≠ q+4 by omega,
      show q+5 ≠ q+3 by omega, show q+5 ≠ 2 by omega]

private theorem reverse_coeff (p : ℚ[X]) (r : ℕ) :
    p.reverse.coeff r = if r ≤ p.natDegree then p.coeff (p.natDegree - r) else 0 := by
  rw [coeff_reverse]
  by_cases h : r ≤ p.natDegree
  · rw [ite_eq_left h, revAt_le h]
  · rw [ite_eq_right h, revAt_eq_self_of_lt (Nat.lt_of_not_ge h),
      coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge h)]

private theorem f_codegrees (q : ℕ) :
    (f q).reverse.coeff 0 = 2 ∧ (f q).reverse.coeff 1 = 2*(q : ℚ)+10 ∧
      (f q).reverse.coeff 2 = (q+3 : ℚ)*(q+2) + 2^(q+3) := by
  have h0 : (f q).reverse.coeff 0 = 2 := by
    rw [reverse_coeff]
    simp [f_degree, f_coeff, show q+5 ≠ 2 by omega]
  have h1 : (f q).reverse.coeff 1 = 2*(q : ℚ)+10 := by
    simp only [reverse_coeff, f_degree, show 1 ≤ q+5 by omega, ite_eq_left,
      show q+5-1 = q+4 by omega, f_coeff]
    simp [show 2 ≤ q+4 by omega, show q+4-2 = q+2 by omega,
      show q+4 ≠ 2 by omega, Nat.choose_succ_self_right]
    ring
  have h2 : (f q).reverse.coeff 2 = (q+3 : ℚ)*(q+2) + 2^(q+3) := by
    simp only [reverse_coeff, f_degree, show 2 ≤ q+5 by omega, ite_eq_left,
      show q+5-2 = q+3 by omega, f_coeff]
    simp only [ite_eq_left (show 2 ≤ q+3 by omega), ite_eq_right (show q+3 ≠ q+4 by omega),
      ite_eq_right (show q+3 ≠ 2 by omega), add_zero]
    rw [show q+3-2 = (q+3)-2 by rfl, Nat.choose_symm (show 2 ≤ q+3 by omega)]
    have hchoose := Nat.choose_two_right (q+3)
    have heven := Nat.even_mul_pred_self (q+3)
    have hdiv : 2 * ((q+3).choose 2) = (q+3)*(q+2) := by
      rw [hchoose, Nat.mul_div_cancel' heven.two_dvd, show q+3-1 = q+2 by omega]
    have hc : 2 * (((q+3).choose 2) : ℚ) = (q+3 : ℚ)*(q+2) := by exact_mod_cast hdiv
    rw [hc]
  exact ⟨h0,h1,h2⟩

private theorem g_nonnegative (q : ℕ) : 0 ≤ g.eval (q : ℚ) := by
  simp only [g, eval_add, eval_X, eval_C]
  positivity

private theorem depth_one : TwoLevel f g (constantDepth g 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    refine ⟨z+5, ?_⟩
    simp [g]
  · exact ⟨0,fun q _ => g_nonnegative q⟩
  · intro q hq
    simp only [constantDepth, ite_eq_left hq]
    exact WithTop.coe_le_coe.mpr (by norm_num : (-1 : ℤ) ≤ 1)
  · intro q _
    constructor
    · intro hz
      have hd := f_degree q
      rw [hz, natDegree_zero] at hd
      omega
    · simp [f_degree,g]
  · intro q hq
    exact False.elim (not_lt_of_ge (g_nonnegative q) hq)
  · refine ⟨fun r => if r = 0 then C 2 else if r = 1 then C 2 * X + C 10 else 0, ?_⟩
    intro q r _ hr
    have hr1 : r ≤ 1 := by
      simpa [constantDepth,g_nonnegative] using hr
    interval_cases r
    · rw [← reverse_coeff]
      simpa using (f_codegrees q).1
    · rw [← reverse_coeff]
      simpa using (f_codegrees q).2.1

private theorem no_larger_depth (d : ℤ) (hd : 1 < d) :
    ¬ TwoLevel f g (constantDepth g d) := by
  intro h
  obtain ⟨φ,hφ⟩ := h.2.2.2.2.2
  let P := φ 2 - (X + C 3)*(X + C 2)
  apply exponential_not_polynomial P
  intro q
  have he := hφ q 2 (g_nonnegative q) (by
    simp only [constantDepth, ite_eq_left (g_nonnegative q)]
    exact WithTop.coe_le_coe.mpr (show (2 : ℤ) ≤ d by omega))
  rw [← reverse_coeff, (f_codegrees q).2.2] at he
  dsimp [P]
  simp only [eval_sub, eval_mul, eval_add, eval_X, eval_C]
  linarith

end D5.S3.Combinatorics.ExtremalDensity.BogartJimenezSalazarConstantDepthHom

noncomputable section
open Finset Polynomial
open D5.S3.Combinatorics.ExtremalDensity.ThreeClassHomomorphismLimit (homCount)
namespace D5.S3.Combinatorics.ExtremalDensity.BogartJimenezSalazarConstantDepthHom
attribute [local instance] Classical.propDecidable

private theorem count_relabel {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    homCount ((G).comap (Fintype.equivFin _).symm) ((H).comap (Fintype.equivFin _).symm) =
      Nat.card {f : V → W // ∀ i j, G.Adj i j → H.Adj (f i) (f j)} := by
  classical
  apply Nat.card_congr
  let e := Fintype.equivFin V
  let d := Fintype.equivFin W
  exact
    { toFun := fun f => ⟨fun v => d.symm (f.val (e v)), by
        intro i j h
        exact f.property (e i) (e j) (by simpa [SimpleGraph.comap, e] using h)⟩
      invFun := fun f => ⟨fun v => d (f.val (e.symm v)), by
        intro i j h
        simpa [SimpleGraph.comap, d] using f.property (e.symm i) (e.symm j) h⟩
      left_inv := by intro f; apply Subtype.ext; funext i; simp
      right_inv := by intro f; apply Subtype.ext; funext i; simp }

private theorem target_colour_sum {V I : Type} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (s : I → ℕ) :
    Nat.card {f : V → (Σ c, Fin (s c)) //
      ∀ i j, G.Adj i j → (f i).1 ≠ (f j).1} =
    ∑ c : {c : V → I // ∀ i j, G.Adj i j → c i ≠ c j},
      ∏ i, s (c.val i) := by
  classical
  let e : {f : V → (Σ c, Fin (s c)) //
      ∀ i j, G.Adj i j → (f i).1 ≠ (f j).1} ≃
      (Σ c : {c : V → I // ∀ i j, G.Adj i j → c i ≠ c j},
        (i : V) → Fin (s (c.val i))) :=
    { toFun := fun f => ⟨⟨fun i => (f.val i).1, f.property⟩, fun i => (f.val i).2⟩
      invFun := fun p => ⟨fun i => ⟨p.1.val i, p.2 i⟩, p.1.property⟩
      left_inv := by intro f; rfl
      right_inv := by intro p; rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro c _
  rw [Nat.card_pi]
  simp

-- The single combinatorial input to strong polynomiality: fixed colourings and independent lifts.
private theorem multipartite_polynomial {V I : Type} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (s : ℕ → I → ℕ) (p : I → ℚ[X])
    (hp : ∀ q c, (s q c : ℚ) = (p c).eval (q : ℚ)) :
    ∃ P : ℚ[X], ∀ q : ℕ,
      (Nat.card {f : V → (Σ c, Fin (s q c)) //
        ∀ i j, G.Adj i j → (f i).1 ≠ (f j).1} : ℚ) = P.eval (q : ℚ) := by
  classical
  refine ⟨∑ c : {c : V → I // ∀ i j, G.Adj i j → c i ≠ c j},
    ∏ i, p (c.val i), ?_⟩
  intro q
  simp only [target_colour_sum, Nat.cast_sum, Nat.cast_prod, eval_finsetSum,
    eval_prod, hp]

private def sizes (n : ℕ) : Fin 3 → ℕ := ![1,n,n]

private theorem bipartite_common_neighbours {m : ℕ} {W : Type} [Fintype W]
    (H : SimpleGraph W) :
    Nat.card {f : (Fin m ⊕ Fin 2) → W //
      ∀ i j, (completeBipartiteGraph (Fin m) (Fin 2)).Adj i j → H.Adj (f i) (f j)} =
    ∑ u : W, ∑ v : W, (Nat.card {x : W // H.Adj x u ∧ H.Adj x v}) ^ m := by
  classical
  let e : {f : (Fin m ⊕ Fin 2) → W //
      ∀ i j, (completeBipartiteGraph (Fin m) (Fin 2)).Adj i j → H.Adj (f i) (f j)} ≃
      (Σ u : W, Σ v : W, Fin m → {x : W // H.Adj x u ∧ H.Adj x v}) :=
    { toFun := fun f => ⟨f.val (.inr 0), f.val (.inr 1), fun i =>
        ⟨f.val (.inl i), f.property _ _ (by simp [completeBipartiteGraph_adj]),
          f.property _ _ (by simp [completeBipartiteGraph_adj])⟩⟩
      invFun := fun p => ⟨Sum.elim (fun i => (p.2.2 i).val) ![p.1,p.2.1], by
        intro i j hij
        cases i with
        | inl i =>
          cases j with
          | inl j => simp [completeBipartiteGraph_adj] at hij
          | inr j => fin_cases j; exact (p.2.2 i).property.1; exact (p.2.2 i).property.2
        | inr i =>
          cases j with
          | inl j => fin_cases i; exact (p.2.2 j).property.1.symm; exact (p.2.2 j).property.2.symm
          | inr j => simp [completeBipartiteGraph_adj] at hij⟩
      left_inv := by
        intro f; apply Subtype.ext; funext i
        cases i with
        | inl i => rfl
        | inr i => fin_cases i <;> rfl
      right_inv := by intro p; rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro u _
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro v _
  simp

private theorem common_card {I : Type} [Fintype I] (s : I → ℕ)
    (u v : Σ c, Fin (s c)) :
    Nat.card {x : (Σ c, Fin (s c)) // x.1 ≠ u.1 ∧ x.1 ≠ v.1} =
      ∑ c : I, if c ≠ u.1 ∧ c ≠ v.1 then s c else 0 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeSigmaEquiv (fun c => Fin (s c))
    (fun c => c ≠ u.1 ∧ c ≠ v.1)), Nat.card_sigma]
  simp only [Nat.card_fin]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (univ.filter (fun c => c ≠ u.1 ∧ c ≠ v.1))
    (by intro c; simp) s).symm

private theorem target_common_card (n : ℕ) (u v : (Σ c, Fin (sizes n c))) :
    Nat.card {x : (Σ c, Fin (sizes n c)) // (SimpleGraph.completeMultipartiteGraph (fun c => Fin (sizes n c))).Adj x u ∧ (SimpleGraph.completeMultipartiteGraph (fun c => Fin (sizes n c))).Adj x v} =
      if u.1 = v.1 then (if u.1 = 0 then 2*n else n+1)
      else (if u.1 = 0 ∨ v.1 = 0 then n else 1) := by
  classical
  change Nat.card {x : (Σ c, Fin (sizes n c)) // x.1 ≠ u.1 ∧ x.1 ≠ v.1} = _
  rw [common_card]
  generalize hu : u.1 = a
  generalize hv : v.1 = b
  fin_cases a <;> fin_cases b <;> simp [sizes, Fin.sum_univ_succ] <;> omega

private theorem exact_count (m n : ℕ) :
    homCount (((completeBipartiteGraph (Fin m) (Fin 2))).comap (Fintype.equivFin _).symm) (((SimpleGraph.completeMultipartiteGraph (fun c => Fin (sizes n c)))).comap (Fintype.equivFin _).symm) =
      2*n^2*(n+1)^m + 4*n^(m+1) + 2^m*n^m + 2*n^2 := by
  classical
  rw [count_relabel, bipartite_common_neighbours]
  simp_rw [target_common_card]
  simp only [Fintype.sum_sigma]
  dsimp +instances [sizes]
  simp +instances [Fin.sum_univ_succ, pow_succ, mul_pow]
  ring

end D5.S3.Combinatorics.ExtremalDensity.BogartJimenezSalazarConstantDepthHom

noncomputable section
open Finset Polynomial
open D5.S3.Combinatorics.ExtremalDensity.ThreeClassHomomorphismLimit (homCount)
namespace D5.S3.Combinatorics.ExtremalDensity.BogartJimenezSalazarConstantDepthHom

private theorem target_relabel {a : ℕ} {W : Type} [Fintype W]
    (F : SimpleGraph (Fin a)) (H : SimpleGraph W) :
    homCount F ((H).comap (Fintype.equivFin _).symm) =
      Nat.card {f : Fin a → W // ∀ i j, F.Adj i j → H.Adj (f i) (f j)} := by
  classical
  apply Nat.card_congr
  let d := Fintype.equivFin W
  exact
    { toFun := fun f => ⟨fun v => d.symm (f.val v), f.property⟩
      invFun := fun f => ⟨fun v => d (f.val v), by
        intro i j h
        simpa [SimpleGraph.comap, d] using f.property i j h⟩
      left_inv := by intro f; apply Subtype.ext; funext i; simp
      right_inv := by intro f; apply Subtype.ext; funext i; simp }

private theorem source_polynomial :
    StronglyPolynomial (fun q => Fintype.card (Fin (q+3) ⊕ Fin 2))
      (fun q => ((completeBipartiteGraph (Fin (q+3)) (Fin 2)).comap (Fintype.equivFin _).symm)) := by
  classical
  let bipSigma (m : ℕ) : (Fin m ⊕ Fin 2) ≃ (Σ c : Bool, Fin (if c then 2 else m)) :=
    (Equiv.sumEquivSigmaBool (Fin m) (Fin 2)).trans
      (Equiv.sigmaCongrRight (fun c => by cases c <;> exact Equiv.refl _))
  intro a F
  obtain ⟨P,hP⟩ := multipartite_polynomial F (fun q (c : Bool) => if c then 2 else q+3)
    (fun c : Bool => if c then C 2 else X+C 3) (by intro q c; cases c <;> simp)
  refine ⟨P, ?_⟩
  intro q
  rw [target_relabel]
  convert hP q using 2
  apply Nat.card_congr
  have he (x y : Fin (q+3) ⊕ Fin 2) :
      (completeBipartiteGraph (Fin (q+3)) (Fin 2)).Adj x y ↔
        (bipSigma (q+3) x).1 ≠ (bipSigma (q+3) y).1 := by
    cases x <;> cases y <;>
      simp [completeBipartiteGraph_adj, bipSigma, Equiv.sumEquivSigmaBool, Equiv.sigmaCongrRight]
  exact
    { toFun := fun f => ⟨fun i => bipSigma (q+3) (f.val i), by
        intro i j h
        exact (he _ _).mp (f.property i j h)⟩
      invFun := fun f => ⟨fun i => (bipSigma (q+3)).symm (f.val i), by
        intro i j h
        apply (he _ _).mpr
        simpa only [Equiv.apply_symm_apply] using f.property i j h⟩
      left_inv := by intro f; apply Subtype.ext; funext i; simp
      right_inv := by intro f; apply Subtype.ext; funext i; simp }

private theorem target_polynomial :
    StronglyPolynomial (fun n => Fintype.card (Σ c, Fin (sizes n c)))
      (fun n => ((SimpleGraph.completeMultipartiteGraph (fun c => Fin (sizes n c))).comap (Fintype.equivFin _).symm)) := by
  classical
  intro a F
  obtain ⟨P,hP⟩ := multipartite_polynomial F sizes ![C 1,X,X]
    (by intro q c; fin_cases c <;> simp [sizes])
  refine ⟨P, fun q => ?_⟩
  rw [target_relabel]
  exact hP q

end D5.S3.Combinatorics.ExtremalDensity.BogartJimenezSalazarConstantDepthHom

namespace D5.S3.Combinatorics.ExtremalDensity.BogartJimenezSalazarConstantDepthHom
open Polynomial

theorem result : claim := by
  refine ⟨(fun q => Fintype.card (Fin (q+3) ⊕ Fin 2)),
    (fun n => Fintype.card (Σ c, Fin (sizes n c))),
    (fun q => ((completeBipartiteGraph (Fin (q+3)) (Fin 2)).comap (Fintype.equivFin _).symm)), (fun n => ((SimpleGraph.completeMultipartiteGraph (fun c => Fin (sizes n c))).comap (Fintype.equivFin _).symm)),
    f, g, 1, by norm_num, source_polynomial, target_polynomial, ?_, ?_, depth_one,
    no_larger_depth⟩
  · intro q n
    rw [exact_count]
    simp only [f, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  · norm_num [g]

end D5.S3.Combinatorics.ExtremalDensity.BogartJimenezSalazarConstantDepthHom
