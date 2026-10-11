/- GID: D5/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/ThreeOutcomePermutationallyInvariantBell
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Five three-outcome PI Bell inequalities hold for every party count. -/

/-
   result: proof_shape: content
   escape_witness: G_nonneg, row3poly_nonneg
   admission_basis: open-problem-resolution (#15121; Proved)
   Direct frozen dependencies (declaration statement_ids):
   F1 = D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.windowLaw
     sha256:e659fbf42bd5c2a9797665be8c0807cda1de8ed38161a59700687ffe8fb9ec21
   F2 = D5/S3/Entropy/NamingWindow/GreenClassWindowEntropy.windowLaw_sum_eq_one
     sha256:99beffbabca86a9230b0d97375009a89cfc9e4f300af741ebc292c228e915a2f
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15148
   Utility none: general inequalities, not certified computational instances.
   The only public theorem is result; implementation lemmas are private.
   Definitions and finite-sum identities are bind-only bookkeeping.
   G_nonneg, row3_small and row3poly_nonneg establish piecewise integer estimates.
   Their integer case estimates survive the normalization-only bypass test.
   The five row identities use polynomial normalization and remain bind-only.
   Per-declaration classification (same-delivery helpers inlined):
   mass_product_moment: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: F1;
     consumers: mass_pair_moment, mass_single_moment.
   mass_single_moment: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: F1;
     consumers: one_marginal, q_marginal.
   mass_pair_moment: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: F1;
     consumers: two_marginal.
   q_normalized: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: F2;
     consumers: bell_average, one_marginal, two_marginal.
   q_marginal: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: F1;
     consumers: one_marginal, two_marginal.
   one_marginal: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: F1,F2;
     consumers: P1_average.
   two_marginal: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: F1,F2;
     consumers: P2_average.
   P1: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: P1_average, Pt0, bell_average, deterministic_bell.
   P2: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: P2_average, Pt00, Pt01, Pt10, Pt11, bell_average, deterministic_bell.
   Pt0: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: bell, bell_average, deterministic_bell.
   Pt00: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: bell, bell_average, deterministic_bell.
   Pt01: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: bell, bell_average, deterministic_bell.
   Pt10: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: bell, bell_average, deterministic_bell.
   Pt11: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: bell, bell_average, deterministic_bell.
   bell: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: bell_average, claim, deterministic_bell, deterministic_validity, model_nonneg.
   table: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: claim, countBell_nonneg, deterministic_validity, model_nonneg, row1_certificate, row2_certificate, row3_certificate, row4_certificate, row5_certificate.
   claim: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: result.
   ca: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell, countBell_nonneg, cr, deterministic_count_formula, row1_certificate, row2_certificate, row3_certificate, row4_certificate, row5_certificate.
   cb: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell, countBell_nonneg, cr, deterministic_count_formula, row1_certificate, row2_certificate, row3_certificate, row4_certificate, row5_certificate.
   cc: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell, countBell_nonneg, cs, deterministic_count_formula, row1_certificate, row2_certificate, row3_certificate, row4_certificate, row5_certificate.
   cd: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell, countBell_nonneg, cs, deterministic_count_formula, row1_certificate, row2_certificate, row3_certificate, row4_certificate, row5_certificate.
   cr: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell, countBell_nonneg, deterministic_count_formula, row1_certificate, row2_certificate, row3_certificate, row4_certificate, row5_certificate.
   cs: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell, countBell_nonneg, deterministic_count_formula, row1_certificate, row2_certificate, row3_certificate, row4_certificate, row5_certificate.
   ck: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell_nonneg, row2_certificate, row3_certificate.
   countBell: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell_nonneg, deterministic_count_formula, deterministic_validity, row1_certificate, row2_certificate, row3_certificate, row4_certificate, row5_certificate.
   counts: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: deterministic_count_formula, deterministic_validity, diagonal_cross, marginal_col, marginal_row.
   m1: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: P1_average, bell_average, detBell, deterministic_bell, deterministic_count_formula, diagonal_same, marginal_col, marginal_row, off_diagonal.
   m2: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: P2_average, bell_average, detBell, deterministic_bell, deterministic_count_formula, off_diagonal.
   off_diagonal: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: deterministic_count_formula.
   diagonal_same: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: deterministic_count_formula.
   diagonal_diff: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: deterministic_count_formula.
   diagonal_cross: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: deterministic_count_formula.
   marginal_row: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: deterministic_count_formula.
   marginal_col: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: deterministic_count_formula.
   detBell: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: bell_average, deterministic_bell, deterministic_count_formula, deterministic_validity, model_nonneg.
   deterministic_count_formula: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: deterministic_validity.
   P1_average: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: F1,F2;
     consumers: bell_average.
   P2_average: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: F1,F2;
     consumers: bell_average.
   bell_average: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: F1,F2;
     consumers: model_nonneg.
   G: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: G_nonneg, countBell_nonneg, row4_certificate, row5_certificate.
   adjacent_nonneg: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: G_nonneg, row3_small.
   G_nonneg: proof_shape: content; escape_witness: G_nonneg;
     direct frozen dependencies: none;
     consumers: countBell_nonneg.
   row1_certificate: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell_nonneg.
   row2_certificate: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell_nonneg.
   row3_certificate: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell_nonneg.
   row4_certificate: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell_nonneg.
   row5_certificate: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell_nonneg.
   row3poly: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: countBell_nonneg, row3_small, row3poly_nonneg.
   row3_small: proof_shape: content; escape_witness: row3_small;
     direct frozen dependencies: none;
     consumers: row3poly_nonneg.
   row3poly_nonneg: proof_shape: content; escape_witness: row3poly_nonneg;
     direct frozen dependencies: none;
     consumers: countBell_nonneg.
   countBell_nonneg: proof_shape: content; escape_witness: G_nonneg, row3poly_nonneg;
     direct frozen dependencies: none;
     consumers: deterministic_validity.
   deterministic_bell: proof_shape: bind-only; escape_witness: none;
     direct frozen dependencies: none;
     consumers: deterministic_validity, model_nonneg.
   deterministic_validity: proof_shape: content; escape_witness: G_nonneg, row3poly_nonneg;
     direct frozen dependencies: none;
     consumers: model_nonneg.
   model_nonneg: proof_shape: content; escape_witness: G_nonneg, row3poly_nonneg;
     direct frozen dependencies: F1,F2;
     consumers: result.
   result: proof_shape: content; escape_witness: G_nonneg, row3poly_nonneg;
     direct frozen dependencies: F1,F2;
     consumers: settling result.
-/

import D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Quantum.Entanglement.ThreeOutcomePermutationallyInvariantBell
open scoped BigOperators
open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
private theorem mass_product_moment {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    (r f : I → O → Real) :
    ∑ s : I → O, windowLaw r s * (∏ i, f i (s i)) = ∏ i, ∑ a, r i a * f i a := by
  classical
  simp_rw [windowLaw, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => r i a*f i a)).symm

private theorem mass_single_moment {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    (r : I → O → Real) (hn : ∀ i, ∑ a, r i a = 1) (i : I) (f : O → Real) :
    ∑ s : I → O, windowLaw r s * f (s i) = ∑ a, r i a * f a := by
  classical
  have h := mass_product_moment r (fun j a => if j=i then f a else 1)
  have hs (j : I) : (∑ a, r j a * (if j=i then f a else 1)) =
      (if j=i then ∑ a, r i a*f a else 1) := by
    by_cases hi : j=i
    · subst j; simp
    · simp [hi,hn]
  simpa only [Finset.prod_ite_eq',Finset.mem_univ,if_true,hs] using h

private theorem mass_pair_moment {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    (r : I → O → Real) (hn : ∀ i, ∑ a, r i a = 1) (i j : I) (hij : i ≠ j)
    (f g : O → Real) :
    ∑ s : I → O, windowLaw r s * (f (s i)*g (s j)) =
      (∑ a, r i a * f a)*(∑ a, r j a * g a) := by
  classical
  have h := mass_product_moment r
    (fun k a => (if k=i then f a else 1)*(if k=j then g a else 1))
  have hf (k : I) : (∑ a, r k a * ((if k=i then f a else 1)*(if k=j then g a else 1))) =
      (if k=i then ∑ a, r i a*f a else 1)*(if k=j then ∑ a, r j a*g a else 1) := by
    by_cases hi : k=i
    · subst k
      simp [hij]
    · by_cases hj : k=j
      · subst k
        simp [hi]
      · simp [hi,hj,hn]
  simp_rw [Finset.prod_mul_distrib] at h
  simpa only [Finset.prod_ite_eq', Finset.mem_univ, if_true, hf,
    Finset.prod_mul_distrib] using h


private theorem q_normalized {N : Nat} (r : Fin N → Fin 2 → Fin 3 → Real)
    (hn : ∀ i x, ∑ a, r i x a = 1) (i : Fin N) : ∑ t, windowLaw (r i) t = 1 := by
  exact windowLaw_sum_eq_one (r i) (hn i)

private theorem q_marginal {N : Nat} (r : Fin N → Fin 2 → Fin 3 → Real)
    (hn : ∀ i x, ∑ a, r i x a = 1) (i : Fin N) (x : Fin 2) (a : Fin 3) :
    ∑ t, windowLaw (r i) t * Pi.single (M := fun _ => Real) a 1 (t x) = r i x a := by
  rw [mass_single_moment (r i) (hn i) x (fun t => Pi.single (M := fun _ => Real) a 1 t)]
  simp [Pi.single_apply, eq_comm]

private theorem one_marginal {N : Nat} (r : Fin N → Fin 2 → Fin 3 → Real)
    (hn : ∀ i x, ∑ a, r i x a = 1) (i : Fin N) (x : Fin 2) (a : Fin 3) :
    ∑ s, windowLaw ((fun i => windowLaw (r i))) s * Pi.single (M := fun _ => Real) a 1 (s i x) = r i x a := by
  rw [mass_single_moment ((fun i => windowLaw (r i))) (q_normalized r hn) i (fun t => Pi.single (M := fun _ => Real) a 1 (t x)),q_marginal r hn]

private theorem two_marginal {N : Nat} (r : Fin N → Fin 2 → Fin 3 → Real)
    (hn : ∀ i x, ∑ a, r i x a = 1) (i j : Fin N) (hij : i ≠ j)
    (x y : Fin 2) (a b : Fin 3) :
    ∑ s, windowLaw ((fun i => windowLaw (r i))) s * (Pi.single (M := fun _ => Real) a 1 (s i x)*Pi.single (M := fun _ => Real) b 1 (s j y)) = r i x a*r j y b := by
  rw [mass_pair_moment ((fun i => windowLaw (r i))) (q_normalized r hn) i j hij (fun t => Pi.single (M := fun _ => Real) a 1 (t x)) (fun t => Pi.single (M := fun _ => Real) b 1 (t y)),
    q_marginal r hn,q_marginal r hn]

variable {N : Nat} {L : Type} [Fintype L]

noncomputable def P1 (w : L → Real) (p : L → Fin N → Fin 2 → Fin 3 → Real)
    (a : Fin 3) (x : Fin 2) : Real := ∑ l, w l * ∑ i, p l i x a

noncomputable def P2 (w : L → Real) (p : L → Fin N → Fin 2 → Fin 3 → Real)
    (a b : Fin 3) (x y : Fin 2) : Real :=
  ∑ l, w l * ∑ i, ∑ j ∈ Finset.univ.erase i, p l i x a * p l j y b

noncomputable def Pt0 (w : L → Real) (p : L → Fin N → Fin 2 → Fin 3 → Real) : Real :=
  P1 w p 0 0 + P1 w p 0 1 + P1 w p 1 0 + P1 w p 1 1
noncomputable def Pt00 (w : L → Real) (p : L → Fin N → Fin 2 → Fin 3 → Real) : Real :=
  P2 w p 0 0 0 0 + P2 w p 0 0 1 1 + P2 w p 1 1 0 0 + P2 w p 1 1 1 1
noncomputable def Pt01 (w : L → Real) (p : L → Fin N → Fin 2 → Fin 3 → Real) : Real :=
  P2 w p 0 1 0 1 + P2 w p 1 0 0 1
noncomputable def Pt10 (w : L → Real) (p : L → Fin N → Fin 2 → Fin 3 → Real) : Real :=
  P2 w p 0 0 0 1 + P2 w p 1 1 0 1
noncomputable def Pt11 (w : L → Real) (p : L → Fin N → Fin 2 → Fin 3 → Real) : Real :=
  P2 w p 0 1 0 0 + P2 w p 0 1 1 1
noncomputable def bell (w : L → Real) (p : L → Fin N → Fin 2 → Fin 3 → Real)
    (c : Fin 6 → Real) : Real :=
  c 0 * Pt0 w p + c 1 * Pt00 w p + c 2 * Pt01 w p +
    c 3 * Pt10 w p + c 4 * Pt11 w p + c 5

def table : Fin 5 → Fin 6 → Real :=
  ![![1,1,0,-2,0,0], ![1,1,-2,-2,2,0], ![-2,1,2,2,0,4],
    ![-6,1,4,4,2,12], ![-6,1,4,0,0,24]]

def claim : Prop := ∀ (k : Fin 5) (N : Nat), 3 < N →
  ∀ (L : Type) [Fintype L] (w : L → Real)
    (p : L → Fin N → Fin 2 → Fin 3 → Real),
  (∀ l, 0 ≤ w l) → ∑ l, w l = 1 → (∀ l i x a, 0 ≤ p l i x a) →
  (∀ l i x, ∑ a, p l i x a = 1) → 0 ≤ bell w p (table k)

private noncomputable def ca (c : Fin 3 → Fin 3 → Nat) : Real := c 0 0+c 0 1+c 0 2
private noncomputable def cb (c : Fin 3 → Fin 3 → Nat) : Real := c 1 0+c 1 1+c 1 2
private noncomputable def cc (c : Fin 3 → Fin 3 → Nat) : Real := c 0 0+c 1 0+c 2 0
private noncomputable def cd (c : Fin 3 → Fin 3 → Nat) : Real := c 0 1+c 1 1+c 2 1
private noncomputable def cr (c : Fin 3 → Fin 3 → Nat) : Real := ca c+cb c
private noncomputable def cs (c : Fin 3 → Fin 3 → Nat) : Real := cc c+cd c
private noncomputable def ck (c : Fin 3 → Fin 3 → Nat) : Real := c 0 0+c 0 1+c 1 0+c 1 1

private noncomputable def countBell (c : Fin 3 → Fin 3 → Nat) (coef : Fin 6 → Real) : Real :=
  coef 0 * (cr c+cs c) + coef 1 * (ca c^2+cb c^2+cc c^2+cd c^2-(cr c+cs c)) +
  coef 2 * (ca c*cd c+cb c*cc c-c 0 1-c 1 0) +
  coef 3 * (ca c*cc c+cb c*cd c-c 0 0-c 1 1) +
  coef 4 * (ca c*cb c+cc c*cd c) + coef 5


private noncomputable def counts {N : Nat} (s : Fin N → Fin 2 → Fin 3) (a b : Fin 3) : Nat :=
  ∑ i, if s i 0=a ∧ s i 1=b then 1 else 0
private noncomputable def m1 {N : Nat} (s : Fin N → Fin 2 → Fin 3) (a : Fin 3) (x : Fin 2) : Real :=
  ∑ i, Pi.single (M := fun _ => Real) a 1 (s i x)
private noncomputable def m2 {N : Nat} (s : Fin N → Fin 2 → Fin 3) (a b : Fin 3) (x y : Fin 2) : Real :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, Pi.single (M := fun _ => Real) a 1 (s i x)*Pi.single (M := fun _ => Real) b 1 (s j y)

private theorem off_diagonal {N : Nat} (s : Fin N → Fin 2 → Fin 3) (a b : Fin 3) (x y : Fin 2) :
    m2 s a b x y = m1 s a x*m1 s b y-∑ i, Pi.single (M := fun _ => Real) a 1 (s i x)*Pi.single (M := fun _ => Real) b 1 (s i y) := by
  have h : m2 s a b x y+(∑ i, Pi.single (M := fun _ => Real) a 1 (s i x)*Pi.single (M := fun _ => Real) b 1 (s i y))=m1 s a x*m1 s b y := by
    unfold m2 m1
    rw [← Finset.sum_add_distrib,Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_erase_add _ _ (Finset.mem_univ i)
  linarith

private theorem diagonal_same {N : Nat} (s : Fin N → Fin 2 → Fin 3) (a : Fin 3) (x : Fin 2) :
    (∑ i, Pi.single (M := fun _ => Real) a 1 (s i x)*Pi.single (M := fun _ => Real) a 1 (s i x))=m1 s a x := by
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.single_apply, eq_comm]

private theorem diagonal_diff {N : Nat} (s : Fin N → Fin 2 → Fin 3)
    (a b : Fin 3) (hab : a ≠ b) (x : Fin 2) :
    (∑ i, Pi.single (M := fun _ => Real) a 1 (s i x) *
      Pi.single (M := fun _ => Real) b 1 (s i x)) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp only [Pi.single_apply]
  split_ifs <;> simp_all

private theorem diagonal_cross {N : Nat} (s : Fin N → Fin 2 → Fin 3) (a b : Fin 3) :
    (∑ i, Pi.single (M := fun _ => Real) a 1 (s i 0)*Pi.single (M := fun _ => Real) b 1 (s i 1))=(counts s a b:Real) := by
  unfold counts
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.single_apply]
  split_ifs <;> simp_all

private theorem marginal_row {N : Nat} (s : Fin N → Fin 2 → Fin 3) (a : Fin 3) :
    (counts s a 0:Real)+counts s a 1+counts s a 2=m1 s a 0 := by
  unfold counts m1
  push_cast
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  generalize h : s i 1=z
  fin_cases z <;> simp [Pi.single_apply, eq_comm]

private theorem marginal_col {N : Nat} (s : Fin N → Fin 2 → Fin 3) (a : Fin 3) :
    (counts s 0 a:Real)+counts s 1 a+counts s 2 a=m1 s a 1 := by
  unfold counts m1
  push_cast
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  generalize h : s i 0=z
  fin_cases z <;> simp [Pi.single_apply, eq_comm]

private noncomputable def detBell {N : Nat} (s : Fin N → Fin 2 → Fin 3) (c : Fin 6 → Real) : Real :=
  c 0*(m1 s 0 0+m1 s 0 1+m1 s 1 0+m1 s 1 1)+
  c 1*(m2 s 0 0 0 0+m2 s 0 0 1 1+m2 s 1 1 0 0+m2 s 1 1 1 1)+
  c 2*(m2 s 0 1 0 1+m2 s 1 0 0 1)+c 3*(m2 s 0 0 0 1+m2 s 1 1 0 1)+
  c 4*(m2 s 0 1 0 0+m2 s 0 1 1 1)+c 5

private theorem deterministic_count_formula {N : Nat} (s : Fin N → Fin 2 → Fin 3) (c : Fin 6 → Real) :
    detBell s c=countBell (counts s) c := by
  have ha : ca (counts s)=m1 s 0 0 := marginal_row s 0
  have hb : cb (counts s)=m1 s 1 0 := marginal_row s 1
  have hc : cc (counts s)=m1 s 0 1 := marginal_col s 0
  have hd : cd (counts s)=m1 s 1 1 := marginal_col s 1
  unfold detBell countBell cr cs
  simp only [off_diagonal,diagonal_same,diagonal_cross,
    diagonal_diff s 0 1 (by decide),ha,hb,hc,hd]
  ring


private theorem P1_average {N : Nat} {L : Type} [Fintype L] (w : L → Real)
    (p : L → Fin N → Fin 2 → Fin 3 → Real)
    (hn : ∀ l i x, ∑ a, p l i x a=1) (a : Fin 3) (x : Fin 2) :
    P1 w p a x = ∑ l, w l * ∑ s, windowLaw ((fun i => windowLaw (p l i))) s * m1 s a x := by
  unfold P1 m1
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (one_marginal (p l) (hn l) i x a).symm

private theorem P2_average {N : Nat} {L : Type} [Fintype L] (w : L → Real)
    (p : L → Fin N → Fin 2 → Fin 3 → Real)
    (hn : ∀ l i x, ∑ a, p l i x a=1) (a b : Fin 3) (x y : Fin 2) :
    P2 w p a b x y = ∑ l, w l * ∑ s, windowLaw ((fun i => windowLaw (p l i))) s * m2 s a b x y := by
  unfold P2 m2
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact (two_marginal (p l) (hn l) i j (Finset.ne_of_mem_erase hj).symm x y a b).symm

set_option maxHeartbeats 2000000 in
-- Distributing the nested finite averages requires additional elaboration work.
private theorem bell_average {N : Nat} {L : Type} [Fintype L] (w : L → Real)
    (p : L → Fin N → Fin 2 → Fin 3 → Real) (c : Fin 6 → Real)
    (hw : ∑ l, w l=1) (hn : ∀ l i x, ∑ a, p l i x a=1) :
    bell w p c = ∑ l, w l * ∑ s, windowLaw ((fun i => windowLaw (p l i))) s * detBell s c := by
  have hq (l : L) : ∑ s, windowLaw ((fun i => windowLaw (p l i))) s=1 :=
    windowLaw_sum_eq_one ((fun i => windowLaw (p l i))) (q_normalized (p l) (hn l))
  have hconst : (∑ l, w l * ∑ s, windowLaw ((fun i => windowLaw (p l i))) s * c 5)=c 5 := by
    simp_rw [← Finset.sum_mul,hq,one_mul]
    rw [← Finset.sum_mul,hw,one_mul]
  unfold bell Pt0 Pt00 Pt01 Pt10 Pt11
  simp_rw [P1_average w p hn,P2_average w p hn]
  conv_lhs => rw [← hconst]
  unfold detBell
  simp only [mul_add,add_mul,Finset.sum_add_distrib,Finset.mul_sum,
    mul_assoc,mul_left_comm,mul_comm,add_assoc]

private noncomputable def G (k u v : Nat) : Real :=
  6*((k:Real)-1)*((k:Real)-2) + ((u:Real)+(v:Real))^2 +
    (6*(k:Real)-7)*((u:Real)+(v:Real)) + 2*(u:Real)*(v:Real)

private theorem adjacent_nonneg (n m : Nat) :
    0 ≤ ((n:Real)-(m:Real))*((n:Real)-((m:Real)+1)) := by
  rcases le_or_gt n m with h | h
  · have h' : (n:Real) ≤ (m:Real) := by exact_mod_cast h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have h' : (m:Real)+1 ≤ (n:Real) := by exact_mod_cast h
    exact mul_nonneg (by linarith) (by linarith)

private theorem G_nonneg (k u v : Nat) : 0 ≤ G k u v := by
  have hu : (0:Real) ≤ u := Nat.cast_nonneg u
  have hv : (0:Real) ≤ v := Nat.cast_nonneg v
  have huv := mul_nonneg hu hv
  rcases k with _ | k
  · have hw := adjacent_nonneg (u+v) 3
    push_cast at hw
    unfold G
    norm_num
    nlinarith
  · rcases k with _ | k
    · have hw := adjacent_nonneg (u+v) 0
      push_cast at hw
      unfold G
      norm_num
      nlinarith
    · have hk : (2:Real) ≤ (k+1+1:Nat) := by exact_mod_cast (show 2 ≤ k+1+1 by omega)
      have h1 := mul_nonneg (show (0:Real) ≤ (k+1+1:Nat)-1 by linarith)
        (show (0:Real) ≤ (k+1+1:Nat)-2 by linarith)
      have h2 := mul_nonneg (show (0:Real) ≤ 6*(k+1+1:Nat)-7 by linarith)
        (show (0:Real) ≤ (u:Real)+v by positivity)
      unfold G
      nlinarith [sq_nonneg ((u:Real)+(v:Real))]

private theorem row1_certificate (c : Fin 3 → Fin 3 → Nat) :
    countBell c (table 0) = (ca c-cc c)^2+(cb c-cd c)^2+2*(c 0 0+c 1 1) := by
  simp [countBell,table,cr,cs]
  ring
private theorem row2_certificate (c : Fin 3 → Fin 3 → Nat) :
    countBell c (table 1) = (cr c-cs c)^2+2*ck c := by
  simp [countBell,table,cr,cs,ck]
  ring
private theorem row3_certificate (c : Fin 3 → Fin 3 → Nat) :
    2*countBell c (table 2) =
    (ca c-cb c)^2+(cc c-cd c)^2+(cr c-2)^2+(cs c-2)^2+
    4*(cr c-2)*(cs c-2)+2*(cr c-2)+6*(cs c-2)+4*(cr c-ck c) := by
  simp [countBell,table,cr,cs,ck]
  ring
private theorem row4_certificate (c : Fin 3 → Fin 3 → Nat) :
    countBell c (table 3) = G (c 0 0+c 0 1+c 1 0+c 1 1)
      (c 0 2+c 1 2) (c 2 0+c 2 1) := by
  simp [countBell,table,cr,cs,ca,cb,cc,cd,G]
  ring
private theorem row5_certificate (c : Fin 3 → Fin 3 → Nat) :
    countBell c (table 4) = G (c 0 1) (c 0 0+c 0 2) (c 1 1+c 2 1) +
      G (c 1 0) (c 1 1+c 1 2) (c 0 0+c 2 0) := by
  simp [countBell,table,cr,cs,ca,cb,cc,cd,G]
  ring


private noncomputable def row3poly (a b c d k : Nat) : Real :=
  (a:Real)^2+(b:Real)^2+(c:Real)^2+(d:Real)^2-
  3*((a:Real)+b+c+d)+2*((a:Real)+b)*((c:Real)+d)-2*(k:Real)+4

private theorem row3_small (a b c d k : Nat) (hk : k ≤ a+b) (hr : a+b ≤ 1) :
    0 ≤ row3poly a b c d k := by
  have hk' : (k:Real) ≤ (a:Real)+b := by exact_mod_cast hk
  have hqa := adjacent_nonneg a 0
  have hqb := adjacent_nonneg b 0
  have hqc := adjacent_nonneg c 0
  have hqd := adjacent_nonneg d 0
  have hc3 := adjacent_nonneg c 1
  have hd3 := adjacent_nonneg d 1
  norm_num at hqa hqb hqc hqd hc3 hd3
  have hab : a+b=0 ∨ a+b=1 := by omega
  rcases hab with h | h
  · have ha : a=0 := by omega
    have hb : b=0 := by omega
    have hz : k=0 := by omega
    simp only [row3poly,ha,hb,hz,Nat.cast_zero,zero_pow (by decide : 2≠0)]
    nlinarith
  · have h' : (a:Real)+b=1 := by exact_mod_cast h
    unfold row3poly
    nlinarith

private theorem row3poly_nonneg (a b c d k : Nat) (hkr : k ≤ a+b) (hks : k ≤ c+d) :
    0 ≤ row3poly a b c d k := by
  by_cases hr : a+b ≤ 1
  · exact row3_small a b c d k hkr hr
  by_cases hs : c+d ≤ 1
  · have h := row3_small c d a b k hks hs
    unfold row3poly at h ⊢
    nlinarith
  have hr' : (2:Real) ≤ (a:Real)+b := by exact_mod_cast (show 2 ≤ a+b by omega)
  have hs' : (2:Real) ≤ (c:Real)+d := by exact_mod_cast (show 2 ≤ c+d by omega)
  have hk' : (k:Real) ≤ (a:Real)+b := by exact_mod_cast hkr
  have hm := mul_nonneg (show (0:Real) ≤ (a:Real)+b-2 by linarith)
    (show (0:Real) ≤ (c:Real)+d-2 by linarith)
  have hid : 2*row3poly a b c d k =
      ((a:Real)-b)^2+((c:Real)-d)^2+((a:Real)+b-2)^2+((c:Real)+d-2)^2+
      4*((a:Real)+b-2)*((c:Real)+d-2)+2*((a:Real)+b-2)+
      6*((c:Real)+d-2)+4*((a:Real)+b-k) := by unfold row3poly; ring
  nlinarith [sq_nonneg ((a:Real)-b),sq_nonneg ((c:Real)-d),
    sq_nonneg ((a:Real)+b-2),sq_nonneg ((c:Real)+d-2)]

private theorem countBell_nonneg (c : Fin 3 → Fin 3 → Nat) (k : Fin 5) :
    0 ≤ countBell c (table k) := by
  fin_cases k
  · change 0 ≤ countBell c (table 0)
    rw [row1_certificate]
    positivity
  · change 0 ≤ countBell c (table 1)
    rw [row2_certificate]
    unfold ck
    positivity
  · change 0 ≤ countBell c (table 2)
    have h := row3poly_nonneg (c 0 0+c 0 1+c 0 2) (c 1 0+c 1 1+c 1 2)
      (c 0 0+c 1 0+c 2 0) (c 0 1+c 1 1+c 2 1)
      (c 0 0+c 0 1+c 1 0+c 1 1) (by omega) (by omega)
    have hid : countBell c (table 2) =
      row3poly (c 0 0+c 0 1+c 0 2) (c 1 0+c 1 1+c 1 2)
      (c 0 0+c 1 0+c 2 0) (c 0 1+c 1 1+c 2 1)
      (c 0 0+c 0 1+c 1 0+c 1 1) := by
        apply mul_left_cancel₀ (by norm_num : (2:Real)≠0)
        rw [row3_certificate]
        simp [row3poly,cr,cs,ca,cb,cc,cd,ck]
        ring
    rw [hid]
    exact h
  · change 0 ≤ countBell c (table 3)
    rw [row4_certificate]
    exact G_nonneg _ _ _
  · change 0 ≤ countBell c (table 4)
    rw [row5_certificate]
    exact add_nonneg (G_nonneg _ _ _) (G_nonneg _ _ _)

private theorem deterministic_bell {N : Nat} (s : Fin N → Fin 2 → Fin 3) (c : Fin 6 → Real) :
    bell (fun _ : Unit => 1) (fun _ i x a => Pi.single (M := fun _ => Real) a 1 (s i x)) c=detBell s c := by
  simp [bell,Pt0,Pt00,Pt01,Pt10,Pt11,P1,P2,detBell,m1,m2]


private theorem deterministic_validity {N : Nat} (s : Fin N → Fin 2 → Fin 3) (k : Fin 5) :
    0 ≤ bell (fun _ : Unit => 1) (fun _ i x a => Pi.single (M := fun _ => Real) a 1 (s i x)) (table k) := by
  rw [deterministic_bell,deterministic_count_formula]
  exact countBell_nonneg (counts s) k

private theorem model_nonneg {N : Nat} {L : Type} [Fintype L]
    (w : L → Real) (p : L → Fin N → Fin 2 → Fin 3 → Real) (k : Fin 5)
    (hw0 : ∀ l, 0 ≤ w l) (hw : ∑ l, w l=1)
    (hp0 : ∀ l i x a, 0 ≤ p l i x a) (hp : ∀ l i x, ∑ a, p l i x a=1) :
    0 ≤ bell w p (table k) := by
  rw [bell_average w p (table k) hw hp]
  apply Finset.sum_nonneg
  intro l _
  apply mul_nonneg (hw0 l)
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg
  · unfold windowLaw
    apply Finset.prod_nonneg
    intro i _
    simpa only [windowLaw, Fin.prod_univ_two] using
      mul_nonneg (hp0 l i 0 (s i 0)) (hp0 l i 1 (s i 1))
  · rw [← deterministic_bell]
    exact deterministic_validity s k

theorem result : claim := by
  intro k N _ L _ w p hw0 hw hp0 hp
  exact model_nonneg w p k hw0 hw hp0 hp

end D5.S3.Quantum.Entanglement.ThreeOutcomePermutationallyInvariantBell
