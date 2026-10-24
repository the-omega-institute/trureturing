/- GID: D5/S3/Arith/MiskaUlasSigmaThreeBound
   generality: I
   mirror-B: D5/B/S3/Arith/MiskaUlasSigmaThreeBound
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/MiskaUlasSigmaThreeBound.claim; result=D5/S3/Arith/MiskaUlasSigmaThreeBound.result; claim=D5/S3/Arith/MiskaUlasSigmaThreeBound.claim
   digest: A positive integer family refutes the degree-six symmetric-product bound. -/

/-
result: proof_shape: bind-only; escape_witness: none;
admission_basis: open-problem-resolution (#19678; Refuted).
Direct frozen dependencies: D5/S3/Combinatorics/Graph/MultipartiteCHS/Extremal (D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal.esymm_cons).
The newly public `D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal.esymm_cons` theorem has an unfinished escape audit under https://github.com/the-omega-institute/trureturing/issues/20171.
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
The elementary symmetric expression in claim is written out as in #19678;
proofs use MvPolynomial.aeval_esymm_eq_multiset_esymm without a new sigma alias.
All private proof helpers have proof_shape: bind-only and escape_witness: none.
Definition rows (proof_shape: bind-only; Direct frozen dependencies: none):
claim → result; cval → defect_one, cval_cast, xvals_domain, xvals;
yvals → defect_one, dval_expand, appended_solution, xvals;
pval → defect_one, dval_expand, appended_solution, xvals_solution, product_gap;
xvals → xvals_multiset, xvals_domain, xvals_solution; qbound → product_gap, result.
For every row, escape_witness: none; the module basis is the settling result.
Consumers: sigma_multiset → xvals_solution; D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal.esymm_cons → defect_one, dval_expand,
appended_solution; esymm_replicate → defect_one, dval_expand, cval_cast, dval_cast;
defect_one → appended_solution; dval_expand → dval_ge, dval_cast;
dval_ge → xvals_domain; cval_cast → dval_cast, product_gap; dval_cast → product_gap;
appended_solution → xvals_solution; xvals_multiset → xvals_solution;
xvals_domain → family; xvals_solution → family; product_gap → product_exceeds;
product_exceeds → family; family → result.
The utility record names the certified instance at n = 11 used to refute claim.
-/
import D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith

namespace D5.S3.Arith.MiskaUlasSigmaThreeBound

/-- Conjecture 4.8. A solution is a nondecreasing tuple `Xₙ = (x₁, …, xₙ)` of positive integers; `xₙ` is its last
entry `X ⟨n - 1, _⟩`. -/
def claim : Prop :=
  ∀ n : ℕ, ∀ hn : 4 ≤ n, ∀ X : Fin n → ℕ, (∀ i, 0 < X i) → Monotone X →
    ∀ m : ℕ, m = MvPolynomial.eval X (MvPolynomial.esymm (Fin n) ℕ 3) → m = MvPolynomial.eval X (MvPolynomial.esymm (Fin n) ℕ n) →
      (m : ℚ) ≤ 1 / 12 * (3021 * (n : ℚ) ^ 6 - 77575 * (n : ℚ) ^ 5 + 920361 * (n : ℚ) ^ 4 - 6235705 * (n : ℚ) ^ 3
          + 24764202 * (n : ℚ) ^ 2 - 53664304 * (n : ℚ) + 48986640) ∧
        (X ⟨n - 1, by omega⟩ : ℚ) ≤ 1 / 12 * (27 * (n : ℚ) ^ 4 - 190 * (n : ℚ) ^ 3 + 471 * (n : ℚ) ^ 2
          - 500 * (n : ℚ) + 216)


private theorem sigma_multiset {n : ℕ} (X : Fin n → ℕ) (j : ℕ) :
    MvPolynomial.eval X (MvPolynomial.esymm (Fin n) ℕ j) = (Finset.univ.val.map X).esymm j := by
  simpa [MvPolynomial.aeval_def] using
    (MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℕ j X)

private theorem esymm_replicate (k : ℕ) :
    (Multiset.replicate k (1 : ℕ)).esymm 1 = k ∧
    2 * (Multiset.replicate k (1 : ℕ)).esymm 2 + k = k^2 ∧
    6 * (Multiset.replicate k (1 : ℕ)).esymm 3 + 3*k^2 = k^3+2*k := by
  have he (j : ℕ) : (Multiset.replicate k (1 : ℕ)).esymm j = k.choose j := by
    simpa [List.ofFn_const] using Finset.esymm_map_val (fun _ : Fin k => (1 : ℕ)) Finset.univ j
  rw [he 1,he 2,he 3]
  constructor
  · simp
  have h2 := Nat.add_one_mul_choose_eq k 1
  have h3 := Nat.add_one_mul_choose_eq k 2
  norm_num [Nat.choose_succ_succ] at h2 h3
  constructor
  · nlinarith
  · nlinarith [congrArg (fun v : ℕ => k*v) h2]



private noncomputable def cval (k : ℕ) : ℕ := 3 * (Multiset.replicate k (1 : ℕ)).esymm 2 + 8*k + 7
private noncomputable def yvals (k : ℕ) : Multiset ℕ := 2 ::ₘ (k+3) ::ₘ cval k ::ₘ Multiset.replicate k (1 : ℕ)
private noncomputable def pval (k : ℕ) : ℕ := 2*(k+3)*cval k

private theorem defect_one (k : ℕ) : (yvals k).esymm 2 + 1 = pval k := by
  have h1 := (esymm_replicate k).1
  have h2 := (esymm_replicate k).2.1
  change (Multiset.replicate k (1 : ℕ)).esymm 1 = k at h1
  change 2*(Multiset.replicate k (1 : ℕ)).esymm 2+k=k^2 at h2
  simp only [yvals, D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal.esymm_cons, Multiset.esymm_zero]
  rw [h1]
  dsimp [pval, cval]
  nlinarith

private theorem dval_expand (k : ℕ) : (yvals k).esymm 3 =
    (Multiset.replicate k (1 : ℕ)).esymm 3 + (2+(k+3)+cval k)*(Multiset.replicate k (1 : ℕ)).esymm 2 +
    (2*(k+3)+2*cval k+(k+3)*cval k)*k + pval k := by
  have h1 := (esymm_replicate k).1
  change (Multiset.replicate k (1 : ℕ)).esymm 1 = k at h1
  simp only [yvals, D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal.esymm_cons, Multiset.esymm_zero]
  rw [h1]
  dsimp [pval]
  ring

private theorem dval_ge (k : ℕ) : pval k ≤ (yvals k).esymm 3 := by
  rw [dval_expand]
  omega

private theorem cval_cast (k : ℕ) : (cval k : ℚ) = ((k:ℚ)+2)*(3*k+7)/2 := by
  have h := congrArg (fun v : ℕ => (v : ℚ)) (esymm_replicate k).2.1
  push_cast at h
  dsimp [cval]
  push_cast
  nlinarith

private theorem dval_cast (k : ℕ) : ((yvals k).esymm 3 : ℚ) =
    (27*((k:ℚ)+4)^4-190*((k:ℚ)+4)^3+471*((k:ℚ)+4)^2-500*((k:ℚ)+4)+216)/12 := by
  have h2 := congrArg (fun v : ℕ => (v : ℚ)) (esymm_replicate k).2.1
  have h3 := congrArg (fun v : ℕ => (v : ℚ)) (esymm_replicate k).2.2
  push_cast at h2 h3
  have h2' : ((Multiset.replicate k (1 : ℕ)).esymm 2 : ℚ) = ((k:ℚ)^2-k)/2 := by
    linarith
  have h3' : ((Multiset.replicate k (1 : ℕ)).esymm 3 : ℚ) = ((k:ℚ)^3-3*(k:ℚ)^2+2*k)/6 := by
    linarith
  rw [dval_expand]
  push_cast
  rw [h2',h3',cval_cast]
  dsimp [pval]
  push_cast
  rw [cval_cast]
  ring

private theorem appended_solution (k : ℕ) :
    ((yvals k).esymm 3 ::ₘ yvals k).esymm 3 = ((yvals k).esymm 3 ::ₘ yvals k).prod := by
  have hd := defect_one k
  rw [show 3=2+1 from rfl, D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal.esymm_cons, Multiset.prod_cons]
  change (yvals k).esymm 3 + (yvals k).esymm 3 * (yvals k).esymm 2 = _
  have hp : (yvals k).prod = pval k := by simp [yvals, pval, mul_assoc]
  rw [hp]
  nlinarith


private noncomputable def xvals (k : ℕ) : Fin (k+4) → ℕ :=
  Fin.append (fun _ : Fin k => 1) ![2,k+3,cval k,(yvals k).esymm 3]

private theorem xvals_multiset (k : ℕ) :
    Finset.univ.val.map (xvals k) = (yvals k).esymm 3 ::ₘ yvals k := by
  rw [Fin.univ_val_map]
  unfold xvals
  rw [List.ofFn_fin_append,List.ofFn_const]
  simp only [List.ofFn_succ,
    List.ofFn_zero,
    ← Multiset.coe_add, ← Multiset.cons_coe, Multiset.coe_nil,
    Multiset.coe_replicate, yvals]
  simp only [Multiset.add_cons, Multiset.add_zero]
  simp [Multiset.cons_swap]

private theorem xvals_domain (k : ℕ) : (∀ i, 0 < xvals k i) ∧ Monotone (xvals k) := by
  have hc : k+3 ≤ cval k := by dsimp [cval]; omega
  have hp : cval k ≤ pval k := by
    exact Nat.le_mul_of_pos_left (cval k) (by omega)
  have hd : cval k ≤ (yvals k).esymm 3 := hp.trans (dval_ge k)
  constructor
  · intro i
    induction i using Fin.addCases
    · simp [xvals]
    · rename_i i
      fin_cases i <;> simp [xvals] <;> omega
  · have hs : (List.ofFn (xvals k)).Pairwise (· ≤ ·) := by
      unfold xvals
      rw [List.ofFn_fin_append,List.ofFn_const]
      simp [List.ofFn_succ,List.pairwise_append,List.pairwise_cons,List.pairwise_replicate] ; omega
    intro i j hij
    rcases lt_or_eq_of_le hij with h|rfl
    · exact List.pairwise_ofFn.mp hs h
    · rfl

private theorem xvals_solution (k : ℕ) : MvPolynomial.eval (xvals k) (MvPolynomial.esymm (Fin (k+4)) ℕ 3) = MvPolynomial.eval (xvals k) (MvPolynomial.esymm (Fin (k+4)) ℕ (k+4)) ∧
    MvPolynomial.eval (xvals k) (MvPolynomial.esymm (Fin (k+4)) ℕ (k+4)) = pval k*(yvals k).esymm 3 := by
  have hm := xvals_multiset k
  have hcard : ((yvals k).esymm 3 ::ₘ yvals k).card = k+4 := by simp [yvals]
  have htop : MvPolynomial.eval (xvals k) (MvPolynomial.esymm (Fin (k+4)) ℕ (k+4)) = pval k*(yvals k).esymm 3 := by
    rw [sigma_multiset,hm,← hcard]
    rw [Multiset.esymm,Multiset.powersetCard_self]
    simp [yvals,pval,mul_assoc,mul_comm]
  constructor
  · rw [htop,sigma_multiset,hm,appended_solution]
    simp [yvals,pval,mul_assoc,mul_comm]
  · exact htop


private def qbound (n : ℕ) : ℚ := 1 / 12 *
    (3021*(n:ℚ)^6-77575*(n:ℚ)^5+920361*(n:ℚ)^4-6235705*(n:ℚ)^3+
      24764202*(n:ℚ)^2-53664304*(n:ℚ)+48986640)

private theorem product_gap (k : ℕ) :
    ((pval k*(yvals k).esymm 3 : ℕ) : ℚ)-qbound (k+4) =
    27/4*(k:ℚ)*((k:ℚ)-1)*((k:ℚ)-2)*((k:ℚ)-3)*((k:ℚ)-4)*((k:ℚ)-5)*((k:ℚ)-6) := by
  dsimp [pval,qbound]
  push_cast
  rw [cval_cast,dval_cast]
  ring

private theorem product_exceeds (k : ℕ) (hk : 7 ≤ k) :
    qbound (k+4) < ((pval k*(yvals k).esymm 3 : ℕ) : ℚ) := by
  have hk' : (7 : ℚ) ≤ k := by exact_mod_cast hk
  have h0 : (0 : ℚ) < k := lt_of_le_of_lt' hk' rfl
  have h1 : (0 : ℚ) < (k:ℚ)-1 := by linarith
  have h2 : (0 : ℚ) < (k:ℚ)-2 := by linarith
  have h3 : (0 : ℚ) < (k:ℚ)-3 := by linarith
  have h4 : (0 : ℚ) < (k:ℚ)-4 := by linarith
  have h5 : (0 : ℚ) < (k:ℚ)-5 := by linarith
  have h6 : (0 : ℚ) < (k:ℚ)-6 := by linarith
  have he : (0:ℚ) < ((pval k*(yvals k).esymm 3 : ℕ) : ℚ)-qbound (k+4) := by
    rw [product_gap]
    positivity
  linarith

private theorem family (k : ℕ) (hk : 7 ≤ k) :
    (∀ i, 0 < xvals k i) ∧ Monotone (xvals k) ∧
    MvPolynomial.eval (xvals k) (MvPolynomial.esymm (Fin (k+4)) ℕ 3) =
      MvPolynomial.eval (xvals k) (MvPolynomial.esymm (Fin (k+4)) ℕ (k+4)) ∧
    qbound (k+4) <
      (MvPolynomial.eval (xvals k) (MvPolynomial.esymm (Fin (k+4)) ℕ (k+4)) : ℚ) := by
  exact ⟨(xvals_domain k).1, (xvals_domain k).2, (xvals_solution k).1,
    by rw [(xvals_solution k).2]; exact product_exceeds k hk⟩

theorem result : ¬ claim := by
  intro h
  have hf := family 7 (by omega)
  have hc := h 11 (by omega) (xvals 7) hf.1 hf.2.1
    (MvPolynomial.eval (xvals 7) (MvPolynomial.esymm (Fin 11) ℕ 11)) hf.2.2.1.symm rfl
  exact (not_le_of_gt hf.2.2.2) hc.1

end D5.S3.Arith.MiskaUlasSigmaThreeBound
