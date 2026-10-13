/- GID: D5/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone
   generality: G
   mirror-B: D5/B/S3/Geometry/AlphaGeometry/LogScalarCurvatureMonotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict Schur increase of logarithmic simplex scalar curvature. -/

/-

admission_basis: open-problem-resolution (#15145; Proved)
escape_witness: none (settling result uses open-problem-resolution)
Direct frozen dependencies: none; all prerequisites are pinned Mathlib or this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15483
Published owner escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15716
Published owner DTR reading: DTR-Unregistered; the typed family bridge, law-violating variation, slot sensitivity and observational-dependence evidence remain missing.
Per-declaration judgement form (definitions carry no new-content claim):
proof_shape: antitoneSortPerm: bind-only; consumer=LogScalarCurvatureMonotone.sorted; witness=none
proof_shape: antitone_comp_antitoneSortPerm: bind-only; consumer=LogScalarCurvatureMonotone.sorted_antitone; witness=none
proof_shape: sorted: bind-only; consumer=LogScalarCurvatureMonotone.sorted_list_eq_desc; witness=none
proof_shape: sorted_antitone: bind-only; consumer=LogScalarCurvatureMonotone.sorted_list_eq_desc; witness=none
proof_shape: sorted_list_eq_desc: bind-only; consumer=LogScalarCurvatureMonotone.moreMixed_sorted_prefix; witness=none
proof_shape: vector_prefix_eq_list: bind-only; consumer=LogScalarCurvatureMonotone.moreMixed_sorted_prefix; witness=none
proof_shape: moreMixed_sorted_prefix: bind-only; consumer=LogScalarCurvatureMonotone.moreMixed_positive_chain; witness=none
proof_shape: permutation_positive_chain: bind-only; consumer=LogScalarCurvatureMonotone.moreMixed_positive_chain; witness=none
proof_shape: moreMixed_positive_chain: content; consumer=LogScalarCurvatureMonotone.formula_result; witness=none
proof_shape: formula: bind-only; consumer=LogScalarCurvatureMonotone.formula_perm; witness=none
proof_shape: powerSum_perm: bind-only; consumer=LogScalarCurvatureMonotone.formula_perm; witness=none
proof_shape: formula_perm: bind-only; consumer=LogScalarCurvatureMonotone.formula_oneT; witness=none
proof_shape: pairVector: bind-only; consumer=LogScalarCurvatureMonotone.powerSum_pair; witness=none
proof_shape: powerSum_pair: bind-only; consumer=LogScalarCurvatureMonotone.formula_pair; witness=none
proof_shape: formula_pair: bind-only; consumer=LogScalarCurvatureMonotone.formula_rest; witness=none
proof_shape: chart_power_product: bind-only; consumer=LogScalarCurvatureMonotone.scalarCurvature_eq_chart_formula; witness=none
proof_shape: scalar_formula_algebra: bind-only; consumer=LogScalarCurvatureMonotone.scalarCurvature_eq_chart_formula; witness=none
proof_shape: scalarCurvature_eq_chart_formula: bind-only; consumer=LogScalarCurvatureMonotone.scalInfty_eq_formula; witness=none
proof_shape: chart_eq_simplex: bind-only; consumer=LogScalarCurvatureMonotone.scalInfty_eq_formula; witness=none
proof_shape: simplex_chart_domain: bind-only; consumer=LogScalarCurvatureMonotone.scalInfty_eq_formula; witness=none
proof_shape: scalInfty_eq_formula: bind-only; consumer=LogScalarCurvatureMonotone.result; witness=none
proof_shape: pairRest: bind-only; consumer=LogScalarCurvatureMonotone.powerSum_rest; witness=none
proof_shape: powerSum_rest: bind-only; consumer=LogScalarCurvatureMonotone.pairRest_sum; witness=none
proof_shape: pairRest_nonneg: bind-only; consumer=LogScalarCurvatureMonotone.formula_oneT; witness=none
proof_shape: pairRest_pos_exists: bind-only; consumer=LogScalarCurvatureMonotone.formula_oneT; witness=none
proof_shape: pairRest_sum: bind-only; consumer=LogScalarCurvatureMonotone.formula_rest; witness=none
proof_shape: formula_rest: bind-only; consumer=LogScalarCurvatureMonotone.formula_oneT; witness=none
proof_shape: nonnegative_pair_invariants: bind-only; consumer=LogScalarCurvatureMonotone.nonnegative_pair_K; witness=none
proof_shape: nonnegative_pair_K: content; consumer=LogScalarCurvatureMonotone.strict_mix_formula_nonnegative_rest; witness=none
proof_shape: strict_mix_formula_nonnegative_rest: content; consumer=LogScalarCurvatureMonotone.formula_oneT; witness=none
proof_shape: formula_oneT: content; consumer=LogScalarCurvatureMonotone.formula_chain; witness=none
proof_shape: formula_chain: content; consumer=LogScalarCurvatureMonotone.formula_result; witness=none
proof_shape: formula_result: content; consumer=LogScalarCurvatureMonotone.result; witness=none
proof_shape: claim: bind-only; consumer=result statement; witness=none
proof_shape: result: content; consumer=external named settlement; witness=none
-/

import D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
import D5.S3.Geometry.AlphaGeometry.PairCurvatureInequality
import Mathlib.Data.Fin.Tuple.Sort

noncomputable section
namespace D5.S3.Geometry.AlphaGeometry.LogScalarCurvatureMonotone
open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
open D5.S3.Geometry.AlphaGeometry.PairCurvatureInequality
open D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector

private noncomputable def antitoneSortPerm {n : ℕ} (f : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  (Fin.revPerm).trans (Tuple.sort f)
private lemma antitone_comp_antitoneSortPerm {n : ℕ} (f : Fin n → ℝ) :
    Antitone (f ∘ antitoneSortPerm f) := by
  intro i j hij
  have hrev : (j : Fin n).rev ≤ (i : Fin n).rev := Fin.rev_le_rev.mpr hij
  exact Tuple.monotone_sort f hrev
private abbrev sorted {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := x ∘ antitoneSortPerm x
private lemma sorted_antitone {n : ℕ} (x : Fin n → ℝ) : Antitone (sorted x) :=
  antitone_comp_antitoneSortPerm x
private lemma sorted_list_eq_desc {n : ℕ} (x : Fin n → ℝ) : List.ofFn (sorted x) = desc x := by
  apply List.Perm.eq_of_pairwise' (r := fun a b : ℝ => b ≤ a)
  · exact (sorted_antitone x).sortedGE_ofFn.pairwise
  · exact List.pairwise_mergeSort' (fun a b : ℝ => b ≤ a) (List.ofFn x)
  · exact ((antitoneSortPerm x).ofFn_comp_perm x).trans (List.mergeSort_perm _ _).symm
private lemma vector_prefix_eq_list {n : ℕ} (x : Fin n → ℝ) (k : ℕ) :
    D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector.prefixSum k x = D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.prefixSum (List.ofFn x) k := by
  simpa [D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector.prefixSum,
    D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.prefixSum]
    using (List.sum_take_ofFn x k).symm
private lemma moreMixed_sorted_prefix {n : ℕ} {x y : Fin n → ℝ} (h : moreMixed x y) :
    ∀ k, D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector.prefixSum k (sorted x) ≤
      D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector.prefixSum k (sorted y) := by
  intro k
  by_cases hk : k < n
  · rw [vector_prefix_eq_list, vector_prefix_eq_list, sorted_list_eq_desc, sorted_list_eq_desc]
    exact h.1 k hk
  · have hnk : n ≤ k := Nat.le_of_not_gt hk
    rw [D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector.prefixSum_eq_full_sum_of_le _ hnk,
      D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector.prefixSum_eq_full_sum_of_le _ hnk]
    have hs := h.2
    rw [← sorted_list_eq_desc, ← sorted_list_eq_desc, ← vector_prefix_eq_list,
      ← vector_prefix_eq_list, D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector.prefixSum_eq_full_sum_of_le _ le_rfl,
      D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector.prefixSum_eq_full_sum_of_le _ le_rfl] at hs
    exact hs.le
private lemma permutation_positive_chain {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (σ : Equiv.Perm (Fin n)) : Relation.ReflTransGen PositiveT x (x ∘ σ) := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simpa using (Relation.ReflTransGen.refl : Relation.ReflTransGen PositiveT x x)
  | mul_swap σ i j hij ih =>
    have htr : IsTTransform (x ∘ σ) ((x ∘ σ) ∘ Equiv.swap i j) := ⟨i,j,1,by norm_num,le_rfl,by simp⟩
    have hp : ∀ i, 0 < (x ∘ σ) i := fun i => hx _
    have hc := Relation.ReflTransGen.single (r := PositiveT) ⟨htr,hp,ttransform_positive htr hp,ttransform_sum htr⟩
    simpa only [Function.comp_assoc, Equiv.Perm.coe_mul] using ih.trans hc
lemma moreMixed_positive_chain {n : ℕ} (x y : Fin n → ℝ)
    (hx : x ∈ simplex n) (hy : y ∈ simplex n) (hxy : moreMixed x y) :
    Relation.ReflTransGen PositiveT y x := by
  have hxsorted : ∀ i, 0 < sorted x i := fun i => hx.1 _
  have hysorted : ∀ i, 0 < sorted y i := fun i => hy.1 _
  have hsum : (∑ i, sorted x i) = ∑ i, sorted y i := by
    simp only [sorted, Function.comp_apply]
    rw [Equiv.sum_comp (antitoneSortPerm x) x, Equiv.sum_comp (antitoneSortPerm y) y, hx.2, hy.2]
  have hc := positive_sorted_chain (sorted_antitone x) hxsorted hysorted (moreMixed_sorted_prefix hxy) hsum
  have hfirst := permutation_positive_chain y hy.1 (antitoneSortPerm y)
  have hlast := permutation_positive_chain (sorted x) hxsorted (antitoneSortPerm x).symm
  have hlast' : Relation.ReflTransGen PositiveT (sorted x) x := by
    simpa [sorted, Function.comp_def] using hlast
  exact hfirst.trans (hc.trans hlast')

private def formula {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (P _ x 2 - P _ x 2 ^ 2 - 2 * P _ x 3 + 2 * P _ x 4) /
    P _ x 2 ^ 2
private lemma powerSum_perm {n : ℕ} (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    P _ (x ∘ σ) k = P _ x k := by
  simpa only [P_evalSum, Function.comp_apply] using Equiv.sum_comp σ (fun i => x i ^ k)
private lemma formula_perm {n : ℕ} (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    formula (x ∘ σ) = formula x := by
  simp [formula,powerSum_perm]
private def pairVector {r : ℕ} (a b : ℝ) (z : Fin r → ℝ) : Fin (r+2) → ℝ :=
  Fin.cons a (Fin.cons b z)
private lemma powerSum_pair {r : ℕ} (a b : ℝ) (z : Fin r → ℝ) (k : ℕ) :
    P _ (pairVector a b z) k = a ^ k + b ^ k + P r z k := by
  simp [P_evalSum,pairVector,Fin.sum_univ_succ,P_evalSum]
  ring
private lemma formula_pair {r : ℕ} (a b : ℝ) (z : Fin r → ℝ)
    (hs : a + b + (∑ i, z i) = 1) :
    formula (pairVector a b z) = pairR (a+b) (∑ i, z i) (P _ z 2)
      (E r z 2) (E r z 3) (E r z 4) (a*b) := by
  have h₂ := newton2 r z
  have h₃ := newton3 r z
  have h₄ := newton4 r z
  rw [E_one_eq_sum] at h₂
  have hsum : (∑ i, z i) = 1 - (a+b) := by linarith
  rw [hsum] at h₂ h₃ h₄
  have hT : a^2+b^2+P r z 2 = pairT (a+b) (a*b) (P _ z 2) := by
    dsimp [pairT]
    ring
  unfold formula
  simp_rw [powerSum_pair]
  rw [hT]
  unfold pairR
  congr 1
  rw [h₃,h₄]
  dsimp [pairN,pairT]
  change _ = 2 * (a*b*(∑ i, z i)+(a+b)*E r z 2+E r z 3-
    4*(a*b*E r z 2+(a+b)*E r z 3+E r z 4))
  rw [hsum]
  have hB : P _ z 2 = (1-(a+b))^2-2*E r z 2 := h₂
  rw [hB]
  ring


private lemma chart_power_product {m : ℕ} (t : Fin m → ℝ) (b : ℝ) (r : ℕ) :
    (∑ i, t i ^ r * (t i - b)) = (∑ i, t i ^ (r+1)) - b * (∑ i, t i ^ r) := by
  simp_rw [mul_sub,← pow_succ]
  rw [Finset.sum_sub_distrib]
  simp only [mul_comm _ b,← Finset.mul_sum]

private lemma scalar_formula_algebra (A B C D b S : ℝ) (hb : b=1-A) (hS : S=b^2+B)
    (hs : S ≠ 0) :
    (A^2-B-2*A*(C-b*B)/S+2*(D-b*C)/S)/S =
      (S-S^2-2*(b^3+C)+2*(b^4+D))/S^2 := by
  have hA : A=1-b := by linarith
  rw [hA]
  apply (eq_div_iff (pow_ne_zero 2 hs)).mpr
  field_simp [hs]
  rw [hS]
  ring

private lemma scalarCurvature_eq_chart_formula {m : ℕ} (t : Fin m → ℝ) (ht : t ∈ chartDomain m) :
    @scalarCurvature (m+1) t = formula (@chart (m+1) t) := by
  rw [scalarCurvature_powerSums t ht,chart_power_product,chart_power_product]
  have hp (k : ℕ) : P _ (@chart (m+1) t) k = remain t ^ k + ∑ i, t i ^ k := by
    simp only [P_evalSum]
    rw [Fin.sum_univ_castSucc]
    simp_rw [chart_castSucc,chart_last]
    ring
  unfold formula
  simp_rw [hp]
  change _ = (chartS2 t-chartS2 t^2-2*(remain t^3+∑ i,t i^3)+
    2*(remain t^4+∑ i,t i^4))/chartS2 t^2
  apply scalar_formula_algebra
  · rfl
  · rfl
  · exact (chartS2_pos t ht).ne'

private lemma chart_eq_simplex {m : ℕ} (x : Fin (m+1) → ℝ) (hx : x ∈ simplex (m+1)) :
    @chart (m+1) (fun i : Fin m => x i.castSucc) = x := by
  ext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · rw [chart_last]
    have hsum := hx.2
    rw [Fin.sum_univ_castSucc] at hsum
    dsimp only [remain]
    linarith
  · exact chart_castSucc _ _

private lemma simplex_chart_domain {m : ℕ} (x : Fin (m+1) → ℝ) (hx : x ∈ simplex (m+1)) :
    (fun i : Fin m => x i.castSucc) ∈ chartDomain m := by
  refine ⟨fun i => hx.1 i.castSucc,?_⟩
  have hsum := hx.2
  rw [Fin.sum_univ_castSucc] at hsum
  linarith [hx.1 (Fin.last m)]

private lemma scalInfty_eq_formula {n : ℕ} (hn : 3 ≤ n) (x : Fin n → ℝ) (hx : x ∈ simplex n) :
    scalInfty x = formula x := by
  cases n with
  | zero => omega
  | succ m =>
    have ht := simplex_chart_domain x hx
    have he : (fun i : Fin m => x (Fin.castLE (Nat.sub_le (m+1) 1) i)) =
        fun i : Fin m => x i.castSucc := by
      funext i
      congr 1
    change @scalarCurvature (m+1) (fun i : Fin m => x (Fin.castLE (Nat.sub_le (m+1) 1) i)) = _
    rw [he,scalarCurvature_eq_chart_formula _ ht,chart_eq_simplex x hx]

private def pairRest {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) : Fin n → ℝ :=
  fun k => if k = i ∨ k = j then 0 else x k
private lemma powerSum_rest {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j)
    (k : ℕ) (hk : 0 < k) :
    P _ x k = x i ^ k + x j ^ k + P _ (pairRest x i j) k := by
  have he (l : Fin n) : x l ^ k =
      (if l = i then x i ^ k else 0) + (if l = j then x j ^ k else 0) +
        pairRest x i j l ^ k := by
    by_cases hli : l = i
    · subst l; simp [pairRest,hij,zero_pow (Nat.ne_of_gt hk)]
    · by_cases hlj : l = j
      · subst l; simp [pairRest,hli,zero_pow (Nat.ne_of_gt hk)]
      · simp [pairRest,hli,hlj]
  simp only [P_evalSum]
  calc
    (∑ l, x l ^ k) = ∑ l, ((if l = i then x i ^ k else 0) +
      (if l = j then x j ^ k else 0) + pairRest x i j l ^ k) :=
        Finset.sum_congr rfl (fun l _ => he l)
    _ = _ := by simp only [Finset.sum_add_distrib]; simp
private lemma pairRest_nonneg {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (i j : Fin n) :
    ∀ k, 0 ≤ pairRest x i j k := by
  intro k
  simp only [pairRest]
  split_ifs
  · exact le_rfl
  · exact (hx k).le
private lemma pairRest_pos_exists {n : ℕ} (hn : 3 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (i j : Fin n) (hij : i ≠ j) :
    ∃ k, 0 < pairRest x i j k := by
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [hij.symm]
  have hs : (((Finset.univ : Finset (Fin n)).erase i).erase j).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hj]
    simp
    omega
  obtain ⟨k,hk⟩ := hs
  simp only [Finset.mem_erase,Finset.mem_univ,and_true] at hk
  exact ⟨k,by simpa [pairRest,hk.1,hk.2] using hx k⟩
private lemma pairRest_sum {n : ℕ} (x : Fin n → ℝ) (hx : x ∈ simplex n)
    (i j : Fin n) (hij : i ≠ j) :
    x i + x j + (∑ k, pairRest x i j k) = 1 := by
  have h := powerSum_rest x i j hij 1 (by norm_num)
  simpa [P_evalSum,hx.2] using h.symm
private lemma formula_rest {n : ℕ} (x : Fin n → ℝ) (hx : x ∈ simplex n)
    (i j : Fin n) (hij : i ≠ j) :
    formula x = pairR (x i + x j) (∑ k, pairRest x i j k) (P n (pairRest x i j) 2)
      (E n (pairRest x i j) 2) (E n (pairRest x i j) 3) (E n (pairRest x i j) 4)
      (x i * x j) := by
  rw [← formula_pair (x i) (x j) (pairRest x i j) (pairRest_sum x hx i j hij)]
  unfold formula
  simp_rw [powerSum_pair]
  rw [powerSum_rest x i j hij 2 (by norm_num),powerSum_rest x i j hij 3 (by norm_num),
    powerSum_rest x i j hij 4 (by norm_num)]
  try rfl
private lemma nonnegative_pair_invariants {r : ℕ} (z : Fin r → ℝ) (a b : ℝ)
    (hz : ∀ i, 0 ≤ z i) (hzp : ∃ i, 0 < z i) (ha : 0 < a) (hb : 0 < b)
    (hsum : a+b+(∑ i, z i)=1) :
    0 < a+b ∧ a+b < 1 ∧ 0 < a*b ∧ a*b ≤ (a+b)^2/4 ∧
      P _ z 2 ≤ (1-(a+b))^2 := by
  have hs : 0 < ∑ i, z i := by
    apply Finset.sum_pos' (fun i _ => hz i)
    obtain ⟨i,hi⟩ := hzp
    exact ⟨i,Finset.mem_univ _,hi⟩
  have hB := coordinateB_le_sum_sq z hz
  refine ⟨by linarith,by linarith,mul_pos ha hb,by nlinarith [sq_nonneg (a-b)],?_⟩
  have hsum' : (∑ i, z i)=1-(a+b) := by linarith
  simpa [hsum'] using hB
private lemma nonnegative_pair_K {r : ℕ} (z : Fin r → ℝ) (a b : ℝ)
    (hz : ∀ i, 0 ≤ z i) (hzp : ∃ i, 0 < z i) (ha : 0 < a) (hb : 0 < b)
    (hsum : a+b+(∑ i, z i)=1) :
    0 < pairK (a+b) (a*b) (∑ i, z i) (P _ z 2) (E r z 2) (E r z 3) (E r z 4) := by
  obtain ⟨hu0,hu1,hv0,hv1,hB⟩ := nonnegative_pair_invariants z a b hz hzp ha hb hsum
  exact coordinate_key_pos z _ _ _ _ _ _ _ (by linarith) rfl rfl rfl rfl rfl
    hzp hu0 hu1 hv0 hv1 hB
private lemma strict_mix_formula_nonnegative_rest {r : ℕ} (z : Fin r → ℝ) (a b t : ℝ)
    (hz : ∀ i, 0 ≤ z i) (hzp : ∃ i, 0 < z i) (ha : 0 < a) (hb : 0 < b)
    (hsum : a+b+(∑ i, z i)=1) (ht0 : 0 < t) (ht1 : t < 1) (hab : a ≠ b) :
    pairR (a+b) (∑ i, z i) (P _ z 2) (E r z 2) (E r z 3) (E r z 4) (a*b) <
      pairR (a+b) (∑ i, z i) (P _ z 2) (E r z 2) (E r z 3) (E r z 4)
        (mixProduct a b t) := by
  let a' := (1-t)*a+t*b
  let b' := t*a+(1-t)*b
  have ha' : 0 < a' := by dsimp [a']; positivity
  have hb' : 0 < b' := by dsimp [b']; positivity
  have habsum : a'+b'=a+b := by dsimp [a',b']; ring
  have hsum' : a'+b'+(∑ i, z i)=1 := by rw [habsum]; exact hsum
  have hk := nonnegative_pair_K z a b hz hzp ha hb hsum
  have hk' := nonnegative_pair_K z a' b' hz hzp ha' hb' hsum'
  obtain ⟨hu0,hu1,hv0,hv1,hB⟩ := nonnegative_pair_invariants z a b hz hzp ha hb hsum
  obtain ⟨hu'0,hu'1,hv'0,hv'1,hB'⟩ := nonnegative_pair_invariants z a' b' hz hzp ha' hb' hsum'
  have hBpos : 0 < P _ z 2 := coordinateB_pos z hzp
  have hv : a*b < a'*b' := by
    have hp := ttransform_product_increase ht0 ht1 hab
    dsimp [a',b']
    nlinarith [hp]
  rw [habsum] at hk' hv'1
  exact ratio_strict_increase hv (pairT_pos hu0 hv1 hBpos)
    (pairT_pos hu0 hv'1 hBpos) hk hk'
private lemma formula_oneT {n : ℕ} (hn : 3 ≤ n) {x q : Fin n → ℝ}
    (hx : x ∈ simplex n) (htr : D5.S3.Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector.IsTTransform x q) :
    formula x ≤ formula q ∧ (formula x = formula q → ∃ σ : Equiv.Perm (Fin n), q = x ∘ σ) := by
  have hp : q ∈ simplex n := by
    exact positiveT_simplex (show PositiveT x q from
      ⟨htr,hx.1,ttransform_positive htr hx.1,ttransform_sum htr⟩) hx
  obtain ⟨i,j,c,hc0,hc1,hq⟩ := htr
  have hperm (h : ∃ σ : Equiv.Perm (Fin n), q = x ∘ σ) :
      formula x ≤ formula q ∧ (formula x = formula q → ∃ σ : Equiv.Perm (Fin n), q = x ∘ σ) := by
    rcases h with ⟨σ,hσ⟩
    rw [hσ,formula_perm]
    exact ⟨le_rfl,fun _ => ⟨σ,rfl⟩⟩
  by_cases hij : i = j
  · apply hperm
    refine ⟨1,?_⟩
    subst j
    rw [hq]
    funext k
    simp
    ring
  by_cases hc : c = 0
  · apply hperm
    exact ⟨1,by simpa [hc] using hq⟩
  by_cases hc' : c = 1
  · apply hperm
    exact ⟨Equiv.swap i j,by simpa [hc'] using hq⟩
  by_cases hab : x i = x j
  · apply hperm
    refine ⟨1,?_⟩
    rw [hq]
    funext k
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Function.comp_apply,
      Equiv.Perm.coe_one,id_eq]
    by_cases hki : k = i
    · subst k; rw [Equiv.swap_apply_left,hab]; ring
    by_cases hkj : k = j
    · subst k; rw [Equiv.swap_apply_right,hab]; ring
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]; ring
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
  have hclt : c < 1 := lt_of_le_of_ne hc1 hc'
  have hrest : pairRest q i j = pairRest x i j := by
    funext k
    by_cases hki : k = i
    · subst k; simp [pairRest]
    by_cases hkj : k = j
    · subst k; simp [pairRest]
    · simp [pairRest,hki,hkj,hq,Equiv.swap_apply_of_ne_of_ne hki hkj]
      ring
  have hqi : q i = (1-c)*x i+c*x j := by simp [hq]
  have hqj : q j = c*x i+(1-c)*x j := by simp [hq]; ring
  have hu : q i+q j=x i+x j := by rw [hqi,hqj]; ring
  have hstrict : formula x < formula q := by
    rw [formula_rest x hx i j hij,formula_rest q hp i j hij,hrest,hu,hqi,hqj]
    exact strict_mix_formula_nonnegative_rest (pairRest x i j) (x i) (x j) c
      (pairRest_nonneg x hx.1 i j) (pairRest_pos_exists hn x hx.1 i j hij)
      (hx.1 i) (hx.1 j) (pairRest_sum x hx i j hij) hcpos hclt hab
  exact ⟨hstrict.le,fun he => False.elim (hstrict.ne he)⟩
private lemma formula_chain {n : ℕ} (hn : 3 ≤ n) {y x : Fin n → ℝ}
    (hy : y ∈ simplex n) (h : Relation.ReflTransGen PositiveT y x) :
    x ∈ simplex n ∧ formula y ≤ formula x ∧
      (formula y = formula x → ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ) := by
  induction h with
  | refl => exact ⟨hy,le_rfl,fun _ => ⟨1,rfl⟩⟩
  | @tail z q hzq hstep ih =>
    have hq := positiveT_simplex hstep ih.1
    obtain ⟨hle,heq⟩ := formula_oneT hn ih.1 hstep.1
    refine ⟨hq,ih.2.1.trans hle,?_⟩
    intro hsum
    have he1 : formula y = formula z := le_antisymm ih.2.1 (by rw [hsum]; exact hle)
    have he2 : formula z = formula q := le_antisymm hle (by rw [← hsum]; exact ih.2.1)
    obtain ⟨σ,hσ⟩ := ih.2.2 he1
    obtain ⟨τ,hτ⟩ := heq he2
    refine ⟨τ.trans σ,?_⟩
    rw [hτ,hσ]
    rfl
private lemma formula_result :
    ∀ n : ℕ, 3 ≤ n → ∀ x y : Fin n → ℝ,
      x ∈ simplex n → y ∈ simplex n → moreMixed x y →
      formula y ≤ formula x ∧
        ((¬ ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ) → formula y < formula x) := by
  intro n hn x y hx hy hm
  obtain ⟨_,hle,heq⟩ := formula_chain hn hy (moreMixed_positive_chain x y hx hy hm)
  refine ⟨hle,?_⟩
  intro hnot
  exact lt_of_le_of_ne hle (fun h => hnot (heq h))


def claim : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ x y : Fin n → ℝ,
    x ∈ simplex n → y ∈ simplex n → moreMixed x y →
      scalInfty y ≤ scalInfty x ∧
        ((¬ ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ) → scalInfty y < scalInfty x)

theorem result : claim := by
  intro n hn x y hx hy hm
  rw [scalInfty_eq_formula hn x hx, scalInfty_eq_formula hn y hy]
  exact formula_result n hn x y hx hy hm

end D5.S3.Geometry.AlphaGeometry.LogScalarCurvatureMonotone
