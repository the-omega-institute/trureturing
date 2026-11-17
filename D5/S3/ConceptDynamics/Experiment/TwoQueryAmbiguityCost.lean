/- GID: D5/S3/ConceptDynamics/Experiment/TwoQueryAmbiguityCost
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/TwoQueryAmbiguityCost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform-fibre ambiguity forces an actual mean trace-length lower bound for arbitrary exact terminating history policies. -/

import D5.S3.ConceptDynamics.Experiment.FiniteHistoryCanonicalTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiment.TwoQueryAmbiguityCost

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
open D5.S3.ConceptDynamics.Experiment.FiniteHistoryCanonicalTree
open D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost (boundedTree)

universe u
variable {W : Type u} {Q : Type} {Y : Q → Type} {L : Type}

/-- Candidates in a first fibre with a distinct partner giving the same second
answer. The second query may equal the first. -/
noncomputable def paired (read : (q : Q) → W → Y q) (D : Finset W) (z : Q) : Finset W :=
  by classical exact D.filter (fun x => ∃ x' ∈ D, x' ≠ x ∧ read z x' = read z x)

/-- Trace injectivity prohibits a stopping tree on two or more candidates. -/
theorem exact_tree_queries (read : (q : Q) → W → Y q) (D : Finset W)
    (p : PassiveProtocol Q Y) (hD : 2 ≤ D.card)
    (exactness : ∀ x ∈ D, ∀ x' ∈ D,
      runPassiveProtocol read p x = runPassiveProtocol read p x' → x = x') :
    ∃ q next, p = .query q next := by
  cases p with
  | stop =>
    have hsmall : D.card ≤ 1 := Finset.card_le_one.mpr (by
      intro x hx x' hx'
      exact exactness x hx x' hx' rfl)
    omega
  | query q next => exact ⟨q,next,rfl⟩

/-- A realized first branch cannot stop; candidates with a second-answer partner
cannot stop at two observations. These pointwise exclusions give the branch sum. -/
theorem first_branch_cost (read : (q : Q) → W → Y q) (C : Finset W)
    (q : Q) (next : Y q → PassiveProtocol Q Y)
    (exactness : ∀ x ∈ C, ∀ x' ∈ C,
      runPassiveProtocol read (.query q next) x =
        runPassiveProtocol read (.query q next) x' → x = x')
    (y : Y q) (m r : Nat) (hm : 2 ≤ m)
    (size : (fiber read C q y).card = m)
    (ambiguity : ∀ z : Q, r ≤ (paired read (fiber read C q y) z).card) :
    ∃ z rest, next y = .query z rest ∧
      (∀ x ∈ fiber read C q y,
        2 ≤ (runPassiveProtocol read (.query q next) x).length) ∧
      (∀ x ∈ paired read (fiber read C q y) z,
        3 ≤ (runPassiveProtocol read (.query q next) x).length) ∧
      2*m+r ≤ ∑ x ∈ fiber read C q y,
        (runPassiveProtocol read (.query q next) x).length := by
  classical
  let D := fiber read C q y
  have member (x : W) (hx : x ∈ D) : x ∈ C ∧ read q x = y := by
    simpa only [D, fiber, Finset.mem_filter] using hx
  have child : ∀ x ∈ D, ∀ x' ∈ D,
      runPassiveProtocol read (next y) x = runPassiveProtocol read (next y) x' → x = x' := by
    intro x hx x' hx' he
    apply exactness x (member x hx).1 x' (member x' hx').1
    simpa only [runPassiveProtocol, (member x hx).2, (member x' hx').2] using
      congrArg (List.cons ⟨q,y⟩) he
  obtain ⟨z,rest,hsecond⟩ := exact_tree_queries read D (next y) (by simpa [D,size] using hm) child
  have base (x : W) (hx : x ∈ D) :
      2 ≤ (runPassiveProtocol read (.query q next) x).length := by
    simp only [runPassiveProtocol, (member x hx).2, hsecond, List.length_cons]
    omega
  have extra (x : W) (hx : x ∈ paired read D z) :
      3 ≤ (runPassiveProtocol read (.query q next) x).length := by
    obtain ⟨hxD,x',hx'D,hne,he⟩ := Finset.mem_filter.mp hx
    cases hs : rest (read z x) with
    | stop =>
      have hc : x' = x := child x' hx'D x hxD (by
        simp only [hsecond, runPassiveProtocol, he, hs])
      exact False.elim (hne hc)
    | query a cont =>
      simp only [runPassiveProtocol, (member x hxD).2, hsecond, hs, List.length_cons]
      omega
  refine ⟨z,rest,hsecond,base,extra,?_⟩
  have pointwise (x : W) (hx : x ∈ D) :
      2 + (if x ∈ paired read D z then 1 else 0) ≤
        (runPassiveProtocol read (.query q next) x).length := by
    split_ifs with hp
    · have := extra x hp; omega
    · have := base x hx; omega
  have count : (∑ x ∈ D, if x ∈ paired read D z then 1 else 0) =
      (paired read D z).card := by
    rw [← Finset.sum_filter]
    have hf : D.filter (fun x => x ∈ paired read D z) = paired read D z := by
      ext x
      simp only [Finset.mem_filter, paired]
      tauto
    rw [hf]
    simp
  calc
    2*m+r ≤ 2*D.card+(paired read D z).card := by
      have ha := ambiguity z
      change r ≤ (paired read D z).card at ha
      have hd : D.card = m := size
      omega
    _ = ∑ x ∈ D, (2 + if x ∈ paired read D z then 1 else 0) := by
      rw [Finset.sum_add_distrib, count]
      simp [Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum pointwise

/-- Partition only over realized answers; no finite ambient response type. -/
theorem sum_first_fibres (read : (q : Q) → W → Y q) (C : Finset W)
    (q : Q) (f : W → Nat) :
    (∑ y ∈ answers read C q, ∑ x ∈ fiber read C q y, f x) = ∑ x ∈ C, f x := by
  classical
  exact Finset.sum_fiberwise_of_maps_to
    (fun x hx => Finset.mem_image_of_mem (read q) hx) f

/-- Rational normalization of the branch sum, with nonempty finite carrier. -/
theorem mean_of_total (C : Finset W) (hC : C.Nonempty) (m r k S : Nat)
    (hm : 2 ≤ m) (partition : C.card = m*k)
    (total : (2*m+r)*k ≤ S) :
    (2 : ℚ)+(r : ℚ)/m ≤ (S : ℚ)/C.card := by
  have hc : 0 < C.card := Finset.card_pos.mpr hC
  have hm0 : m ≠ 0 := by omega
  have hk0 : k ≠ 0 := by intro hk; rw [hk, Nat.mul_zero] at partition; omega
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
  calc
    (2 : ℚ)+(r : ℚ)/m = (((2*m+r)*k : Nat) : ℚ)/C.card := by
      rw [partition]
      push_cast
      field_simp [hmQ,hkQ]
      <;> ring
    _ ≤ (S : ℚ)/C.card := by
      apply (div_le_div_iff_of_pos_right (by exact_mod_cast hc : (0 : ℚ) < C.card)).2
      exact_mod_cast total

/-- Generic uniform-fibre lower bound for the actual trace of any exact tree.
The root query and every adaptive second query come from the supplied tree.
Only the candidate carrier is finite. Nonempty Q rules out vacuous fibre
hypotheses on a singleton carrier. r admissibility is retained explicitly. -/
theorem tree_two_query_cost [Nonempty Q]
    (read : (q : Q) → W → Y q) (C : Finset W) (hC : C.Nonempty)
    (m r : Nat) (hm : 2 ≤ m) (hr : r ≤ m)
    (sizes : ∀ q, ∀ y ∈ answers read C q, (fiber read C q y).card = m)
    (ambiguity : ∀ q, ∀ y ∈ answers read C q, ∀ z : Q,
      r ≤ (paired read (fiber read C q y) z).card)
    (p : PassiveProtocol Q Y)
    (exactness : ∀ x ∈ C, ∀ x' ∈ C,
      runPassiveProtocol read p x = runPassiveProtocol read p x' → x = x') :
    ∃ q next, p = .query q next ∧
      C.card = m*(answers read C q).card ∧
      (∀ y ∈ answers read C q,
        2*m+r ≤ ∑ x ∈ fiber read C q y, (runPassiveProtocol read p x).length) ∧
      (2*m+r)*(answers read C q).card ≤ ∑ x ∈ C, (runPassiveProtocol read p x).length ∧
      (2 : ℚ)+(r : ℚ)/m ≤ ((∑ x ∈ C, (runPassiveProtocol read p x).length : Nat) : ℚ)/(C.card : ℚ) := by
  classical
  obtain ⟨x,hx⟩ := hC
  let a : Q := Classical.choice inferInstance
  have hy : read a x ∈ answers read C a := Finset.mem_image_of_mem _ hx
  have hsub : fiber read C a (read a x) ⊆ C := Finset.filter_subset _ _
  have hcard : 2 ≤ C.card := by
    have hc := Finset.card_le_card hsub
    rw [sizes a _ hy] at hc
    omega
  obtain ⟨q,next,hroot⟩ := exact_tree_queries read C p hcard exactness
  have branches (y : Y q) (hy : y ∈ answers read C q) :
      2*m+r ≤ ∑ x ∈ fiber read C q y, (runPassiveProtocol read p x).length := by
    rw [hroot] at exactness ⊢
    exact (first_branch_cost read C q next exactness y m r hm (sizes q y hy)
      (ambiguity q y hy)).choose_spec.choose_spec.2.2.2
  have partition : C.card = m*(answers read C q).card := by
    calc
      C.card = ∑ y ∈ answers read C q, (fiber read C q y).card := by
        simpa using (sum_first_fibres read C q (fun _ => 1)).symm
      _ = ∑ _y ∈ answers read C q, m := Finset.sum_congr rfl (fun y hy => sizes q y hy)
      _ = _ := by simp [Nat.mul_comm]
  have total : (2*m+r)*(answers read C q).card ≤
      ∑ x ∈ C, (runPassiveProtocol read p x).length := by
    calc
      _ = ∑ _y ∈ answers read C q, (2*m+r) := by simp [Nat.mul_comm]
      _ ≤ ∑ y ∈ answers read C q, ∑ x ∈ fiber read C q y,
          (runPassiveProtocol read p x).length := Finset.sum_le_sum branches
      _ = _ := sum_first_fibres read C q _
  exact ⟨q,next,hroot,partition,branches,total,mean_of_total C ⟨x,hx⟩ m r _ _ hm partition total⟩

/-- Transfer the new lower bound through the authenticated unpruned bridge.
The supplied tr/lab are actual completed executions of an arbitrary pointwise
terminating correct history policy; no bound on their depths is imposed. -/
theorem history_two_query_cost [Nonempty Q]
    (read : (q : Q) → W → Y q) (C : Finset W) (hC : C.Nonempty)
    (m r : Nat) (hm : 2 ≤ m) (hr : r ≤ m)
    (sizes : ∀ q, ∀ y ∈ answers read C q, (fiber read C q y).card = m)
    (ambiguity : ∀ q, ∀ y ∈ answers read C q, ∀ z : Q,
      r ≤ (paired read (fiber read C q y) z).card)
    (policy : Hist Y → Sum Q L) (tr : W → Hist Y) (lab : W → L)
    (runs : ∀ x ∈ C, ∃ n, execute read policy n [] x = some (tr x,lab x))
    (decode : L → W) (correct : ∀ x ∈ C, decode (lab x) = x) :
    ∃ q, policy [] = .inl q ∧
      C.card = m*(answers read C q).card ∧
      (∀ y ∈ answers read C q, 2*m+r ≤ ∑ x ∈ fiber read C q y, (tr x).length) ∧
      (2*m+r)*(answers read C q).card ≤ ∑ x ∈ C, (tr x).length ∧
      (2 : ℚ)+(r : ℚ)/m ≤ ((∑ x ∈ C, (tr x).length : Nat) : ℚ)/(C.card : ℚ) := by
  classical
  have terminates : ∀ x ∈ C, ∃ n t l, execute read policy n [] x = some (t,l) := by
    intro x hx
    obtain ⟨n,hn⟩ := runs x hx
    exact ⟨n,tr x,lab x,hn⟩
  have correct' : ∀ x ∈ C, ∀ n t l,
      execute read policy n [] x = some (t,l) → decode l = x := by
    intro x hx n t l hn
    obtain ⟨k,hk⟩ := runs x hx
    have he := execute_unique read policy n k [] x t (tr x) l (lab x) hn hk
    have hl : l = lab x := congrArg Prod.snd he
    simpa only [hl] using correct x hx
  obtain ⟨N,hN⟩ := finite_history_canonical_tree read policy C terminates
  obtain ⟨hbound,hexact,hweighted,hcorrect⟩ := hN N le_rfl
  have trace (x : W) (hx : x ∈ C) :
      runPassiveProtocol read (boundedTree policy N []) x = tr x := by
    obtain ⟨k,hk⟩ := runs x hx
    exact (hexact x hx k (tr x) (lab x) hk).1
  obtain ⟨q,next,hroot,hcard,hbranches,htotal,hmean⟩ :=
    tree_two_query_cost read C hC m r hm hr sizes ambiguity
      (boundedTree policy N []) (hcorrect decode correct').2
  have root : policy [] = .inl q := by
    cases N with
    | zero => simp [boundedTree] at hroot
    | succ n =>
      cases hp : policy [] with
      | inr l => simp [boundedTree,hp] at hroot
      | inl a =>
        simp only [boundedTree,hp] at hroot
        have he : some a = some q := congrArg
          (fun t : PassiveProtocol Q Y => match t with
            | .stop => none
            | .query b _ => some b) hroot
        exact congrArg Sum.inl (Option.some.inj he)
  have totalEq : (∑ x ∈ C, (runPassiveProtocol read (boundedTree policy N []) x).length) =
      ∑ x ∈ C, (tr x).length := Finset.sum_congr rfl (fun x hx => congrArg List.length (trace x hx))
  refine ⟨q,root,hcard,?_,?_,?_⟩
  · intro y hy
    have he : (∑ x ∈ fiber read C q y,
        (runPassiveProtocol read (boundedTree policy N []) x).length) =
        ∑ x ∈ fiber read C q y, (tr x).length := by
      apply Finset.sum_congr rfl
      intro x hx
      exact congrArg List.length (trace x (Finset.mem_filter.mp hx).1)
    simpa only [he] using hbranches y hy
  · simpa only [totalEq] using htotal
  · simpa only [totalEq] using hmean

set_option pp.proofs false in
#print tree_two_query_cost
set_option pp.proofs false in
#print history_two_query_cost
#print axioms exact_tree_queries
#print axioms first_branch_cost
#print axioms sum_first_fibres
#print axioms mean_of_total
#print axioms tree_two_query_cost
#print axioms history_two_query_cost

end D5.S3.ConceptDynamics.Experiment.TwoQueryAmbiguityCost
