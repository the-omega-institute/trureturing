/- GID: D5/S3/Observer/Budget/ResidueFirstStepOptimality
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/ResidueFirstStepOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Terminal selectors attain exact original-cost sibling first-step minima. -/

import D5.S3.Observer.Budget.ResiduePosteriorClosure
import D5.S3.Observer.Budget.AdaptiveSeparationDepthUpperBound
import Mathlib.Order.WellFounded

set_option autoImplicit false
open scoped BigOperators
open D5.S3.Observer.Budget.ResidueLeafOptimality
open D5.S3.Observer.Budget.ResiduePosteriorClosure
open D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
namespace D5.S3.Observer.Budget.ResidueFirstStepOptimality

/-- The complete chronological trace, with ordinary pairs for constant response type. -/
def trace {X : Type} (q : X → X → ℕ) (T : PassiveProtocol X (fun _ => ℕ)) (a : X) :
    List (X × ℕ) := (runPassiveProtocol q T a).map (fun z => (z.1, z.2))

/-- A suffix is legal, has the actual replies, and ends at a genuine selector stop. -/
def terminal {X : Type} (q : X → X → ℕ) (D : List (X × ℕ) → Option X)
    (P : List (X × ℕ)) (a : X) (H : List (X × ℕ)) : Prop :=
  legal D P H ∧ (∀ z ∈ H, q z.1 a = z.2) ∧ D (P ++ H) = none

/-- Follow a tree along the entire supplied history; wrong centers stop immediately. -/
def treeSelector {X : Type} [DecidableEq X] :
    PassiveProtocol X (fun _ => ℕ) → List (X × ℕ) → Option X
  | .stop, _ => none
  | .query c _, [] => some c
  | .query c next, (c', r) :: H => if c' = c then treeSelector (next r) H else none

/-- Original rational costs of all eventually terminating zero-error history selectors.
The witness histories are actual terminal traces, not bounds on the policies. -/
def policyCosts {X : Type} [DecidableEq X] (q : X → X → ℕ) (μ : X → ℚ)
    (S : Finset X) (P : List (X × ℕ)) : Set ℚ :=
  {v | ∃ (D : List (X × ℕ) → Option X) (H : X → List (X × ℕ)),
    (∀ a ∈ S, terminal q D P a (H a)) ∧
    (∀ a ∈ S, ∀ b ∈ S, ∀ L,
      terminal q D P a L → terminal q D P b L → a = b) ∧
    v = ∑ a ∈ S, μ a * (H a).length}

/-- Original rational costs of identifying protocols, without a syntactic depth bound. -/
def treeCosts {X : Type} [DecidableEq X] (q : X → X → ℕ) (μ : X → ℚ)
    (S : Finset X) : Set ℚ :=
  {v | ∃ T : PassiveProtocol X (fun _ => ℕ),
    (∀ a ∈ S, ∀ b ∈ S, runPassiveProtocol q T a = runPassiveProtocol q T b → a = b) ∧
    v = ∑ a ∈ S, μ a * (runPassiveProtocol q T a).length}

/-- Eventually terminating selectors and well-founded query trees have the same exact
original-cost minima. The sibling recurrences charge an internal first query only once. -/
theorem residue_first_step_optimality (p e : ℕ) [Fact p.Prime]
    (μ : ZMod (p ^ e) → ℚ) (positive : ∀ a, 0 < μ a) (normalized : ∑ a, μ a = 1) :
    let q := residueReadout p e
    (∀ D P a H n, terminal q D P a H → H.length ≤ n →
      trace q (unroll D n P) a = H) ∧
    (∀ D P a H L, terminal q D P a H → terminal q D P a L → H = L) ∧
    (∀ T : PassiveProtocol (ZMod (p ^ e)) (fun _ => ℕ), ∀ a,
      terminal q (treeSelector T) [] a (trace q T a)) ∧
    (∀ (S : Finset (ZMod (p ^ e))) D P,
      (∀ a ∈ S, ∃ H, terminal q D P a H) →
      ∃ N, ∀ n ≥ N, ∀ a ∈ S, ∀ H, terminal q D P a H →
        trace q (unroll D n P) a = H ∧
        (runPassiveProtocol q (unroll D n P) a).length = H.length) ∧
    (∀ S P, policyCosts q μ S P = treeCosts q μ S) ∧
    ∃ K : Finset (ZMod (p ^ e)) → ℚ,
      (∀ S P, IsLeast (policyCosts q μ S P) (K S)) ∧
      (∀ S, IsLeast (treeCosts q μ S) (K S)) ∧
      K ∅ = 0 ∧ (∀ a, K {a} = 0) ∧ (e = 0 → K Finset.univ = 0) ∧
      (∀ S P, S.Nonempty →
        IsLeast {v : ℚ | ∃ w ∈ policyCosts q μ S P, v = w / (∑ a ∈ S, μ a)}
          (K S / (∑ a ∈ S, μ a))) ∧
      (∀ (d : ℕ) (hd : d < e) (j : ZMod (p ^ (d + 1))),
        K (siblings p e d hd {j}) = K (node p e (d + 1) (Nat.succ_le_of_lt hd) j)) ∧
      (∀ (d : ℕ) (hd : d < e) (b : ZMod (p ^ d))
        (I : Finset (ZMod (p ^ (d + 1)))), I.Nonempty → I ⊆ children p d b →
        let S := siblings p e d hd I
        let C := node p e (d + 1) (Nat.succ_le_of_lt hd)
        let E := fun j => siblings p e d hd (I.erase j)
        (d + 1 < e → IsLeast {v : ℚ | ∃ j ∈ I,
          v = K (C j) + K (E j) + (∑ a ∈ S, μ a) - (∑ a ∈ C j, μ a)} (K S)) ∧
        (d + 1 = e → I.card = 1 → K S = 0) ∧
        (d + 1 = e → 2 ≤ I.card → IsLeast {v : ℚ | ∃ j ∈ I,
          v = (∑ a ∈ S, μ a) + K (E j)} (K S))) := by
  classical
  dsimp only
  let X := ZMod (p ^ e)
  let q := residueReadout p e
  obtain ⟨threshold, exactDepth, top, cards, childrenFacts, geometry, outside,
    nonpath, partition, heights, roots, singletonUpdate, shapes, histories, massPos, rest⟩ :=
    residue_posterior_closure p e μ positive normalized
  have feasible : ∃ T : PassiveProtocol X (fun _ => ℕ),
      Function.Injective (runPassiveProtocol q T) := by
    by_cases he : e = 0
    · refine ⟨.stop, ?_⟩
      subst e
      have : Subsingleton (ZMod (p ^ 0)) := by
        simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
      exact fun _ _ _ => Subsingleton.elim _ _
    · obtain ⟨T, hT, _⟩ :=
        AdaptiveSeparationDepthUpperBound.adaptive_separation_depth_upper_bound q
          (fun a b hab => ⟨a, by
            intro h
            have ha : q a a = e := (top a a).2 rfl
            have hb : b = a := (top b a).1 (h.symm.trans ha)
            exact hab hb.symm⟩)
      exact ⟨T, hT⟩
  let cost (S : Finset X) (T : PassiveProtocol X (fun _ => ℕ)) : ℚ :=
    ∑ a ∈ S, μ a * (runPassiveProtocol q T a).length
  let identifies (S : Finset X) (T : PassiveProtocol X (fun _ => ℕ)) : Prop :=
    ∀ a ∈ S, ∀ b ∈ S, runPassiveProtocol q T a = runPassiveProtocol q T b → a = b
  have attained (S : Finset X) : ∃ T, identifies S T ∧ ∀ R, identifies S R →
      cost S T ≤ cost S R := by
    let Q : ℕ := ∏ a ∈ S, (μ a).den
    have Qpos : 0 < Q := Finset.prod_pos (fun a _ => (μ a).den_pos)
    let w (a : X) : ℕ := (μ a).num.toNat * ∏ b ∈ S.erase a, (μ b).den
    have scale (a : X) (ha : a ∈ S) : (Q : ℚ) * μ a = w a := by
      have num : (0 : ℤ) ≤ (μ a).num := (Rat.num_pos.mpr (positive a)).le
      have prod := Finset.mul_prod_erase S (fun b => (μ b).den) ha
      dsimp only [Q, w]
      have castnum : ((μ a).num.toNat : ℚ) = (μ a).num := by
        exact_mod_cast Int.toNat_of_nonneg num
      rw [← prod, Nat.cast_mul, Nat.cast_mul, castnum]
      rw [mul_right_comm, Rat.den_mul_eq_num]
    let objective (T : PassiveProtocol X (fun _ => ℕ)) : ℕ :=
      ∑ a ∈ S, w a * (runPassiveProtocol q T a).length
    have objective_eq (T) : (objective T : ℚ) = (Q : ℚ) * cost S T := by
      simp only [objective, cost, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [← scale a ha, mul_assoc]
    have : Nonempty {T // identifies S T} :=
      ⟨⟨feasible.choose, fun a _ b _ h => feasible.choose_spec h⟩⟩
    let T := Function.argmin (fun T : {T // identifies S T} => objective T.val)
    refine ⟨T.val, T.property, fun R hR => ?_⟩
    have h := Function.argmin_le (fun T : {T // identifies S T} => objective T.val) ⟨R,hR⟩
    have hq : (objective T.val : ℚ) ≤ objective R := by exact_mod_cast h
    rw [objective_eq, objective_eq] at hq
    exact (mul_le_mul_iff_right₀ (by exact_mod_cast Qpos : (0 : ℚ) < Q)).1 hq
  have persist (D : List (X × ℕ) → Option X) (P : List (X × ℕ)) (a : X)
      (H : List (X × ℕ)) (n : ℕ) (ht : terminal q D P a H) (hn : H.length ≤ n) :
      trace q (unroll D n P) a = H := by
    induction H generalizing P n with
    | nil =>
      obtain ⟨_, _, stop⟩ := ht
      have stop' : D P = none := by simpa only [List.append_nil] using stop
      cases n with
      | zero => rfl
      | succ n => simp only [trace, unroll, stop', runPassiveProtocol, List.map_nil]
    | cons z H ih =>
      obtain ⟨c,r⟩ := z
      obtain ⟨⟨hc,hl⟩, hr, stop⟩ := ht
      have hca : q c a = r := hr _ (List.mem_cons_self ..)
      cases n with
      | zero => simp at hn
      | succ n =>
        simp only [trace, unroll, hc, runPassiveProtocol, List.map_cons, hca]
        congr 1
        apply ih (P ++ [(c,r)]) n
        · refine ⟨hl, fun z hz => hr z (List.mem_cons_of_mem _ hz), ?_⟩
          simpa only [List.append_assoc, List.singleton_append] using stop
        · simpa only [List.length_cons, Nat.succ_le_succ_iff] using hn
  have unique (D : List (X × ℕ) → Option X) (P : List (X × ℕ)) (a : X)
      (H L : List (X × ℕ)) (hH : terminal q D P a H) (hL : terminal q D P a L) : H = L :=
    (persist D P a H (max H.length L.length) hH (le_max_left ..)).symm.trans
      (persist D P a L _ hL (le_max_right ..))
  have realizes (T : PassiveProtocol X (fun _ => ℕ)) (a : X) :
      terminal q (treeSelector T) [] a (trace q T a) := by
    induction T with
    | stop => simp [terminal, trace, runPassiveProtocol, legal, treeSelector]
    | query c next ih =>
      have residual (r : ℕ) (L P : List (X × ℕ)) :
          legal (treeSelector (.query c next)) ((c,r) :: P) L ↔
            legal (treeSelector (next r)) P L := by
        induction L generalizing P with
        | nil => rfl
        | cons z L ihL =>
          obtain ⟨x,t⟩ := z
          simp only [legal, treeSelector, ite_true, List.cons_append, ihL]
      have h := ih (q c a)
      refine ⟨?_, ?_, ?_⟩
      · change some c = some c ∧ legal (treeSelector (.query c next)) [(c,q c a)]
          (trace q (next (q c a)) a)
        exact ⟨rfl, (residual _ _ []).2 h.1⟩
      · simpa only [trace, runPassiveProtocol, List.map_cons, List.forall_mem_cons,
          Prod.fst, Prod.snd, true_and] using h.2.1
      · simpa only [trace, runPassiveProtocol, List.map_cons, List.nil_append,
          treeSelector, ite_true] using h.2.2
  have family (S : Finset X) (D : List (X × ℕ) → Option X) (P : List (X × ℕ))
      (terminates : ∀ a ∈ S, ∃ H, terminal q D P a H) :
      ∃ N, ∀ n ≥ N, ∀ a ∈ S, ∀ H, terminal q D P a H →
        trace q (unroll D n P) a = H ∧
        (runPassiveProtocol q (unroll D n P) a).length = H.length := by
    let L (a : X) := if ha : a ∈ S then (terminates a ha).choose else []
    have hL (a : X) (ha : a ∈ S) : terminal q D P a (L a) := by
      simpa only [L, dif_pos ha] using (terminates a ha).choose_spec
    refine ⟨S.sup (fun a => (L a).length), fun n hn a ha H hH => ?_⟩
    have he := unique D P a (L a) H (hL a ha) hH
    have bound : H.length ≤ n := he ▸ (Finset.le_sup (f := fun a => (L a).length) ha).trans hn
    have tr := persist D P a H n hH bound
    exact ⟨tr, by simpa only [trace, List.length_map] using congrArg List.length tr⟩
  have trace_inj (T R : PassiveProtocol X (fun _ => ℕ)) (a b : X) :
      trace q T a = trace q R b ↔ runPassiveProtocol q T a = runPassiveProtocol q R b := by
    have inj : Function.Injective (fun z : Sigma (fun _ : X => ℕ) => (z.1,z.2)) := by
      intro x y h
      cases x; cases y
      simpa only [Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq] using h
    exact ⟨fun h => (List.map_injective_iff.mpr inj) h,
      fun h => congrArg (List.map (fun z : Sigma (fun _ : X => ℕ) => (z.1,z.2))) h⟩
  have equalCosts (S : Finset X) (P : List (X × ℕ)) :
      policyCosts q μ S P = treeCosts q μ S := by
    ext v
    constructor
    · rintro ⟨D,H,hH,hI,rfl⟩
      obtain ⟨N,hN⟩ := family S D P (fun a ha => ⟨H a,hH a ha⟩)
      refine ⟨unroll D N P, ?_, ?_⟩
      · intro a ha b hb hab
        have he : H a = H b := by
          rw [← (hN N le_rfl a ha _ (hH a ha)).1,
            ← (hN N le_rfl b hb _ (hH b hb)).1]
          exact congrArg (List.map (fun z => (z.1,z.2))) hab
        exact hI a ha b hb (H a) (hH a ha) (he.symm ▸ hH b hb)
      · apply Finset.sum_congr rfl
        intro a ha
        rw [(hN N le_rfl a ha _ (hH a ha)).2]
    · rintro ⟨T,hI,rfl⟩
      let D := fun (H : List (X × ℕ)) => treeSelector T (H.drop P.length)
      have shift (L R : List (X × ℕ)) : legal D (P ++ R) L ↔ legal (treeSelector T) R L := by
        induction L generalizing R with
        | nil => rfl
        | cons z L ih =>
          obtain ⟨c,r⟩ := z
          simp only [legal, D, List.drop_left, List.append_assoc, ih]
      have hTerm (a : X) : terminal q D P a (trace q T a) := by
        have h := realizes T a
        refine ⟨?_, h.2.1, ?_⟩
        · simpa only [List.append_nil] using (shift (trace q T a) []).2 h.1
        · simpa only [D, List.drop_left, List.nil_append] using h.2.2
      refine ⟨D,trace q T,fun a _ => hTerm a, ?_, ?_⟩
      · intro a ha b hb L hLa hLb
        have haL := unique D P a _ L (hTerm a) hLa
        have hbL := unique D P b _ L (hTerm b) hLb
        exact hI a ha b hb ((trace_inj T T a b).1 (haL.trans hbL.symm))
      · simp only [trace, List.length_map]
  choose best bestIdent bestLe using attained
  let K := fun S => cost S (best S)
  have leastTree (S : Finset X) : IsLeast (treeCosts q μ S) (K S) :=
    ⟨⟨best S, bestIdent S, rfl⟩, fun v ⟨R,hR,hv⟩ => hv ▸ bestLe S R hR⟩
  let mass (S : Finset X) : ℚ := ∑ a ∈ S, μ a
  have costNonneg (S : Finset X) (T) : 0 ≤ cost S T :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (positive a).le (Nat.cast_nonneg _))
  have small (S : Finset X) (hS : S.card ≤ 1) : K S = 0 := by
    apply le_antisymm
    · have h := bestLe S .stop (fun a ha b hb _ => (Finset.card_le_one.mp hS) a ha b hb)
      simpa only [cost, runPassiveProtocol, List.length_nil, Nat.cast_zero, mul_zero,
        Finset.sum_const_zero] using h
    · exact costNonneg S _
  have queryCost (S : Finset X) (c : X) (next : ℕ → PassiveProtocol X (fun _ => ℕ)) :
      cost S (.query c next) = mass S +
        ∑ a ∈ S, μ a * (runPassiveProtocol q (next (q c a)) a).length := by
    simp only [cost, mass, runPassiveProtocol, List.length_cons, Nat.cast_add, Nat.cast_one,
      mul_add, mul_one, Finset.sum_add_distrib, add_comm]
  have rootInside (S : Finset X) (big : 1 < S.card)
      (constant : ∀ c, c ∉ S → ∃ r, ∀ a ∈ S, q c a = r) :
      ∃ c next, best S = .query c next ∧ c ∈ S := by
    cases hT : best S with
    | stop =>
      have sub : S.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb =>
        bestIdent S a ha b hb (by simp only [hT, runPassiveProtocol]))
      omega
    | query c next =>
      refine ⟨c,next,rfl,?_⟩
      by_contra hc
      obtain ⟨r,hr⟩ := constant c hc
      have id : identifies S (next r) := by
        intro a ha b hb hab
        apply bestIdent S a ha b hb
        simp only [hT, runPassiveProtocol, hr a ha, hr b hb, hab]
      have cheaper := bestLe S (next r) id
      have eq : cost S (best S) = mass S + cost S (next r) := by
        rw [hT, queryCost]
        congr 1
        exact Finset.sum_congr rfl (fun a ha => by rw [hr a ha])
      have pos : 0 < mass S := massPos S (Finset.card_pos.mp (by omega))
      linarith
  have siblingConstant (d : ℕ) (hd : d < e) (b : ZMod (p ^ d))
      (I : Finset (ZMod (p ^ (d + 1)))) (ne : I.Nonempty) (valid : I ⊆ children p d b)
      (c : X) (hc : c ∉ siblings p e d hd I) :
      ∃ r, ∀ a ∈ siblings p e d hd I, q c a = r := by
    obtain ⟨r,_,hr⟩ := outside d hd b I ne valid c hc
    refine ⟨r,fun a ha => ?_⟩
    have eq := hr r
    rw [if_pos rfl] at eq
    have mem : a ∈ (siblings p e d hd I).filter
        (fun a => residueReadout p e c a = r) := eq.symm ▸ ha
    exact (Finset.mem_filter.mp mem).2
  have pieces (d : ℕ) (hd : d < e) (I : Finset (ZMod (p ^ (d + 1))))
      (j : ZMod (p ^ (d + 1))) (hj : j ∈ I) :
      let C := node p e (d + 1) (Nat.succ_le_of_lt hd) j
      let E := siblings p e d hd (I.erase j)
      Disjoint C E ∧ C ∪ E = siblings p e d hd I := by
    dsimp only
    constructor
    · apply Finset.disjoint_left.mpr
      intro a ha he
      simp only [node, siblings, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase] at ha he
      exact he.1 ha
    · ext a
      simp only [Finset.mem_union, node, siblings, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_erase]
      by_cases h : primePowerProjection p (Nat.succ_le_of_lt hd) a = j
      · simp only [h, hj, true_or]
      · simp only [h, false_or]
        exact and_iff_right h
  have responses (d : ℕ) (hd : d < e) (b : ZMod (p ^ d))
      (I : Finset (ZMod (p ^ (d + 1)))) (valid : I ⊆ children p d b)
      (j : ZMod (p ^ (d + 1))) (hj : j ∈ I) (c : X)
      (hc : c ∈ node p e (d + 1) (Nat.succ_le_of_lt hd) j) :
      (∀ a ∈ node p e (d + 1) (Nat.succ_le_of_lt hd) j, d < q c a) ∧
      (∀ a ∈ siblings p e d hd (I.erase j), q c a = d) := by
    have hpc : primePowerProjection p (Nat.succ_le_of_lt hd) c = j :=
      (Finset.mem_filter.mp hc).2
    have hcs : c ∈ siblings p e d hd I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc ▸ hj⟩
    constructor
    · intro a ha
      have hpa := (Finset.mem_filter.mp ha).2
      exact (threshold (d + 1) _ a c).2 (hpa.trans hpc.symm)
    · have fiber := (geometry d hd b I valid c).2.2.2 hcs |>.1
      rw [hpc] at fiber
      intro a ha
      have mem : a ∈ (siblings p e d hd I).filter
          (fun a => residueReadout p e c a = d) := fiber.symm ▸ ha
      exact (Finset.mem_filter.mp mem).2
  have costSplit (C E : Finset X) (dis : Disjoint C E) (T) :
      cost (C ∪ E) T = cost C T + cost E T := Finset.sum_union dis
  have splice (C E : Finset X) (dis : Disjoint C E) (c : X) (d : ℕ)
      (next : ℕ → PassiveProtocol X (fun _ => ℕ)) (R : PassiveProtocol X (fun _ => ℕ))
      (hit : ∀ a ∈ C, d < q c a) (miss : ∀ a ∈ E, q c a = d)
      (idC : identifies C (.query c next)) (idE : identifies E R) :
      let U := PassiveProtocol.query c (fun r => if r = d then R else next r)
      identifies (C ∪ E) U ∧
      (∀ a ∈ C, runPassiveProtocol q U a = runPassiveProtocol q (.query c next) a) ∧
      (∀ a ∈ E, runPassiveProtocol q U a = ⟨c,d⟩ :: runPassiveProtocol q R a) ∧
      cost (C ∪ E) U = cost C (.query c next) + cost E R + mass E := by
    dsimp only
    let U := PassiveProtocol.query c (fun r => if r = d then R else next r)
    have onC (a : X) (ha : a ∈ C) :
        runPassiveProtocol q U a = runPassiveProtocol q (.query c next) a := by
      simp only [U, runPassiveProtocol, if_neg (Nat.ne_of_gt (hit a ha))]
    have onE (a : X) (ha : a ∈ E) :
        runPassiveProtocol q U a = ⟨c,d⟩ :: runPassiveProtocol q R a := by
      simp only [U, runPassiveProtocol, miss a ha, ite_true]
    refine ⟨?_,onC,onE,?_⟩
    · intro a ha b hb hab
      rcases Finset.mem_union.mp ha with ha | ha <;>
        rcases Finset.mem_union.mp hb with hb | hb
      · exact idC a ha b hb ((onC a ha).symm.trans (hab.trans (onC b hb)))
      · rw [onC a ha, onE b hb] at hab
        have h := congrArg (fun L => L.head?) hab
        simp only [runPassiveProtocol, List.head?_cons, Option.some.injEq] at h
        have eq := congrArg Sigma.snd h
        exact False.elim (Nat.ne_of_gt (hit a ha) eq)
      · rw [onE a ha, onC b hb] at hab
        have h := congrArg (fun L => L.head?) hab
        simp only [runPassiveProtocol, List.head?_cons, Option.some.injEq] at h
        have eq := congrArg Sigma.snd h
        exact False.elim (Nat.ne_of_gt (hit b hb) eq.symm)
      · rw [onE a ha, onE b hb] at hab
        exact idE a ha b hb (List.cons.inj hab).2
    · rw [costSplit C E dis]
      have hC : cost C U = cost C (.query c next) :=
        Finset.sum_congr rfl (fun a ha => by rw [onC a ha])
      have hE : cost E U = cost E R + mass E := by
        dsimp only [cost, mass]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        rw [onE a ha, List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      rw [hC,hE,add_assoc]
  have recurrence (d : ℕ) (hd : d < e) (b : ZMod (p ^ d))
      (I : Finset (ZMod (p ^ (d + 1)))) (ne : I.Nonempty) (valid : I ⊆ children p d b) :
      (d + 1 < e → IsLeast {v : ℚ | ∃ j ∈ I,
        v = K (node p e (d + 1) (Nat.succ_le_of_lt hd) j) +
          K (siblings p e d hd (I.erase j)) + mass (siblings p e d hd I) -
          mass (node p e (d + 1) (Nat.succ_le_of_lt hd) j)}
        (K (siblings p e d hd I))) ∧
      (d + 1 = e → I.card = 1 → K (siblings p e d hd I) = 0) ∧
      (d + 1 = e → 2 ≤ I.card → IsLeast {v : ℚ | ∃ j ∈ I,
        v = mass (siblings p e d hd I) + K (siblings p e d hd (I.erase j))}
        (K (siblings p e d hd I))) := by
    let S := siblings p e d hd I
    let C := node p e (d + 1) (Nat.succ_le_of_lt hd)
    let E := fun j => siblings p e d hd (I.erase j)
    have cne (j) : (C j).Nonempty := Finset.card_pos.mp (by
      rw [cards]; exact pow_pos (show 0 < p from (Fact.out : p.Prime).pos) _)
    have split (j) (hj : j ∈ I) : Disjoint (C j) (E j) ∧ C j ∪ E j = S := pieces d hd I j hj
    have massSplit (j) (hj : j ∈ I) : mass S = mass (C j) + mass (E j) := by
      rw [← (split j hj).2]
      exact Finset.sum_union (split j hj).1
    have subC (j) (hj : j ∈ I) : C j ⊆ S := by
      rw [← (split j hj).2]; exact Finset.subset_union_left
    have subE (j) (hj : j ∈ I) : E j ⊆ S := by
      rw [← (split j hj).2]; exact Finset.subset_union_right
    have lower (big : 1 < S.card) : ∃ j ∈ I,
        K (C j) + K (E j) + mass (E j) ≤ K S ∧
        mass S + K (E j) ≤ K S := by
      obtain ⟨c,next,hT,hc⟩ := rootInside S big (siblingConstant d hd b I ne valid)
      let j := primePowerProjection p (Nat.succ_le_of_lt hd) c
      have hj : j ∈ I := (Finset.mem_filter.mp hc).2
      have hcC : c ∈ C j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
      obtain ⟨hit,miss⟩ := responses d hd b I valid j hj c hcC
      have idC : identifies (C j) (best S) :=
        fun a ha b hb h => bestIdent S a (subC j hj ha) b (subC j hj hb) h
      have idE : identifies (E j) (next d) := by
        intro a ha b hb h
        apply bestIdent S a (subE j hj ha) b (subE j hj hb)
        simp only [hT, runPassiveProtocol, miss a ha, miss b hb, h]
      have ce : cost (E j) (best S) = mass (E j) + cost (E j) (next d) := by
        rw [hT,queryCost]
        congr 1
        exact Finset.sum_congr rfl (fun a ha => by rw [miss a ha])
      have cs : K S = cost (C j) (best S) + cost (E j) (best S) := by
        dsimp only [K]
        rw [← (split j hj).2, costSplit _ _ (split j hj).1]
      have lc := bestLe (C j) (best S) idC
      have le := bestLe (E j) (next d) idE
      have first : mass (C j) ≤ cost (C j) (best S) := by
        rw [hT, queryCost]
        exact le_add_of_nonneg_right (Finset.sum_nonneg (fun a _ =>
          mul_nonneg (positive a).le (Nat.cast_nonneg _)))
      refine ⟨j,hj,?_,?_⟩
      · change cost (C j) (best (C j)) + cost (E j) (best (E j)) + _ ≤ _
        linarith
      · rw [massSplit j hj]
        change _ + _ + cost (E j) (best (E j)) ≤ _
        linarith
    constructor
    · intro hn
      have bigC (j) : 1 < (C j).card := by
        rw [cards]
        exact one_lt_pow₀ (show 1 < p from (Fact.out : p.Prime).one_lt) (by omega)
      have big : 1 < S.card := lt_of_lt_of_le (bigC ne.choose)
        (Finset.card_le_card (subC _ ne.choose_spec))
      have upper (j) (hj : j ∈ I) : K S ≤ K (C j) + K (E j) + mass (E j) := by
        have full : siblings p e (d + 1) hn (children p (d + 1) j) = C j :=
          (childrenFacts (d + 1) hn j).2.2.2 _ |>.trans (childrenFacts (d + 1) hn j).2.1
        have constant : ∀ c, c ∉ C j → ∃ r, ∀ a ∈ C j, q c a = r := by
          rw [← full]
          apply siblingConstant (d + 1) hn j (children p (d + 1) j)
          · exact Finset.card_pos.mp ((childrenFacts (d + 1) hn j).1.symm ▸
              (Fact.out : p.Prime).pos)
          · exact Finset.Subset.refl _
        obtain ⟨c,next,hT,hc⟩ := rootInside (C j) (bigC j) constant
        obtain ⟨hit,miss⟩ := responses d hd b I valid j hj c hc
        have sp := splice (C j) (E j) (split j hj).1 c d next (best (E j)) hit miss
          (hT ▸ bestIdent (C j)) (bestIdent (E j))
        have bound := bestLe S _ ((split j hj).2 ▸ sp.1)
        have eq := sp.2.2.2
        rw [(split j hj).2, ← hT] at eq
        change cost S (best S) ≤ _
        rw [eq] at bound
        exact bound
      obtain ⟨j,hj,low,_⟩ := lower big
      refine ⟨⟨j,hj,?_⟩,?_⟩
      · have up := upper j hj
        dsimp only [S,C,E] at up low ⊢
        rw [massSplit j hj]
        linarith
      · intro v ⟨j,hj,hv⟩
        rw [hv, massSplit j hj]
        have up := upper j hj
        dsimp only [S,C,E] at up
        linarith
    · constructor
      · intro leaf one
        obtain ⟨j,hj⟩ := Finset.card_eq_one.mp one
        have eq : S = C j := by
          dsimp only [S]
          rw [hj]
          ext a
          simp only [C,siblings,node,Finset.mem_filter,Finset.mem_univ,true_and,
            Finset.mem_singleton]
        apply small
        change S.card ≤ 1
        rw [eq,cards,leaf,Nat.sub_self,pow_zero]
      · intro leaf many
        have singletonC (j) : (C j).card = 1 := by
          rw [cards,leaf,Nat.sub_self,pow_zero]
        have big : 1 < S.card := by
          obtain ⟨j,hj,k,hk,hjk⟩ := Finset.one_lt_card.mp (by omega : 1 < I.card)
          obtain ⟨a,ha⟩ := cne j
          obtain ⟨b,hb⟩ := cne k
          apply Finset.one_lt_card.mpr
          refine ⟨a,subC j hj ha,b,subC k hk hb,?_⟩
          intro hab
          have hpa := (Finset.mem_filter.mp ha).2
          have hpb := (Finset.mem_filter.mp hb).2
          exact hjk (hpa.symm.trans (hab ▸ hpb))
        have upper (j) (hj : j ∈ I) : K S ≤ mass S + K (E j) := by
          obtain ⟨c,hc⟩ := cne j
          obtain ⟨hit,miss⟩ := responses d hd b I valid j hj c hc
          have idC : identifies (C j) (.query c (fun _ => .stop)) :=
            fun a ha b hb _ => (Finset.card_le_one.mp (singletonC j).le) a ha b hb
          have sp := splice (C j) (E j) (split j hj).1 c d (fun _ => .stop)
            (best (E j)) hit miss idC (bestIdent (E j))
          have bound := bestLe S _ ((split j hj).2 ▸ sp.1)
          have eq := sp.2.2.2
          rw [(split j hj).2] at eq
          have cc : cost (C j) (.query c (fun _ => .stop)) = mass (C j) := by
            simp only [cost,mass,runPassiveProtocol,List.length_cons,List.length_nil,
              Nat.zero_add,Nat.cast_one,mul_one]
          rw [cc] at eq
          rw [eq] at bound
          rw [massSplit j hj]
          change cost S (best S) ≤ _
          linarith
        obtain ⟨j,hj,_,low⟩ := lower big
        refine ⟨⟨j,hj,le_antisymm (upper j hj) low⟩,?_⟩
        intro v ⟨k,hk,hv⟩
        exact hv ▸ upper k hk
  have leastPolicy (S : Finset X) (P : List (X × ℕ)) :
      IsLeast (policyCosts q μ S P) (K S) := equalCosts S P ▸ leastTree S
  refine ⟨persist, unique, realizes, family, equalCosts, K, leastPolicy, leastTree,
    small ∅ (by simp only [Finset.card_empty, Nat.zero_le]),
    (fun a => small {a} (by rw [Finset.card_singleton])), ?_, ?_, ?_, recurrence⟩
  · intro he
    rw [roots.1 he]
    exact small {0} (by rw [Finset.card_singleton])
  · intro S P ne
    refine ⟨⟨K S,(leastPolicy S P).1,rfl⟩,?_⟩
    intro v ⟨w,hw,hv⟩
    rw [hv]
    exact (div_le_div_iff_of_pos_right (massPos S ne)).2 ((leastPolicy S P).2 hw)
  · intro d hd j
    congr 1
    ext a
    simp only [siblings,node,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_singleton]

#print axioms residue_first_step_optimality
end D5.S3.Observer.Budget.ResidueFirstStepOptimality
