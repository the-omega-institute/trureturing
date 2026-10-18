/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalProduct
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent network substitution preserves all five terminal partition masses. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing
import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms
import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycleArcs
import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment

/-! Full finite-sum substitution for independent edge families. -/

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct

open SimpleGraph ThreeTerminalBond ThreeTerminalTree ThreeTerminalGluing
open scoped BigOperators
set_option backward.isDefEq.respectTransparency.types false

/-- Detach the third label when the independent connecting network is closed. -/
def detachThird (s : Mode) (b : Bool) : Mode :=
  if b then s else match s with
    | .all | .ab => .ab
    | _ => .separate

private lemma independent_detach {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Mode) (Q : Y → Bool) (w : X → ℝ) (v : Y → ℝ)
    (hv : ∑ y, v y = 1) (s : Mode) :
    let p := fun t => ∑ x, if P x = t then w x else 0
    let q := ∑ y, if Q y then v y else 0
    (∑ x, ∑ y, if detachThird (P x) (Q y) = s then w x * v y else 0) =
      match s with
      | .all => q*p .all
      | .ab => p .ab+(1-q)*p .all
      | .bc => q*p .bc
      | .ac => q*p .ac
      | .separate => p .separate+(1-q)*(p .bc+p .ac) := by
  classical
  dsimp only
  have hfalse : (∑ y, if Q y then 0 else v y) =
      1-(∑ y, if Q y then v y else 0) := by
    have hh : (∑ y, if Q y then v y else 0)+(∑ y, if Q y then 0 else v y) = 1 := by
      rw [← Finset.sum_add_distrib]
      convert hv using 1
      apply Finset.sum_congr rfl
      intro y _
      cases Q y <;> simp
    linarith
  have hsplit (x : X) (y : Y) :
      (if detachThird (P x) (Q y) = s then w x*v y else 0) =
        (if P x = s then w x else 0)*(if Q y then v y else 0)+
        (if detachThird (P x) false = s then w x else 0)*(if Q y then 0 else v y) := by
    cases hQ : Q y <;> simp only [detachThird,hQ,Bool.false_eq_true,ite_false,ite_true]
    all_goals split_ifs <;> ring
  simp_rw [hsplit,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [← Finset.sum_mul,← Finset.sum_mul,hfalse]
  have hlast : (∑ x, if detachThird (P x) false = s then w x else 0) =
      match s with
      | .ab => (∑ x, if P x = .ab then w x else 0)+(∑ x, if P x = .all then w x else 0)
      | .separate => (∑ x, if P x = .separate then w x else 0)+
          (∑ x, if P x = .bc then w x else 0)+(∑ x, if P x = .ac then w x else 0)
      | _ => 0 := by
    cases s <;> simp only [← Finset.sum_add_distrib]
    all_goals first | apply Finset.sum_congr rfl | apply Finset.sum_eq_zero
    all_goals intro x _; cases P x <;> simp [detachThird]
  rw [hlast]
  cases s <;> dsimp only <;> ring

private lemma openGraph_sum {V E F : Type*} (e : E → V × V) (f : F → V × V)
    (ω : E → Bool) (η : F → Bool) :
    openGraph (Sum.elim e f) (Sum.elim ω η) = openGraph e ω ⊔ openGraph f η := by
  ext x y
  simp only [openGraph,SimpleGraph.fromRel_adj,SimpleGraph.sup_adj]
  constructor
  · rintro ⟨hne,h | h⟩
    all_goals obtain ⟨i,hi,he⟩ := h
    all_goals cases i with
      | inl i => exact Or.inl ⟨hne,by aesop⟩
      | inr i => exact Or.inr ⟨hne,by aesop⟩
  · rintro (⟨hne,h | h⟩ | ⟨hne,h | h⟩)
    · obtain ⟨i,hi,he⟩ := h
      exact ⟨hne,Or.inl ⟨Sum.inl i,hi,he⟩⟩
    · obtain ⟨i,hi,he⟩ := h
      exact ⟨hne,Or.inr ⟨Sum.inl i,hi,he⟩⟩
    · obtain ⟨i,hi,he⟩ := h
      exact ⟨hne,Or.inl ⟨Sum.inr i,hi,he⟩⟩
    · obtain ⟨i,hi,he⟩ := h
      exact ⟨hne,Or.inr ⟨Sum.inr i,hi,he⟩⟩

private lemma openGraph_le_full {V E : Type*} (e : E → V × V) (ω : E → Bool) :
    openGraph e ω ≤ openGraph e (fun _ => true) := by
  intro x y h
  simp only [openGraph,SimpleGraph.fromRel_adj] at h ⊢
  aesop

/-- Boolean and propositional readings of the same actual graph partition agree. -/
lemma partition_graphMode {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (e : E → V × V) (a b c : V) (ω : E → Bool) :
    partition e a b c ω = graphMode (openGraph e ω) a b c := by
  classical
  by_cases hab : (openGraph e ω).Reachable a b <;>
    by_cases hbc : (openGraph e ω).Reachable b c <;>
    by_cases hac : (openGraph e ω).Reachable a c <;>
    simp [partition,connected,graphMode,hab,hbc,hac]

/-- The reliability is computed on the complete edge cube of the attached
network, including configurations of edges irrelevant to the connection. -/
def reliability {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (f : F → V × V) (g c : V) (ρ : F → ℝ) : ℝ :=
  ∑ η : F → Bool, if connected f η g c then weight ρ η else 0

/-- Joining two independent edge networks at a single gate transforms all five
partition probabilities together. No strict positivity or distinctness of the
terminals is needed. Both probability laws are finite sums on actual graphs. -/
theorem joined_network_law {V E F : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (e : E → V × V) (f : F → V × V) (A B : Set V) (a b c g : V)
    (h : OneVertexUnion (openGraph e (fun _ => true))
      (openGraph f (fun _ => true)) A B g)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ B)
    (θ : E → ℝ) (ρ : F → ℝ) :
    let p := law e a b g θ
    let q := reliability f g c ρ
    law (Sum.elim e f) a b c (Sum.elim θ ρ) = fun s => match s with
      | .all => q*p .all
      | .ab => p .ab+(1-q)*p .all
      | .bc => q*p .bc
      | .ac => q*p .ac
      | .separate => p .separate+(1-q)*(p .bc+p .ac) := by
  classical
  have hpoint (ω : E → Bool) (η : F → Bool) :
      partition (Sum.elim e f) a b c (Sum.elim ω η) =
        detachThird (partition e a b g ω) (connected f η g c) := by
    rw [partition_graphMode,openGraph_sum]
    have h' : OneVertexUnion (openGraph e ω) (openGraph f η) A B g :=
      ⟨fun {_ _} hxy => h.left_support (openGraph_le_full e ω hxy),
       fun {_ _} hxy => h.right_support (openGraph_le_full f η hxy),h.intersection⟩
    rw [graphMode_pendant h' ha hb hc,partition_graphMode]
    by_cases hgc : (openGraph f η).Reachable g c <;>
      simp only [detachThird,connected,hgc,decide_true,decide_false,ite_true,ite_false,Bool.false_eq_true]
    all_goals cases graphMode (openGraph e ω) a b g <;> rfl
  have hweight (ω : E → Bool) (η : F → Bool) :
      weight (Sum.elim θ ρ) (Sum.elim ω η) = weight θ ω * weight ρ η := by
    simp [weight,Fintype.prod_sum_type]
  funext s
  unfold law
  rw [← (Equiv.sumArrowEquivProdArrow E F Bool).symm.sum_comp,Fintype.sum_prod_type]
  change (∑ ω : E → Bool, ∑ η : F → Bool,
    if partition (Sum.elim e f) a b c (Sum.elim ω η) = s
    then weight (Sum.elim θ ρ) (Sum.elim ω η) else 0) = _
  simp_rw [hpoint,hweight]
  exact independent_detach (partition e a b g) (fun η => connected f η g c)
    (weight θ) (weight ρ) (weight_sum ρ) s

private lemma grouped_mass {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)]
    (w : ∀ i, X i → ℝ) (f : ∀ i, X i → Bool)
    (hw : ∀ i, ∑ x, w i x = 1) (b : I → Bool) :
    (∑ x : ∀ i, X i,
      if (fun i => f i (x i)) = b then ∏ i, w i (x i) else 0) =
    weight (fun i => ∑ x, if f i x then w i x else 0) b := by
  classical
  have hind (x : ∀ i, X i) :
      (if (fun i => f i (x i)) = b then ∏ i, w i (x i) else 0) =
        ∏ i, if f i (x i) = b i then w i (x i) else 0 := by
    by_cases h : (fun i => f i (x i)) = b
    · have hi (i) := congrFun h i
      simp [h,hi]
    · rw [if_neg h]
      obtain ⟨i,hi⟩ : ∃ i, f i (x i) ≠ b i := by
        simpa only [funext_iff,not_forall] using h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  simp_rw [hind]
  rw [← Fintype.prod_sum (fun (i : I) (x : X i) => if f i x = b i then w i x else 0)]
  unfold weight
  apply Finset.prod_congr rfl
  intro i _
  cases hb : b i
  · simp only [Bool.false_eq_true,ite_false]
    have hh : (∑ x, if f i x = false then w i x else 0)+
        (∑ x, if f i x then w i x else 0) = 1 := by
      rw [← Finset.sum_add_distrib]
      convert hw i using 1
      apply Finset.sum_congr rfl
      intro x _
      cases f i x <;> simp
    linarith
  · simp

private lemma grouped_source_mass {I E : Type*} [Fintype I] [DecidableEq I]
    [Fintype E] [DecidableEq E] (label : E → I) (θ : E → ℝ)
    (f : ∀ i, ({e : E // label e = i} → Bool) → Bool) (b : I → Bool) :
    (∑ ω : E → Bool,
      if (fun i => f i (fun e => ω e.val)) = b then weight θ ω else 0) =
    weight (fun i => ∑ η : {e : E // label e = i} → Bool,
      if f i η then weight (fun e => θ e.val) η else 0) b := by
  classical
  let c : (E → Bool) ≃ (∀ i, {e : E // label e = i} → Bool) :=
    Equiv.piCongrFiberwise (f:=label) (fun _ => Equiv.refl _)
  have hweight (ω : E → Bool) :
      weight θ ω = ∏ i, weight (fun e : {e : E // label e = i} => θ e.val)
        (fun e => ω e.val) := by
    unfold weight
    exact (Fintype.prod_fiberwise label (fun e => if ω e then θ e else 1-θ e)).symm
  simp_rw [hweight]
  rw [← c.symm.sum_comp]
  convert grouped_mass (fun i => weight (fun e : {e : E // label e = i} => θ e.val))
    f (fun _ => weight_sum _) b using 1
  apply Finset.sum_congr rfl
  intro x _
  have hc : ∀ i, (fun e : {e : E // label e = i} => c.symm x e.val) = x i := by
    intro i
    exact congrFun (c.apply_symm_apply x) i
  simp only [hc]

private lemma grouped_source_law {I E S : Type*} [Fintype I] [DecidableEq I]
    [Fintype E] [DecidableEq E] [DecidableEq S]
    (label : E → I) (θ : E → ℝ)
    (f : ∀ i, ({e : E // label e = i} → Bool) → Bool)
    (read : (I → Bool) → S) (s : S) :
    (∑ ω : E → Bool,
      if read (fun i => f i (fun e => ω e.val)) = s then weight θ ω else 0) =
    ∑ b : I → Bool, if read b = s then
      weight (fun i => ∑ η : {e : E // label e = i} → Bool,
        if f i η then weight (fun e => θ e.val) η else 0) b else 0 := by
  classical
  calc
    _ = ∑ ω : E → Bool, ∑ b : I → Bool,
        if (fun i => f i (fun e => ω e.val)) = b then
          (if read b = s then weight θ ω else 0) else 0 := by simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : read b = s
      · simp only [h,ite_true]
        exact grouped_source_mass label θ f b
      · simp [h]

/-- Every simple cycle length and every ordered triple of distinct gates has
an actual independent three-arc source law. The stronger determinant invariant
is included because it survives terminal network substitution. -/
theorem cycle_law_and_invariant {n : ℕ} (i j : Fin (n + 3))
    (hi : 0 < i.val) (hij : i.val < j.val) (θ : Fin (n + 3) → ℝ)
    (hθ : ∀ e, θ e ∈ Set.Icc 0 1) :
    ∃ u v r : ℝ, u ∈ Set.Icc 0 1 ∧ v ∈ Set.Icc 0 1 ∧ r ∈ Set.Icc 0 1 ∧
      law (ThreeTerminalCycleArcs.cycleEnds n) 0 i j θ =
        law ThreeTerminalTriangleArms.triangleArmsEnds 0 1 2 ![u,v,r,1,1,1] ∧
      0 ≤ delta (law (ThreeTerminalCycleArcs.cycleEnds n) 0 i j θ) ∧
      delta (law (ThreeTerminalCycleArcs.cycleEnds n) 0 i j θ)+
        law (ThreeTerminalCycleArcs.cycleEnds n) 0 i j θ .all *
          law (ThreeTerminalCycleArcs.cycleEnds n) 0 i j θ .ac ≤
        2*law (ThreeTerminalCycleArcs.cycleEnds n) 0 i j θ .ac := by
  classical
  let label : Fin (n + 3) → Fin 3 := fun e =>
    if e.val < i.val then 0 else if e.val < j.val then 1 else 2
  let f (k : Fin 3) (η : {e : Fin (n + 3) // label e = k} → Bool) : Bool :=
    decide (∀ e, η e = true)
  let q (k : Fin 3) : ℝ :=
    ∑ η : {e : Fin (n + 3) // label e = k} → Bool,
      if f k η then weight (fun e => θ e.val) η else 0
  have hq (k : Fin 3) : q k ∈ Set.Icc (0:ℝ) 1 := by
    have hw (η : {e : Fin (n + 3) // label e = k} → Bool) :
        0 ≤ weight (fun e => θ e.val) η := by
      apply Finset.prod_nonneg
      intro e _
      split_ifs
      · exact (hθ e.val).1
      · exact sub_nonneg.mpr (hθ e.val).2
    constructor
    · apply Finset.sum_nonneg
      intro η _
      split_ifs
      · exact hw η
      · exact le_rfl
    · calc q k ≤ ∑ η : {e : Fin (n + 3) // label e = k} → Bool,
            weight (fun e => θ e.val) η := by
             apply Finset.sum_le_sum
             intro η _
             split_ifs
             · exact le_rfl
             · exact hw η
           _ = 1 := weight_sum _
  have heff (ω : Fin (n + 3) → Bool) :
      (fun k => f k (fun e => ω e.val)) =
        ![ThreeTerminalCycleArcs.arcBit ω 0 i.val,
          ThreeTerminalCycleArcs.arcBit ω i.val j.val,
          ThreeTerminalCycleArcs.arcBit ω j.val (n + 3)] := by
    funext k
    have hlabel (e : Fin (n + 3)) :
        label e = k ↔ e ∈ (![ThreeTerminalCycleArcs.arcSupport n 0 i.val,
          ThreeTerminalCycleArcs.arcSupport n i.val j.val,
          ThreeTerminalCycleArcs.arcSupport n j.val (n + 3)] :
          Fin 3 → Finset (Fin (n + 3))) k := by
      fin_cases k <;> dsimp [label] <;>
        simp only [ThreeTerminalCycleArcs.arcSupport,Finset.mem_filter,Finset.mem_univ,true_and]
      all_goals split_ifs <;> simp_all <;> omega
    fin_cases k <;> dsimp [f,ThreeTerminalCycleArcs.arcBit]
    all_goals congr 1
    all_goals simp only [Subtype.forall]
    all_goals apply propext
    all_goals constructor
    all_goals intro h e he
    all_goals first
      | exact h e ((hlabel e).mpr (by simpa using he))
      | exact h e (by simpa using (hlabel e).mp he)
  let read (b : Fin 3 → Bool) := partition ThreeTerminalTriangleArms.triangleArmsEnds 0 1 2
    ![b 0,b 1,b 2,true,true,true]
  have hpart (ω : Fin (n + 3) → Bool) :
      partition (ThreeTerminalCycleArcs.cycleEnds n) 0 i j ω =
        read (fun k => f k (fun e => ω e.val)) := by
    rw [partition_graphMode,ThreeTerminalCycleArcs.cycle_partition ω i j hi hij,heff]
    rfl
  have hcore (s : Mode) :
      (∑ b : Fin 3 → Bool, if read b = s then weight q b else 0) =
        law ThreeTerminalTriangleArms.triangleArmsEnds 0 1 2 ![q 0,q 1,q 2,1,1,1] s := by
    rw [ThreeTerminalTriangleArms.triangle_arms_law]
    simp only [read,ThreeTerminalCycleArcs.core_partition]
    simp only [sum_cube_succ,Fintype.sum_bool]
    simp only [cons_three_last,cons_three_mid,cons_two_last,Fin.cons_zero]
    cases s <;> simp [weight,Fin.prod_univ_succ] <;> ring
  have hp : law (ThreeTerminalCycleArcs.cycleEnds n) 0 i j θ =
      law ThreeTerminalTriangleArms.triangleArmsEnds 0 1 2 ![q 0,q 1,q 2,1,1,1] := by
    funext s
    unfold law
    simp_rw [hpart]
    change _ = law ThreeTerminalTriangleArms.triangleArmsEnds 0 1 2
      ![q 0,q 1,q 2,1,1,1] s
    rw [grouped_source_law label θ f read s]
    exact hcore s
  refine ⟨q 0,q 1,q 2,hq 0,hq 1,hq 2,hp,?_,?_⟩
  · rw [hp]
    exact (ThreeTerminalTriangleArms.triangle_arms_bound _ _ _ _ _ _
      (hq 0) (hq 1) (hq 2) (by norm_num) (by norm_num) (by norm_num)).1
  · rw [hp]
    have hid :
        delta (law ThreeTerminalTriangleArms.triangleArmsEnds 0 1 2 ![q 0,q 1,q 2,1,1,1])+
          law ThreeTerminalTriangleArms.triangleArmsEnds 0 1 2 ![q 0,q 1,q 2,1,1,1] .all *
          law ThreeTerminalTriangleArms.triangleArmsEnds 0 1 2 ![q 0,q 1,q 2,1,1,1] .ac =
        (q 0+q 1-q 0*q 1*q 2)*
          law ThreeTerminalTriangleArms.triangleArmsEnds 0 1 2 ![q 0,q 1,q 2,1,1,1] .ac := by
      rw [ThreeTerminalTriangleArms.triangle_arms_law]
      dsimp [delta]
      ring
    rw [hid]
    have hc : q 0+q 1-q 0*q 1*q 2 ≤ 2 := by
      nlinarith [(hq 0).2,(hq 1).2,mul_nonneg (mul_nonneg (hq 0).1 (hq 1).1) (hq 2).1]
    have hz : 0 ≤ law ThreeTerminalTriangleArms.triangleArmsEnds 0 1 2
        ![q 0,q 1,q 2,1,1,1] .ac := by
      rw [ThreeTerminalTriangleArms.triangle_arms_law]
      dsimp
      have he : q 2+(1-q 2)*q 0*q 1-
          (q 0*q 1+q 0*q 2+q 1*q 2-2*q 0*q 1*q 2) =
          q 2*(1-q 0)*(1-q 1) := by ring
      nlinarith [mul_nonneg (mul_nonneg (hq 2).1 (sub_nonneg.mpr (hq 0).2))
        (sub_nonneg.mpr (hq 1).2)]
    exact mul_le_mul_of_nonneg_right hc hz

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.joined_network_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joined_network_law

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.cycle_law_and_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cycle_law_and_invariant


open SimpleGraph ThreeTerminalBond ThreeTerminalTree ThreeTerminalGluing
open ThreeTerminalProduct ThreeTerminalAttachment
open scoped BigOperators
set_option backward.isDefEq.respectTransparency.types false

/-- The three terminals of the main network, after replacing the attached label by its gate. -/
def gateTerminals {V : Type*} (port : Port) (a b c g : V) : V × V × V :=
  match port with
  | .a => (g,b,c)
  | .b => (a,g,c)
  | .c => (a,b,g)

/-- The actual terminal at the far end of the attached network. -/
def outerTerminal {V : Type*} (port : Port) (a b c : V) : V :=
  match port with
  | .a => a
  | .b => b
  | .c => c

/-- The other two terminals are in the main network and the attached terminal is in the other side. -/
def Supported {V : Type*} (port : Port) (A B : Set V) (a b c : V) : Prop :=
  match port with
  | .a => b ∈ A ∧ c ∈ A ∧ a ∈ B
  | .b => a ∈ A ∧ c ∈ A ∧ b ∈ B
  | .c => a ∈ A ∧ b ∈ A ∧ c ∈ B

noncomputable section

local instance classical_decidable (P : Prop) : Decidable P := Classical.propDecidable P

private lemma graphMode_attach {V : Type*} {H K : SimpleGraph V} {A B : Set V}
    {a b c g : V} (h : OneVertexUnion H K A B g) (port : Port)
    (hs : Supported port A B a b c) :
    graphMode (H ⊔ K) a b c =
      detach port (graphMode H (gateTerminals port a b c g).1
        (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2)
        (decide (K.Reachable g (outerTerminal port a b c))) := by
  classical
  cases port with
  | c =>
    obtain ⟨ha,hb,hc⟩ := hs
    rw [graphMode_pendant h ha hb hc]
    by_cases hr : K.Reachable g c <;>
      simp only [gateTerminals,outerTerminal,detach,hr,decide_true,decide_false,
        ite_true,ite_false,Bool.false_eq_true]
    all_goals cases graphMode H a b g <;> rfl
  | a =>
    obtain ⟨hb,hc,ha⟩ := hs
    obtain ⟨hbc,hba,hca⟩ := simultaneous_reachability h hb hc ha
    have hab : (H ⊔ K).Reachable a b ↔ H.Reachable g b ∧ K.Reachable g a := by
      simpa only [@reachable_comm _ (H ⊔ K) a b,@reachable_comm _ H g b] using hba
    have hac : (H ⊔ K).Reachable a c ↔ H.Reachable g c ∧ K.Reachable g a := by
      simpa only [@reachable_comm _ (H ⊔ K) a c,@reachable_comm _ H g c] using hca
    by_cases hr : K.Reachable g a
    · simp only [graphMode,hab,hbc,hac,hr,and_true,gateTerminals,outerTerminal,
        detach,decide_true,ite_true]
      by_cases hgb : H.Reachable g b <;> by_cases hbc : H.Reachable b c <;>
        by_cases hgc : H.Reachable g c <;> simp [hgb,hbc,hgc]
    · simp only [graphMode,hab,hbc,hac,hr,and_false,gateTerminals,outerTerminal,
        detach,decide_false,ite_false,Bool.false_eq_true]
      by_cases hgb : H.Reachable g b <;> by_cases hbc : H.Reachable b c <;>
        by_cases hgc : H.Reachable g c <;> simp [hgb,hbc,hgc]
  | b =>
    obtain ⟨ha,hc,hb⟩ := hs
    obtain ⟨hac,hab,hcb⟩ := simultaneous_reachability h ha hc hb
    have hbc : (H ⊔ K).Reachable b c ↔ H.Reachable g c ∧ K.Reachable g b := by
      simpa only [@reachable_comm _ (H ⊔ K) b c,@reachable_comm _ H g c] using hcb
    by_cases hr : K.Reachable g b
    · simp only [graphMode,hab,hbc,hac,hr,and_true,gateTerminals,outerTerminal,
        detach,decide_true,ite_true]
      by_cases hag : H.Reachable a g <;> by_cases hgc : H.Reachable g c <;>
        by_cases hac : H.Reachable a c <;> simp [hag,hgc,hac]
    · simp only [graphMode,hab,hbc,hac,hr,and_false,gateTerminals,outerTerminal,
        detach,decide_false,ite_false,Bool.false_eq_true]
      by_cases hag : H.Reachable a g <;> by_cases hgc : H.Reachable g c <;>
        by_cases hac : H.Reachable a c <;> simp [hag,hgc,hac]
      · exact False.elim (hac (hag.trans hgc))
      · exact False.elim (hgc (hag.symm.trans hac))
      · exact False.elim (hag (hac.trans hgc.symm))

private lemma product_pushforward {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Mode) (Q : Y → Bool) (w : X → ℝ) (v : Y → ℝ)
    (hv : ∑ y, v y = 1) (port : Port) (s : Mode) :
    (∑ x, ∑ y, if detach port (P x) (Q y) = s then w x*v y else 0) =
      transfer port (fun t => ∑ x, if P x = t then w x else 0)
        (∑ y, if Q y then v y else 0) s := by
  classical
  have hbool (b : Bool) : (∑ y, if Q y = b then v y else 0) =
      if b then (∑ y, if Q y then v y else 0) else
        1-(∑ y, if Q y then v y else 0) := by
    cases b
    · have hh : (∑ y, if Q y = false then v y else 0)+
          (∑ y, if Q y then v y else 0) = 1 := by
        rw [← Finset.sum_add_distrib]
        convert hv using 1
        apply Finset.sum_congr rfl
        intro y _
        cases Q y <;> simp
      simp only [Bool.false_eq_true,ite_false]
      linarith
    · simp
  unfold transfer
  simp_rw [← hbool]
  calc
    _ = ∑ x, ∑ y, ∑ t : Mode, ∑ bit : Bool,
        if detach port t bit = s then
          (if P x = t then w x else 0)*(if Q y = bit then v y else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      have henum : (Finset.univ : Finset Mode) = {.separate,.ab,.bc,.all,.ac} := by decide
      cases P x <;> cases Q y <;> simp [henum]
    _ = ∑ x, ∑ t : Mode, ∑ y, ∑ bit : Bool,
        if detach port t bit = s then
          (if P x = t then w x else 0)*(if Q y = bit then v y else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ t : Mode, ∑ x, ∑ y, ∑ bit : Bool,
        if detach port t bit = s then
          (if P x = t then w x else 0)*(if Q y = bit then v y else 0) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t : Mode, ∑ x, ∑ bit : Bool, ∑ y,
        if detach port t bit = s then
          (if P x = t then w x else 0)*(if Q y = bit then v y else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ t : Mode, ∑ bit : Bool, ∑ x, ∑ y,
        if detach port t bit = s then
          (if P x = t then w x else 0)*(if Q y = bit then v y else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro bit _
      by_cases hd : detach port t bit = s
      · simp only [hd,ite_true]
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
      · simp only [hd,ite_false,Finset.sum_const_zero]


/-- The complete actual graph source under single-gate substitution, at any labelled terminal. -/
theorem joined_network_transfer {V E F : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (e : E → V × V) (f : F → V × V) (A B : Set V) (a b c g : V)
    (h : OneVertexUnion (openGraph e (fun _ => true))
      (openGraph f (fun _ => true)) A B g) (port : Port)
    (hs : Supported port A B a b c) (θ : E → ℝ) (ρ : F → ℝ) :
    law (Sum.elim e f) a b c (Sum.elim θ ρ) =
      transfer port (law e (gateTerminals port a b c g).1
        (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ)
        (reliability f g (outerTerminal port a b c) ρ) := by
  classical
  by_cases hport : port = .c
  · subst port
    obtain ⟨ha,hb,hc⟩ := hs
    rw [joined_network_law e f A B a b c g h ha hb hc θ ρ]
    dsimp only [gateTerminals,outerTerminal]
    have henum : (Finset.univ : Finset Mode) = {.separate,.ab,.bc,.all,.ac} := by decide
    funext s
    cases s <;> simp [transfer,detach,henum] <;> ring
  have hpoint (ω : E → Bool) (η : F → Bool) :
      partition (Sum.elim e f) a b c (Sum.elim ω η) =
        detach port (partition e (gateTerminals port a b c g).1
          (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 ω)
          (connected f η g (outerTerminal port a b c)) := by
    rw [partition_graphMode,ThreeTerminalProduct.openGraph_sum]
    have h' : OneVertexUnion (openGraph e ω) (openGraph f η) A B g :=
      ⟨fun {_ _} hxy => h.left_support (ThreeTerminalProduct.openGraph_le_full e ω hxy),
       fun {_ _} hxy => h.right_support (ThreeTerminalProduct.openGraph_le_full f η hxy),
       h.intersection⟩
    rw [graphMode_attach h' port hs,partition_graphMode]
    by_cases hgc : (openGraph f η).Reachable g (outerTerminal port a b c) <;>
      simp [connected,hgc]
  funext s
  unfold law
  rw [← (Equiv.sumArrowEquivProdArrow E F Bool).symm.sum_comp,Fintype.sum_prod_type]
  change (∑ ω : E → Bool, ∑ η : F → Bool,
    if partition (Sum.elim e f) a b c (Sum.elim ω η) = s
      then weight (Sum.elim θ ρ) (Sum.elim ω η) else 0) = _
  have hw (ω : E → Bool) (η : F → Bool) :
      weight (Sum.elim θ ρ) (Sum.elim ω η) = weight θ ω*weight ρ η := by
    simp [weight,Fintype.prod_sum_type]
  simp_rw [hpoint,hw]
  exact product_pushforward _ _ (weight θ) (weight ρ) (weight_sum ρ) port s



/-- A network attached at one gate is invisible to all five partition events
when all three terminals remain in the other side. -/
theorem joined_network_ignored {V E F : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (e : E → V × V) (f : F → V × V) (A B : Set V) (a b c g : V)
    (h : OneVertexUnion (openGraph e (fun _ => true))
      (openGraph f (fun _ => true)) A B g)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hg : g ∈ B)
    (θ : E → ℝ) (ρ : F → ℝ) :
    law (Sum.elim e f) a b c (Sum.elim θ ρ) = law e a b c θ := by
  classical
  have hpoint (ω : E → Bool) (η : F → Bool) :
      partition (Sum.elim e f) a b c (Sum.elim ω η) = partition e a b c ω := by
    rw [partition_graphMode,openGraph_sum,partition_graphMode]
    have h' : OneVertexUnion (openGraph e ω) (openGraph f η) A B g :=
      ⟨fun {_ _} hxy => h.left_support (openGraph_le_full e ω hxy),
       fun {_ _} hxy => h.right_support (openGraph_le_full f η hxy),h.intersection⟩
    have hab := (simultaneous_reachability h' ha hb hg).1
    have hbc := (simultaneous_reachability h' hb hc hg).1
    have hac := (simultaneous_reachability h' ha hc hg).1
    by_cases hp : (openGraph e ω).Reachable a b <;>
      by_cases hq : (openGraph e ω).Reachable b c <;>
      by_cases hr : (openGraph e ω).Reachable a c <;> simp [graphMode,hab,hbc,hac,hp,hq,hr]
  funext s
  unfold law
  rw [← (Equiv.sumArrowEquivProdArrow E F Bool).symm.sum_comp,Fintype.sum_prod_type]
  change (∑ ω : E → Bool, ∑ η : F → Bool,
    if partition (Sum.elim e f) a b c (Sum.elim ω η) = s
      then weight (Sum.elim θ ρ) (Sum.elim ω η) else 0) = _
  have hw (ω : E → Bool) (η : F → Bool) :
      weight (Sum.elim θ ρ) (Sum.elim ω η) = weight θ ω*weight ρ η := by
    simp [weight,Fintype.prod_sum_type]
  simp_rw [hpoint,hw]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs
  · rw [← Finset.mul_sum]
    change weight θ ω*(∑ η : F → Bool, weight ρ η) = weight θ ω
    rw [weight_sum,mul_one]
  · simp

/-- An absolute graph-source determinant bound is preserved by an actual independent
network substituted at any one of the three marked vertices. -/
theorem joined_network_signed_invariant {V E F : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (e : E → V × V) (f : F → V × V) (A B : Set V) (a b c g : V)
    (h : OneVertexUnion (openGraph e (fun _ => true))
      (openGraph f (fun _ => true)) A B g) (port : Port)
    (hs : Supported port A B a b c) (θ : E → ℝ) (ρ : F → ℝ)
    (hθ : ∀ i, θ i ∈ Set.Icc 0 1) (hρ : ∀ i, ρ i ∈ Set.Icc 0 1)
    (C : ℝ) (hC : 1 ≤ C)
    (hbound : |delta (law e (gateTerminals port a b c g).1
      (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ)|+
      law e (gateTerminals port a b c g).1
        (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ .all *
      law e (gateTerminals port a b c g).1
        (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ .ac ≤
      C*law e (gateTerminals port a b c g).1
        (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ .ac) :
    |delta (law (Sum.elim e f) a b c (Sum.elim θ ρ))|+
        law (Sum.elim e f) a b c (Sum.elim θ ρ) .all *
        law (Sum.elim e f) a b c (Sum.elim θ ρ) .ac ≤
      C*law (Sum.elim e f) a b c (Sum.elim θ ρ) .ac := by
  classical
  have hprob := law_probability e (gateTerminals port a b c g).1
    (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ hθ
  have hw (η : F → Bool) : 0 ≤ weight ρ η := by
    apply Finset.prod_nonneg
    intro i _
    split_ifs
    · exact (hρ i).1
    · exact sub_nonneg.mpr (hρ i).2
  have hq : reliability f g (outerTerminal port a b c) ρ ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · apply Finset.sum_nonneg
      intro η _
      split_ifs
      · exact hw η
      · exact le_rfl
    · calc
        _ ≤ ∑ η : F → Bool, weight ρ η := by
          apply Finset.sum_le_sum
          intro η _
          split_ifs
          · exact le_rfl
          · exact hw η
        _ = 1 := weight_sum ρ
  rw [joined_network_transfer e f A B a b c g h port hs θ ρ]
  exact attachment_signed_invariant _ hprob.1 hprob.2 C hC _ hq hbound port

/-- A graph-source determinant bound is preserved by an actual independent
network substituted at any one of the three marked vertices. -/
theorem joined_network_invariant {V E F : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (e : E → V × V) (f : F → V × V) (A B : Set V) (a b c g : V)
    (h : OneVertexUnion (openGraph e (fun _ => true))
      (openGraph f (fun _ => true)) A B g) (port : Port)
    (hs : Supported port A B a b c) (θ : E → ℝ) (ρ : F → ℝ)
    (hθ : ∀ i, θ i ∈ Set.Icc 0 1) (hρ : ∀ i, ρ i ∈ Set.Icc 0 1)
    (C : ℝ) (hC : 1 ≤ C)
    (hlow : 0 ≤ delta (law e (gateTerminals port a b c g).1
      (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ))
    (hbound : delta (law e (gateTerminals port a b c g).1
      (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ)+
      law e (gateTerminals port a b c g).1
        (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ .all *
      law e (gateTerminals port a b c g).1
        (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ .ac ≤
      C*law e (gateTerminals port a b c g).1
        (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ .ac) :
    0 ≤ delta (law (Sum.elim e f) a b c (Sum.elim θ ρ)) ∧
      delta (law (Sum.elim e f) a b c (Sum.elim θ ρ))+
        law (Sum.elim e f) a b c (Sum.elim θ ρ) .all *
        law (Sum.elim e f) a b c (Sum.elim θ ρ) .ac ≤
      C*law (Sum.elim e f) a b c (Sum.elim θ ρ) .ac := by
  classical
  have hprob := law_probability e (gateTerminals port a b c g).1
    (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ hθ
  have hw (η : F → Bool) : 0 ≤ weight ρ η := by
    apply Finset.prod_nonneg
    intro i _
    split_ifs
    · exact (hρ i).1
    · exact sub_nonneg.mpr (hρ i).2
  have hq : reliability f g (outerTerminal port a b c) ρ ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · apply Finset.sum_nonneg
      intro η _
      split_ifs
      · exact hw η
      · exact le_rfl
    · calc
        _ ≤ ∑ η : F → Bool, weight ρ η := by
          apply Finset.sum_le_sum
          intro η _
          split_ifs
          · exact le_rfl
          · exact hw η
        _ = 1 := weight_sum ρ
  have hsigned : |delta (law e (gateTerminals port a b c g).1
      (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ)|+
      law e (gateTerminals port a b c g).1
        (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ .all *
      law e (gateTerminals port a b c g).1
        (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ .ac ≤
      C*law e (gateTerminals port a b c g).1
        (gateTerminals port a b c g).2.1 (gateTerminals port a b c g).2.2 θ .ac := by
    simpa only [abs_of_nonneg hlow] using hbound
  have hjoined := joined_network_signed_invariant e f A B a b c g h port hs
    θ ρ hθ hρ C hC hsigned
  constructor
  · rw [joined_network_transfer e f A B a b c g h port hs θ ρ]
    exact (attachment_invariant _ hprob.1 hprob.2 C hC _ hq hlow hbound port).1
  · exact le_trans (add_le_add (le_abs_self _) le_rfl) hjoined

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.joined_network_signed_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joined_network_signed_invariant

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.joined_network_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joined_network_transfer

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.joined_network_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joined_network_invariant

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct.joined_network_ignored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joined_network_ignored

end
end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct
