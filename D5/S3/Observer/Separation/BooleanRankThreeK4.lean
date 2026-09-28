/- GID: D5/S3/Observer/Separation/BooleanRankThreeK4
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/BooleanRankThreeK4
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Observer/Separation/BooleanRankThreeK4.claim; result=D5/S3/Observer/Separation/BooleanRankThreeK4.result; claim=D5/S3/Observer/Separation/BooleanRankThreeK4.claim
   digest: An actual Boolean rank-three K4 subdivision refutes the four-path reduction. -/

import D5.S3.Observer.Separation.BooleanRankFour
import D5.S3.Observer.Separation.BooleanRankThreeFiber
import D5.S3.Observer.Separation.ThreeLeafCausalPeak
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Separation.BooleanRankThreeK4
open BooleanRankFour
open D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace

abbrev V := Fin 8 ⊕ Fin 6
instance : DecidableEq V := inferInstance
abbrev x (i : Fin 8) : V := .inl i
abbrev y (j : Fin 6) : V := .inr j

def table : Task (Fin 8) (Fin 6) :=
  ![![some false, some false, none, none, none, none],
    ![none, none, some true, some true, none, none],
    ![some true, none, none, none, some false, none],
    ![none, none, some true, none, some false, none],
    ![none, some false, none, none, none, some true],
    ![none, none, none, some false, none, some true],
    ![some false, none, none, some true, none, none],
    ![none, some true, some false, none, none, none]]

abbrev G := support table
instance : DecidableRel G.Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [G, support] <;> infer_instance

def legalPairs : Fin 16 → Fin 8 × Fin 6 :=
  ![(0,0),(0,1),(1,2),(1,3),(2,0),(2,4),(3,2),(3,4),
    (4,1),(4,5),(5,3),(5,5),(6,0),(6,3),(7,1),(7,2)]
def edge (i : Fin 16) : Sym2 V := s(x (legalPairs i).1, y (legalPairs i).2)
def incident (v : V) (i : Fin 16) : Bool :=
  decide (v = x (legalPairs i).1 ∨ v = y (legalPairs i).2)
def bit (i : Fin 16) : Bool := (table (legalPairs i).1 (legalPairs i).2).getD false

/-- The binary cycle space in its even-incidence edge-coordinate definition. -/
def CycleVector (z : Fin 16 → Bool) : Prop :=
  ∀ v : V, ((List.ofFn fun i : Fin 16 => z i && incident v i).foldr Bool.xor false) = false

def oddParity (z : Fin 16 → Bool) : Bool :=
  (List.ofFn fun i : Fin 16 => z i && bit i).foldr Bool.xor false

def encode (t : Bool × Bool × Bool) : Fin 16 → Bool :=
  let a := t.1; let b := t.2.1; let d := t.2.2
  ![a,a,b ^^ d,b ^^ d,b,b,b,b,a ^^ d,a ^^ d,a ^^ d,a ^^ d,a ^^ b,a ^^ b,d,d]

def branches : Finset V := {y 0,y 1,y 2,y 3}
def ends : Fin 6 → V × V := ![(y 0,y 1),(y 0,y 2),(y 0,y 3),
  (y 1,y 2),(y 1,y 3),(y 2,y 3)]
def paths : Fin 6 → List V :=
  ![[y 0,x 0,y 1], [y 0,x 2,y 4,x 3,y 2], [y 0,x 6,y 3],
    [y 1,x 7,y 2], [y 1,x 4,y 5,x 5,y 3], [y 2,x 1,y 3]]
def pathWalk (i : Fin 6) : G.Walk (ends i).1 (ends i).2 :=
  (SimpleGraph.Walk.ofSupport (paths i)
    (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)).copy
    (by fin_cases i <;> rfl) (by fin_cases i <;> rfl)
def internal (i : Fin 6) : List V := (paths i).tail.dropLast

def cycleStart : Fin 4 → V := ![x 0,x 0,x 1,x 1]
def cycles : Fin 4 → List V :=
  ![[x 0,y 0,x 2,y 4,x 3,y 2,x 7,y 1,x 0],
    [x 0,y 0,x 6,y 3,x 5,y 5,x 4,y 1,x 0],
    [x 1,y 2,x 3,y 4,x 2,y 0,x 6,y 3,x 1],
    [x 1,y 2,x 7,y 1,x 4,y 5,x 5,y 3,x 1]]
def cycleWalk (i : Fin 4) : G.Walk (cycleStart i) (cycleStart i) :=
  (SimpleGraph.Walk.ofSupport (cycles i)
    (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)).copy
    (by fin_cases i <;> rfl) (by fin_cases i <;> rfl)
def cycleVector (i : Fin 4) (e : Fin 16) : Bool :=
  decide (edge e ∈ (cycleWalk i).edges)

/-- These predicates always inspect the original table, never a residual table. -/
def monoX (c : Bool) (i : Fin 8) : Prop :=
  ∀ j b, table i j = some b → b = c
def monoY (c : Bool) (j : Fin 6) : Prop :=
  ∀ i b, table i j = some b → b = c
def survives (c d : Bool) : V → Prop
  | .inl i => ¬ monoX c i
  | .inr j => ¬ monoY d j
def residualCycle (c d : Bool) : Fin 4 :=
  if c then (if d then 0 else 1) else (if d then 2 else 3)

def bit2 (b : Bool) : ZMod 2 := if b then 1 else 0
def mappedTask : BooleanRankThreeFiber.Task (Fin 8) (Fin 6) := ⟨fun i j => (table i j).map bit2⟩

instance : DecidableRel (BooleanRankThreeFiber.support mappedTask).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [BooleanRankThreeFiber.support] <;> infer_instance
instance (c d : Bool) : DecidableRel (BooleanRankThreeFiber.residual mappedTask (bit2 c) (bit2 d)).Adj := by
  intro a b
  dsimp [BooleanRankThreeFiber.residual]
  cases a <;> cases b <;> dsimp [BooleanRankThreeFiber.monoLeft, BooleanRankThreeFiber.monoRight] <;> infer_instance

def residualWalk (c d : Bool) :
    (BooleanRankThreeFiber.residual mappedTask (bit2 c) (bit2 d)).Walk
      (cycleStart (residualCycle c d)) (cycleStart (residualCycle c d)) :=
  (SimpleGraph.Walk.ofSupport (cycles (residualCycle c d))
    (by cases c <;> cases d <;> decide)
    (by cases c <;> cases d <;> decide)).copy
    (by cases c <;> cases d <;> rfl) (by cases c <;> cases d <;> rfl)

abbrev Legal := {p : Fin 8 × Fin 6 // (table p.1 p.2).isSome = true}
def leftInput (w : Legal) : Fin 8 := w.val.1
def rightInput (w : Legal) : Fin 6 := w.val.2
def output (w : Legal) : Bool := (table w.val.1 w.val.2).getD false

def alpha : Fin 8 → Fin 3 := ![0,0,1,0,1,1,0,2]
def beta : Fin 6 → Fin 3 := ![0,1,2,2,1,0]
def decoder : Fin 3 → Fin 3 → Bool :=
  ![![false,false,true],![true,false,false],![false,true,false]]
def alphaNat (i : Fin 8) : ℕ := (alpha i).val
def betaNat (j : Fin 6) : ℕ := (beta j).val
def decoderNat (a b : ℕ) : Bool :=
  if ha : a < 3 then if hb : b < 3 then decoder ⟨a,ha⟩ ⟨b,hb⟩ else false else false

/-- Full actual-task positive certificate; the cycle space is on the certified
bijective enumeration of the original legal edges. -/
def Certificate : Prop :=
  ActiveConnected table ∧ cycleRank table = 3 ∧
  Nat.card {p : Fin 8 × Fin 6 // (table p.1 p.2).isSome = true} = 16 ∧
  Nat.card V = 14 ∧
  (leftConflict table).chromaticNumber = 2 ∧
  (rightConflict table).chromaticNumber = 2 ∧
  Function.Injective legalPairs ∧
  (∀ i j, (table i j).isSome = true ↔ ∃ e, legalPairs e = (i,j)) ∧
  (∀ c i, monoX c i ↔ i = if c then 1 else 0) ∧
  (∀ c j, monoY c j ↔ j = if c then 5 else 4) ∧
  branches.card = 4 ∧
  (∀ v, G.degree v = if v ∈ branches then 3 else 2) ∧
  (∀ i, (pathWalk i).IsPath ∧ (pathWalk i).support = paths i) ∧
  (∀ i v, v ∈ internal i → v ∉ branches) ∧
  (∀ i j, i ≠ j → List.Disjoint (internal i) (internal j)) ∧
  (∀ u ∈ branches, ∀ v ∈ branches, u ≠ v →
    ∃ i, ends i = (u,v) ∨ ends i = (v,u)) ∧
  (∀ u v, G.Adj u v ↔ ∃ i, s(u,v) ∈ (pathWalk i).edges) ∧
  (∀ v, ∃ i, v ∈ (pathWalk i).support) ∧
  (∀ i, (cycleWalk i).IsCycle ∧ CycleVector (cycleVector i) ∧
    oddParity (cycleVector i) = true) ∧
  (∀ c d v, v ∈ (cycleWalk (residualCycle c d)).support → survives c d v) ∧
  (∀ z, CycleVector z ↔ z = encode (z 0,z 4,z 14)) ∧
  Nat.card {z : Fin 16 → Bool // CycleVector z} = 8 ∧
  (∀ z, CycleVector z → (oddParity z = true ↔ ∃ i, z = cycleVector i)) ∧
  Nat.card {z : Fin 16 → Bool // CycleVector z ∧ oddParity z = true} = 4 ∧
  Nat.card (Set.range alphaNat) = 3 ∧ Nat.card (Set.range betaNat) = 3 ∧
  (∀ i j c, table i j = some c → decoderNat (alphaNat i) (betaNat j) = c) ∧
  Admits table 3 3 ∧
  ThreeLeafCausalPeak.cutCost output leftInput rightInput = 2 ∧
  ThreeLeafCausalPeak.cutCost output rightInput leftInput = 2 ∧
  (∀ e, cycleVector 0 e ^^ cycleVector 1 e ^^ cycleVector 2 e ^^ cycleVector 3 e = false) ∧
    (∀ z, CycleVector z → z = fun e =>
      (z 0 && cycleVector 1 e) ^^ (z 4 && cycleVector 2 e) ^^
        (z 14 && cycleVector 3 e)) ∧
    (∀ a b d : Bool,
      (fun e => (a && cycleVector 1 e) ^^ (b && cycleVector 2 e) ^^
        (d && cycleVector 3 e)) = (fun _ => false) ↔
        a = false ∧ b = false ∧ d = false) ∧
    (∀ a b d, CycleVector (encode (a,b,d)) ∧
      oddParity (encode (a,b,d)) = (a ^^ b ^^ d)) ∧
  Function.Bijective bit2 ∧
    (∀ a b, bit2 (a ^^ b) = bit2 a + bit2 b) ∧
    (∀ i j b, mappedTask.table i j = some (bit2 b) ↔ table i j = some b) ∧
    (∀ a b, (BooleanRankThreeFiber.support mappedTask).Adj a b ↔ G.Adj a b) ∧
    (∀ c i, BooleanRankThreeFiber.monoLeft mappedTask (bit2 c) i ↔ monoX c i) ∧
    (∀ d j, BooleanRankThreeFiber.monoRight mappedTask (bit2 d) j ↔ monoY d j) ∧
    (∀ c d a b, (BooleanRankThreeFiber.residual mappedTask (bit2 c) (bit2 d)).Adj a b ↔
      G.Adj a b ∧ survives c d a ∧ survives c d b) ∧
    (∀ e, BooleanRankThreeFiber.label mappedTask (edge e) = bit2 (bit e)) ∧
    (∀ c d, (residualWalk c d).support = cycles (residualCycle c d) ∧
      (residualWalk c d).edges = (cycleWalk (residualCycle c d)).edges ∧
      (residualWalk c d).IsCycle ∧
      walkParity (fun e => BooleanRankThreeFiber.label mappedTask e.val) (residualWalk c d) = 1) ∧
    (∀ c d, walkParity (fun e => BooleanRankThreeFiber.label mappedTask e.val) (residualWalk c d) =
      bit2 (oddParity (cycleVector (residualCycle c d)))) ∧
    (∀ c d, ¬ BooleanRankThreeFiber.Balanced mappedTask (BooleanRankThreeFiber.residual mappedTask (bit2 c) (bit2 d))) ∧
    (∀ c d : ZMod 2, ¬ BooleanRankThreeFiber.Balanced mappedTask (BooleanRankThreeFiber.residual mappedTask c d))

/-- Only the necessary degree consequence of a full four-path subdivision.
This is explicitly not a definition of the full subdivision property. -/
def FourPathDegreeConsequence : Prop :=
  ∃ u v : V, u ≠ v ∧ G.degree u = 4 ∧ G.degree v = 4 ∧
    ∀ w, w ≠ u → w ≠ v → G.degree w = 2

def claim : Prop := Certificate → FourPathDegreeConsequence

/-- A negated implication retains the entire positive certificate and refutes
its proposed necessary four-path degree consequence on the same actual task. -/
theorem result : Not claim := by
  have classification (z : Fin 16 → Bool) :
      CycleVector z ↔ z = encode (z 0,z 4,z 14) := by
    simp only [CycleVector, Sum.forall, Fin.forall_fin_succ]
    simp [incident, legalPairs, List.ofFn_succ, encode, funext_iff,
      Fin.forall_fin_succ]
    generalize z 0 = a0, z 1 = a1, z 2 = a2, z 3 = a3,
      z 4 = a4, z 5 = a5, z 6 = a6, z 7 = a7,
      z 8 = a8, z 9 = a9, z 10 = a10, z 11 = a11,
      z 12 = a12, z 13 = a13, z 14 = a14, z 15 = a15
    cases a0 <;> cases a4 <;> cases a14 <;> simp_all
    all_goals constructor <;> intro h <;> rcases h with ⟨h1,hrest⟩ <;> simp_all
    all_goals aesop
  have encoded : ∀ t, CycleVector (encode t) := by
    intro t
    rw [classification]
    rfl
  have injective : Function.Injective encode := by
    intro a b h
    have h0 := congrFun h 0
    have h4 := congrFun h 4
    have h14 := congrFun h 14
    exact Prod.ext h0 (Prod.ext h4 h14)
  have allCard : Nat.card {z : Fin 16 → Bool // CycleVector z} = 8 := by
    let f : (Bool × Bool × Bool) → {z // CycleVector z} := fun t => ⟨encode t,encoded t⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b h; exact injective (congrArg Subtype.val h)
      · intro z; exact ⟨(z.val 0,z.val 4,z.val 14), Subtype.ext ((classification z.val).mp z.property).symm⟩
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (by simp)
  have cyc : ∀ i, (cycleWalk i).IsCycle ∧ CycleVector (cycleVector i) ∧
      oddParity (cycleVector i) = true := by
    intro i
    refine ⟨?_,?_,?_⟩
    · rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length, SimpleGraph.Walk.isPath_def]
      fin_cases i <;> decide
    · unfold CycleVector
      fin_cases i <;> decide
    · fin_cases i <;> decide
  have oddClass (z : Fin 16 → Bool) (hz : CycleVector z) :
      oddParity z = true ↔ ∃ i, z = cycleVector i := by
    rw [(classification z).mp hz]
    generalize z 0 = a, z 4 = b, z 14 = d
    cases a <;> cases b <;> cases d <;> decide
  have oddCard : Nat.card {z : Fin 16 → Bool // CycleVector z ∧ oddParity z = true} = 4 := by
    let f : Fin 4 → {z // CycleVector z ∧ oddParity z = true} :=
      fun i => ⟨cycleVector i,(cyc i).2⟩
    have hf : Function.Bijective f := by
      constructor
      · have hinj : Function.Injective cycleVector := by decide
        intro a b h; exact hinj (congrArg Subtype.val h)
      · intro z
        obtain ⟨i,hi⟩ := (oddClass z.val z.property.1).mp z.property.2
        exact ⟨i,Subtype.ext hi.symm⟩
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (by simp)
  have cycleChecks : (∀ e, cycleVector 0 e ^^ cycleVector 1 e ^^ cycleVector 2 e ^^ cycleVector 3 e = false) ∧
    (∀ z, CycleVector z → z = fun e =>
      (z 0 && cycleVector 1 e) ^^ (z 4 && cycleVector 2 e) ^^
        (z 14 && cycleVector 3 e)) ∧
    (∀ a b d : Bool,
      (fun e => (a && cycleVector 1 e) ^^ (b && cycleVector 2 e) ^^
        (d && cycleVector 3 e)) = (fun _ => false) ↔
        a = false ∧ b = false ∧ d = false) ∧
    (∀ a b d, CycleVector (encode (a,b,d)) ∧
      oddParity (encode (a,b,d)) = (a ^^ b ^^ d)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e; fin_cases e <;> decide
    · intro z hz
      rw [(classification z).mp hz]
      generalize z 0 = a, z 4 = b, z 14 = d
      cases a <;> cases b <;> cases d <;> decide
    · intro a b d
      cases a <;> cases b <;> cases d <;> decide
    · intro a b d
      constructor
      · apply (classification _).mpr
        rfl
      · cases a <;> cases b <;> cases d <;> decide
  have residualFacts : Function.Bijective bit2 ∧
    (∀ a b, bit2 (a ^^ b) = bit2 a + bit2 b) ∧
    (∀ i j b, mappedTask.table i j = some (bit2 b) ↔ table i j = some b) ∧
    (∀ a b, (BooleanRankThreeFiber.support mappedTask).Adj a b ↔ G.Adj a b) ∧
    (∀ c i, BooleanRankThreeFiber.monoLeft mappedTask (bit2 c) i ↔ monoX c i) ∧
    (∀ d j, BooleanRankThreeFiber.monoRight mappedTask (bit2 d) j ↔ monoY d j) ∧
    (∀ c d a b, (BooleanRankThreeFiber.residual mappedTask (bit2 c) (bit2 d)).Adj a b ↔
      G.Adj a b ∧ survives c d a ∧ survives c d b) ∧
    (∀ e, BooleanRankThreeFiber.label mappedTask (edge e) = bit2 (bit e)) ∧
    (∀ c d, (residualWalk c d).support = cycles (residualCycle c d) ∧
      (residualWalk c d).edges = (cycleWalk (residualCycle c d)).edges ∧
      (residualWalk c d).IsCycle ∧
      walkParity (fun e => BooleanRankThreeFiber.label mappedTask e.val) (residualWalk c d) = 1) ∧
    (∀ c d, walkParity (fun e => BooleanRankThreeFiber.label mappedTask e.val) (residualWalk c d) =
      bit2 (oddParity (cycleVector (residualCycle c d)))) ∧
    (∀ c d, ¬ BooleanRankThreeFiber.Balanced mappedTask (BooleanRankThreeFiber.residual mappedTask (bit2 c) (bit2 d))) ∧
    (∀ c d : ZMod 2, ¬ BooleanRankThreeFiber.Balanced mappedTask (BooleanRankThreeFiber.residual mappedTask c d)) := by
    have hbits : Function.Bijective bit2 := by decide
    have hs : ∀ a b, (BooleanRankThreeFiber.support mappedTask).Adj a b ↔ G.Adj a b := by decide
    have hx : ∀ c i, BooleanRankThreeFiber.monoLeft mappedTask (bit2 c) i ↔ monoX c i := by
      unfold BooleanRankThreeFiber.monoLeft monoX; decide
    have hy : ∀ d j, BooleanRankThreeFiber.monoRight mappedTask (bit2 d) j ↔ monoY d j := by
      unfold BooleanRankThreeFiber.monoRight monoY; decide
    have hcycles : ∀ c d, (residualWalk c d).support = cycles (residualCycle c d) ∧
        (residualWalk c d).edges = (cycleWalk (residualCycle c d)).edges ∧
        (residualWalk c d).IsCycle ∧
        walkParity (fun e => BooleanRankThreeFiber.label mappedTask e.val) (residualWalk c d) = 1 := by
      intro c d
      refine ⟨?_, ?_, ?_, ?_⟩
      · cases c <;> cases d <;> rfl
      · cases c <;> cases d <;> rfl
      · rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length,
          SimpleGraph.Walk.isPath_def]
        cases c <;> cases d <;> decide
      · have raw : walkParity (fun e => BooleanRankThreeFiber.label mappedTask e.val) (residualWalk c d) =
            ((residualWalk c d).edges.map (BooleanRankThreeFiber.label mappedTask)).sum := by
          unfold walkParity
          congr 1
          apply List.map_congr_left
          intro e he
          simp only [dif_pos ((residualWalk c d).edges_subset_edgeSet he)]
        rw [raw]
        cases c <;> cases d <;> decide
    have hn : ∀ c d, ¬ BooleanRankThreeFiber.Balanced mappedTask
        (BooleanRankThreeFiber.residual mappedTask (bit2 c) (bit2 d)) := by
      intro c d hbal
      exact one_ne_zero ((hcycles c d).2.2.2.symm.trans
        (hbal _ (residualWalk c d) (hcycles c d).2.2.1))
    refine ⟨hbits, ?_, ?_, hs, hx, hy, ?_, ?_, hcycles, ?_, hn, ?_⟩
    · intro a b; cases a <;> cases b <;> decide
    · decide
    · intro c d a b
      cases a <;> cases b <;>
        simp only [BooleanRankThreeFiber.residual, survives, hs, hx, hy]
    · intro e; fin_cases e <;> rfl
    · intro c d
      rw [(hcycles c d).2.2.2]
      cases c <;> cases d <;> decide
    · intro c d
      obtain ⟨c',rfl⟩ := hbits.2 c
      obtain ⟨d',rfl⟩ := hbits.2 d
      exact hn c' d'
  have cutAUpper : ThreeLeafCausalPeak.CutAdmits output leftInput rightInput 2 := by
    let e : Fin 8 → Fin 2 := ![0,0,1,0,0,1,0,1]
    let d : Fin 2 → Fin 6 → Bool :=
      ![![false,false,true,true,false,true],![true,true,false,false,false,true]]
    refine ⟨Fin 2,e,d,?_,?_⟩
    · exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
        (by simp)
    · have correct : ∀ i j, (table i j).isSome = true →
          d (e i) j = (table i j).getD false := by decide
      intro w
      exact correct w.val.1 w.val.2 w.property
  have cutBUpper : ThreeLeafCausalPeak.CutAdmits output rightInput leftInput 2 := by
    let e : Fin 6 → Fin 2 := ![0,1,0,1,1,0]
    let d : Fin 2 → Fin 8 → Bool :=
      ![![false,true,true,true,true,true,false,false],
        ![false,true,false,false,false,false,true,true]]
    refine ⟨Fin 2,e,d,?_,?_⟩
    · exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
        (by simp)
    · have correct : ∀ i j, (table i j).isSome = true →
          d (e j) i = (table i j).getD false := by decide
      intro w
      exact correct w.val.1 w.val.2 w.property
  have lower {L R : Type} (l : Legal → L) (r : Legal → R)
      (w₀ w₁ : Legal) (hr : r w₀ = r w₁) (hf : output w₀ ≠ output w₁)
      (n : ℕ) (h : ThreeLeafCausalPeak.CutAdmits output l r n) : 2 ≤ n := by
    classical
    obtain ⟨A,e,d,hcard,hcorrect⟩ := h
    let : Fintype (Set.range (e ∘ l)) := Fintype.ofFinite _
    have different : e (l w₀) ≠ e (l w₁) := by
      intro he
      apply hf
      rw [← hcorrect w₀, ← hcorrect w₁, he, hr]
    by_contra hn
    have hs : Subsingleton (Set.range (e ∘ l)) :=
      Fintype.card_le_one_iff_subsingleton.mp (by
        simpa only [Nat.card_eq_fintype_card] using hcard.trans (by omega : n ≤ 1))
    exact different (congrArg Subtype.val
      (@Subsingleton.elim _ hs ⟨_,w₀,rfl⟩ ⟨_,w₁,rfl⟩))
  have cutA : ThreeLeafCausalPeak.cutCost output leftInput rightInput = 2 := by
    apply le_antisymm (Nat.sInf_le cutAUpper)
    exact lower leftInput rightInput ⟨(0,0),by decide⟩ ⟨(2,0),by decide⟩ rfl
      (by decide) _ (Nat.sInf_mem (show ∃ n,
        ThreeLeafCausalPeak.CutAdmits output leftInput rightInput n from ⟨2,cutAUpper⟩))
  have cutB : ThreeLeafCausalPeak.cutCost output rightInput leftInput = 2 := by
    apply le_antisymm (Nat.sInf_le cutBUpper)
    exact lower rightInput leftInput ⟨(6,0),by decide⟩ ⟨(6,3),by decide⟩ rfl
      (by decide) _ (Nat.sInf_mem (show ∃ n,
        ThreeLeafCausalPeak.CutAdmits output rightInput leftInput n from ⟨2,cutBUpper⟩))
  have degrees : ∀ v, G.degree v = if v ∈ branches then 3 else 2 := by decide
  have connected : G.Connected := by
    apply G.connected_iff_exists_forall_reachable.mpr
    refine ⟨y 0, ?_⟩
    have e (i : Fin 8) (j : Fin 6) (h : (table i j).isSome = true) :
        G.Reachable (x i) (y j) := SimpleGraph.Adj.reachable h
    have h0 := (e 0 0 (by decide)).symm
    have h2 := (e 2 0 (by decide)).symm
    have h6 := (e 6 0 (by decide)).symm
    have hy1 := h0.trans (e 0 1 (by decide))
    have hy4 := h2.trans (e 2 4 (by decide))
    have hy3 := h6.trans (e 6 3 (by decide))
    have h3 := hy4.trans (e 3 4 (by decide)).symm
    have hy2 := h3.trans (e 3 2 (by decide))
    have h1 := hy2.trans (e 1 2 (by decide)).symm
    have h4 := hy1.trans (e 4 1 (by decide)).symm
    have h5 := hy3.trans (e 5 3 (by decide)).symm
    have h7 := hy1.trans (e 7 1 (by decide)).symm
    intro v
    rcases v with i | j
    · fin_cases i <;> assumption
    · fin_cases j
      · exact SimpleGraph.Reachable.refl _
      · exact hy1
      · exact hy2
      · exact hy3
      · exact hy4
      · exact h4.trans (e 4 5 (by decide))
  have ca : (leftConflict table).Colorable 2 := by
    refine ⟨⟨![0,0,1,0,0,1,0,1],?_⟩⟩
    change ∀ i j, (leftConflict table).Adj i j → _
    simp only [leftConflict, SimpleGraph.top_adj]
    decide
  have cb : (rightConflict table).Colorable 2 := by
    refine ⟨⟨![0,1,0,1,1,0],?_⟩⟩
    change ∀ i j, (rightConflict table).Adj i j → _
    simp only [rightConflict, leftConflict, SimpleGraph.top_adj]
    decide
  have chiA : (leftConflict table).chromaticNumber = 2 := by
    apply le_antisymm ca.chromaticNumber_le
    refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (f := ![0,2]) (by simp) ?_
    simp only [Pairwise,leftConflict]
    decide
  have chiB : (rightConflict table).chromaticNumber = 2 := by
    apply le_antisymm cb.chromaticNumber_le
    refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (f := ![0,3]) (by simp) ?_
    simp only [Pairwise,rightConflict,leftConflict]
    decide
  have arange : Set.range alphaNat = {n : ℕ | n < 3} := by
    ext n
    constructor
    · rintro ⟨i,rfl⟩; exact (alpha i).isLt
    · intro hn
      have hsur : Function.Surjective alpha := by decide
      obtain ⟨i,hi⟩ := hsur ⟨n,hn⟩
      exact ⟨i,congrArg Fin.val hi⟩
  have brange : Set.range betaNat = {n : ℕ | n < 3} := by
    ext n
    constructor
    · rintro ⟨i,rfl⟩; exact (beta i).isLt
    · intro hn
      have hsur : Function.Surjective beta := by decide
      obtain ⟨i,hi⟩ := hsur ⟨n,hn⟩
      exact ⟨i,congrArg Fin.val hi⟩
  have acard : Nat.card (Set.range alphaNat) = 3 := by rw [arange]; exact (Nat.card_congr Fin.equivSubtype).symm.trans (Nat.card_fin 3)
  have bcard : Nat.card (Set.range betaNat) = 3 := by rw [brange]; exact (Nat.card_congr Fin.equivSubtype).symm.trans (Nat.card_fin 3)
  have correct : ∀ i j c, table i j = some c →
      decoderNat (alphaNat i) (betaNat j) = c := by decide
  have pathSupport (i : Fin 6) : (pathWalk i).support = paths i := by
    fin_cases i <;> rfl
  have cycleSupport (i : Fin 4) : (cycleWalk i).support = cycles i := by
    fin_cases i <;> rfl
  have certificate : Certificate := by
    refine ⟨⟨⟨0,0,false,rfl⟩,by decide,by decide,connected⟩, ?_, ?_, ?_,
      chiA,chiB,by decide,by decide,(by unfold monoX; decide),
      (by unfold monoY; decide),by decide,degrees,
      ?_,by decide,?_,by decide,by decide,?_,cyc,?_,
      classification,allCard,oddClass,oddCard,acard,bcard,correct,?_,
      cutA,cutB,cycleChecks.1,cycleChecks.2.1,cycleChecks.2.2.1,
      cycleChecks.2.2.2,residualFacts⟩
    · unfold cycleRank
      simp only [Nat.card_eq_fintype_card]
      decide
    · simp only [Nat.card_eq_fintype_card]; decide
    · simp only [Nat.card_eq_fintype_card]; decide
    · intro i
      constructor
      · apply SimpleGraph.Walk.IsPath.mk'
        fin_cases i <;> decide
      · fin_cases i <;> rfl
    · intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first | exact (hij rfl).elim | simp [internal, paths, List.disjoint_left]
    · intro v
      rcases v with i | j
      · refine ⟨![0,5,1,1,4,4,2,3] i, ?_⟩
        rw [pathSupport]
        fin_cases i <;> simp [paths]
      · refine ⟨![0,0,1,2,1,4] j, ?_⟩
        rw [pathSupport]
        fin_cases j <;> simp [paths]
    · simp_rw [cycleSupport]
      intro c d
      cases c <;> cases d <;>
        simp [cycles, residualCycle, survives, monoX, monoY, table, Fin.forall_fin_succ]
    · exact ⟨ℕ,ℕ,alphaNat,betaNat,decoderNat,acard.le,bcard.le,correct⟩
  intro h
  obtain ⟨u,v,_,hu,_,_⟩ := h certificate
  have hd := degrees u
  split_ifs at hd <;> omega

end D5.S3.Observer.Separation.BooleanRankThreeK4

