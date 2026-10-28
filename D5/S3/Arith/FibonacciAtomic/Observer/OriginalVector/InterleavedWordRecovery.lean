/- GID: D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original vector recovery by an interleaved native control tree and its complete legal word image. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
import D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Log
import Mathlib.InformationTheory.Hamming

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.InterleavedWordRecovery

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open ActualCutPartitionRecovery (prefixTrie prefixTrie_at)
open NativeSerialMachine
open DelayedOriginalReadout (rights rightClock right_clock_iterate right_clock_readout)
open scoped BigOperators

/-- Numerical false/true denotes original zero/one; source true denotes alpha. -/
noncomputable def leafValue {h : Nat} (q : Fin h → Address) (x : List Bool) (a : Address) : Source :=
  if hi : ∃ i, q i = a then .of (!(x.getD hi.choose.val false)) else .of true

/-- The cut is the entire level, including every unselected skeleton leaf. -/
def level (m : Nat) : Finset Address :=
  Finset.univ.image (List.ofFn : (Fin m → Bool) → Address)

private theorem mem_level (m : Nat) (a : Address) : a ∈ level m ↔ a.length = m := by
  classical
  constructor
  · rintro ha
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp ha
    simp
  · intro ha
    apply Finset.mem_image.mpr
    refine ⟨fun i => a.get ⟨i.val, by omega⟩, Finset.mem_univ _, ?_⟩
    subst m
    exact List.ofFn_get a

/-- A complete depth-m promised source, without any positivity restriction. -/
noncomputable def original {h : Nat} (m : Nat) (q : Fin h → Address) (x : List Bool) : Source :=
  prefixTrie m (level m) [] (leafValue q x)

private theorem original_at {h m : Nat} (q : Fin h → Address) (x : List Bool) (a : Address) (ha : a.length = m) :
    subtree a (original m q x) = some (leafValue q x a) := by
  apply prefixTrie_at
  · simpa using (mem_level m a).mpr ha
  · omega
  · intro s hs hne hm
    have len := (mem_level m s).mp (by simpa using hm)
    have eq := hs.eq_of_length (by omega)
    exact hne eq

private theorem selected_leaf {h m : Nat} (q : Fin h → Address)
    (injective : Function.Injective q) (lengths : ∀ i, (q i).length = m) (x : List Bool) (i : Fin h) :
    subtree (q i) (original m q x) = some (.of (!(x.getD i.val false))) := by
  classical
  rw [original_at q x (q i) (lengths i)]
  have hi : ∃ j, q j = q i := ⟨i, rfl⟩
  simp only [leafValue, dif_pos hi]
  rw [injective hi.choose_spec]

def rawReply (n : Nat) (b : Bool) : Reply :=
  if n % 2 = 0 then (if b then .beta else .alpha)
  else (if b then .branch else .beta)

def decode (n : Nat) (r : Reply) : Option Bool :=
  if n % 2 = 0 then
    match r with
    | .alpha => some false
    | .beta => some true
    | .branch => none
    | .absent => none
  else
    match r with
    | .beta => some false
    | .branch => some true
    | .alpha => none
    | .absent => none

private theorem decode_raw (n : Nat) (b : Bool) : decode n (rawReply n b) = some b := by
  cases b <;> by_cases hn : n % 2 = 0 <;> simp [decode, rawReply, hn]

private theorem leaf_reply (n : Nat) (b : Bool) :
    readout (rights (n/2)) (substitution^[n] (.of (!b))) = rawReply n b := by
  have ca := right_clock_iterate n (.of true)
  have cb := right_clock_iterate n (.of false)
  simp only [rightClock, Nat.zero_add] at ca cb
  have ra := right_clock_readout (n/2) (substitution^[n] (.of true))
  have rb := right_clock_readout (n/2) (substitution^[n] (.of false))
  have rem := Nat.mod_add_div n 2
  have bound := Nat.mod_lt n (by decide : 0 < 2)
  cases b <;> by_cases hn : n % 2 = 0
  · simpa [rawReply, hn] using ra.2.1.mpr (by omega)
  · simpa [rawReply, hn] using ra.2.2.1.mpr (by omega)
  · simpa [rawReply, hn] using rb.2.2.1.mpr (by omega)
  · simpa [rawReply, hn] using rb.2.2.2.mpr (by omega)

def literal {h : Nat} (q : Fin h → Address) (n : Nat) : Address :=
  (if hn : n < h then q ⟨n, hn⟩ else []) ++ rights (n/2)

private theorem original_reply {h m : Nat} (q : Fin h → Address)
    (injective : Function.Injective q) (lengths : ∀ i, (q i).length = m) (x : List Bool) (n : Nat) (hn : n < h) :
    readout (literal q n) (substitution^[n] (original m q x)) = rawReply n (x.getD n false) := by
  rw [literal, dif_pos hn]
  have present := NativeDepthPatterns.original_present_transport n (q ⟨n, hn⟩)
    (original m q x) _ (selected_leaf q injective lengths x ⟨n, hn⟩)
  rw [ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1, present]
  exact leaf_reply n _

/-- The three source-prescribed row kinds; proof fields do not add states. -/
inductive Vertex (h : Nat) where
  | q (s : List Bool) (bound : s.length < h)
  | u (s : List Bool) (bound : 0 < s.length ∧ s.length < h)
  | z (s : List Bool) (bound : s.length = h)

def child {h : Nat} (s : List Bool) (hs : s.length < h) (b : Bool) : Vertex h :=
  if hb : (s ++ [b]).length < h then .u (s ++ [b]) ⟨by simp, hb⟩
  else .z (s ++ [b]) (by simp only [List.length_append, List.length_singleton] at *; omega)

def response {h : Nat} (s : List Bool) (hs : s.length < h) (r : Reply) : Vertex h :=
  match decode s.length r with
  | some b => child s hs b
  | none => .q s hs

/-- Row selection has only one control argument; no source or epoch is supplied. -/
def program {h : Nat} (q : Fin h → Address) : Vertex h → Op (Vertex h) (List Bool)
  | .q s hs => .read (literal q s.length) (response s hs)
  | .u s hs => .applyRho (.q s hs.2)
  | .z s _ => .stop s

def initial (h : Nat) (positive : 0 < h) : Vertex h := .q [] positive

/-- The full chronological raw log, with one genuine Update between Reads. -/
def chronology {h : Nat} (q : Fin h → Address) (n : Nat) : List Bool → Trace
  | [] => []
  | b :: t => .read n (literal q n) (rawReply n b) ::
      (if t = [] then [] else .update n :: chronology q (n+1) t)

private theorem run_from {h m : Nat} (q : Fin h → Address)
    (injective : Function.Injective q) (lengths : ∀ i, (q i).length = m)
    (s t : List Bool) (nonempty : t ≠ []) (size : (s ++ t).length = h) :
    Run (program q) (.q s (by simp only [List.length_append] at size; have := List.length_pos_iff_ne_nil.mpr nonempty; omega))
      s.length (substitution^[s.length] (original m q (s ++ t)))
      (chronology q s.length t) (s ++ t) := by
  induction t generalizing s with
  | nil => exact (nonempty rfl).elim
  | cons b t ih =>
      have hs : s.length < h := by simp only [List.length_append, List.length_cons] at size; omega
      have read : readout (literal q s.length)
          (substitution^[s.length] (original m q (s ++ b :: t))) = rawReply s.length b := by
        rw [original_reply q injective lengths _ _ hs,
          List.getD_append_right _ _ _ _ le_rfl]
        simp
      apply Run.read rfl read
      simp only [response, decode_raw]
      by_cases ht : t = []
      · subst t
        have he : (s ++ [b]).length = h := size
        have no : ¬ (s ++ [b]).length < h := by omega
        have noNat : ¬ s.length+1 < h := by simpa using no
        simpa [chronology, child, noNat] using
          (Run.stop (δ := program q) (c := Vertex.z (s ++ [b]) he)
            (e := s.length) (r := substitution^[s.length] (original m q (s ++ [b]))) rfl)
      · have next : (s ++ [b]).length < h := by
          have hp : 0 < t.length := List.length_pos_iff_ne_nil.mpr ht
          simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil] at size ⊢
          omega
        have sz : ((s ++ [b]) ++ t).length = h := by simpa [List.append_assoc] using size
        have rest := ih (s ++ [b]) ht sz
        simp only [List.length_append, List.length_singleton] at rest
        rw [Function.iterate_succ_apply'] at rest
        have short : s.length+1 < h := by simpa using next
        simpa [chronology, ht, child, short, List.append_assoc] using
          (Run.update (δ := program q) (c := Vertex.u (s ++ [b]) ⟨by simp, next⟩) rfl rest)

def decodedAnswers (n : Nat) : List Reply → List (Option Bool)
  | [] => []
  | r :: rs => decode n r :: decodedAnswers (n+1) rs

private theorem decoded_chronology {h : Nat} (q : Fin h → Address) (n : Nat) (x : List Bool) :
    decodedAnswers n (answers (chronology q n x)) = x.map some := by
  induction x generalizing n with
  | nil => rfl
  | cons b t ih =>
    by_cases ht : t = []
    · subst t
      simp [chronology, answers, reads, decodedAnswers, decode_raw]
    · simpa [chronology, ht, answers, reads, decodedAnswers, decode_raw] using
        congrArg (List.cons (some b)) (ih (n+1))

private theorem raw_answers_injective {h : Nat} (q : Fin h → Address) :
    Function.Injective (fun x => answers (chronology q 0 x)) := by
  intro x y he
  have decoded := congrArg (decodedAnswers 0) he
  rw [decoded_chronology, decoded_chronology] at decoded
  exact (List.map_injective_iff.mpr (fun _ _ h => Option.some.inj h)) decoded

private theorem genuine_update (u : Source) : substitution u ≠ u := by
  intro he
  have hc := right_clock_iterate 1 u
  simpa [he] using hc

private theorem chronology_counts {h : Nat} (q : Fin h → Address) (n : Nat) (t : List Bool) :
    (answers (chronology q n t)).length = t.length ∧ (chronology q n t).length = 2*t.length - 1 ∧
    (chronology q n t).countP (fun e => match e with | .update _ => true | _ => false) = t.length - 1 ∧
    Event.localStep ∉ chronology q n t := by
  induction t generalizing n with
  | nil => simp [chronology, answers, reads]
  | cons b t ih =>
      by_cases ht : t = []
      · subst t; simp [chronology, answers, reads]
      · have hp := List.length_pos_iff_ne_nil.mpr ht
        have h := ih (n+1)
        simp only [chronology, ht, ↓reduceIte, answers, reads, List.map_cons,
          List.length_cons, List.countP_cons, List.mem_cons] at *
        simp_all
        omega

/-- The constructed Run retains every raw reply and ends at the fixed full target. -/
private theorem native_original_recovery {h : Nat} (positive : 0 < h)
    (q : Fin h → Address) (injective : Function.Injective q) (lengths : ∀ i, (q i).length = Nat.clog 2 h)
    (x : List Bool) (size : x.length = h) : Run (program q) (initial h positive) 0 (original (Nat.clog 2 h) q x)
      (chronology q 0 x) x ∧ (∀ t z, Run (program q) (initial h positive) 0 (original (Nat.clog 2 h) q x) t z →
      t = chronology q 0 x ∧ z = x) ∧ (answers (chronology q 0 x)).length = h ∧ (chronology q 0 x).length = 2*h-1 ∧
    (chronology q 0 x).countP (fun e => match e with | .update _ => true | _ => false) = h-1 ∧
    Event.localStep ∉ chronology q 0 x ∧ (∀ u : Source, substitution u ≠ u) := by
  have run := run_from q injective lengths [] x (by intro he; simp [he] at size; omega)
    (by simpa using size)
  have run' : Run (program q) (initial h positive) 0 (original (Nat.clog 2 h) q x)
      (chronology q 0 x) x := by simpa [initial] using run
  have counts := chronology_counts q 0 x
  refine ⟨run', ?_, ?_, ?_, ?_, counts.2.2.2, genuine_update⟩
  · intro t z other
    exact NativeSerialDepth.run_unique other run'
  · simpa [size] using counts.1
  · simpa [size] using counts.2.1
  · simpa [size] using counts.2.2.1

/-- Actual support, extracted from nativeStep reachability rather than installed rows. -/
def Reached {h : Nat} (positive : 0 < h) (q : Fin h → Address) (u : Source) (v : Vertex h) (r : Source) : Prop :=
  ∃ e t, StateTransition.Reaches (nativeStep (program q))
    (initial h positive, 0, u, []) (v, e, r, t)

def prefixOf {h : Nat} : Vertex h → List Bool
  | .q s _ | .u s _ | .z s _ => s

def epochOf {h : Nat} : Vertex h → Nat
  | .q s _ => s.length
  | .u s _ => s.length - 1
  | .z _ _ => h - 1

def Fits {h : Nat} (v : Vertex h) (x : List Bool) : Prop :=
  match v with | .z s _ => s = x | _ => prefixOf v <+: x

def Support {h m : Nat} (q : Fin h → Address) (x : List Bool) (v : Vertex h) (e : Nat) (r : Source) : Prop :=
  Fits v x ∧
  e = epochOf v ∧ r = substitution^[epochOf v] (original m q x)

private theorem next_prefix (s x : List Bool) (pre : s <+: x) (lt : s.length < x.length) :
    (s ++ [x.getD s.length false]) <+: x := by
  obtain ⟨t, rfl⟩ := List.prefix_iff_exists_append_eq.mp pre
  cases t with
  | nil => simp at lt
  | cons b t =>
    rw [List.getD_append_right _ _ _ _ le_rfl]
    simp only [Nat.sub_self, List.getD_cons_zero]
    exact List.prefix_iff_exists_append_eq.mpr ⟨t, by simp [List.append_assoc]⟩

private theorem support_step {h m : Nat} (q : Fin h → Address)
    (injective : Function.Injective q) (lengths : ∀ i, (q i).length = m) (x : List Bool) (size : x.length = h)
    (a b : Config (Vertex h)) (inv : Support (m := m) q x a.1 a.2.1 a.2.2.1)
    (step : nativeStep (program q) a = some b) :
    Support (m := m) q x b.1 b.2.1 b.2.2.1 := by
  rcases a with ⟨v, e, r, log⟩
  cases v with
  | q s hs =>
    dsimp [Support, Fits] at inv
    rcases inv with ⟨pre, he, hr⟩
    dsimp [epochOf, prefixOf] at he hr pre
    subst e; subst r
    have truth := original_reply q injective lengths x s.length hs
    have pre' := next_prefix s x pre (by omega)
    simp only [nativeStep, program, truth, response, decode_raw] at step
    have eq := Option.some.inj step
    subst b
    unfold child
    split
    · simp only [Support, Fits, prefixOf, epochOf]
      exact ⟨pre', by simp, by simp⟩
    · rename_i no
      have len : (s ++ [x.getD s.length false]).length = h := by simp at *; omega
      have same := pre'.eq_of_length (len.trans size.symm)
      simp only [Support, Fits, epochOf]
      have lenNat : s.length+1 = h := by simpa using len
      have ee : s.length = h-1 := by omega
      exact ⟨same, ee, by rw [ee]⟩
  | u s hs =>
    dsimp [Support, Fits] at inv
    rcases inv with ⟨pre, he, hr⟩
    dsimp [epochOf, prefixOf] at he hr pre
    subst e; subst r
    simp only [nativeStep, program] at step
    have eq := Option.some.inj step
    subst b
    refine ⟨pre, by dsimp [epochOf]; omega, ?_⟩
    dsimp [epochOf]
    have ee : s.length = (s.length-1)+1 := by omega
    conv_rhs => rw [ee]
    exact (Function.iterate_succ_apply' (f := (substitution : Source → Source)) (s.length-1) (original m q x)).symm
  | z s hs =>
    simp [nativeStep, program] at step

private theorem reached_support {h m : Nat} (positive : 0 < h) (q : Fin h → Address) (injective : Function.Injective q)
    (lengths : ∀ i, (q i).length = m) (x : List Bool) (size : x.length = h)
    (v : Vertex h) (r : Source) (reached : Reached positive q (original m q x) v r) : Fits v x ∧
      r = substitution^[epochOf v] (original m q x) := by
  obtain ⟨e, t, reach⟩ := reached
  have invariant : ∀ a, StateTransition.Reaches (nativeStep (program q))
      (initial h positive, 0, original m q x, []) a →
      Support (m := m) q x a.1 a.2.1 a.2.2.1 := by
    intro a reach
    induction reach with
    | refl => exact ⟨List.nil_prefix, rfl, rfl⟩
    | @tail b c path step ih => exact support_step q injective lengths x size b c ih step
  have inv := invariant _ reach
  exact ⟨inv.1, inv.2.2⟩

private theorem q_reached {h m : Nat} (positive : 0 < h) (q : Fin h → Address) (injective : Function.Injective q)
    (lengths : ∀ i, (q i).length = m) (x : List Bool) (size : x.length = h)
    (s : List Bool) (hs : s.length < h) (pre : s <+: x) : ∃ log, StateTransition.Reaches (nativeStep (program q))
      (initial h positive, 0, original m q x, [])
      (.q s hs, s.length, substitution^[s.length] (original m q x), log) := by
  induction s using List.reverseRecOn with
  | nil => exact ⟨[], Relation.ReflTransGen.refl⟩
  | append_singleton s b ih =>
    have lt : s.length < h := by simp at hs; omega
    have preS : s <+: x := (List.prefix_append _ _).trans pre
    obtain ⟨t, reach⟩ := ih lt preS
    obtain ⟨rest, hx⟩ := List.prefix_iff_exists_append_eq.mp pre
    have bit : x.getD s.length false = b := by
      rw [← hx, List.append_assoc, List.getD_append_right _ _ _ _ le_rfl]
      simp
    have read := (original_reply q injective lengths x s.length lt).trans (congrArg (rawReply s.length) bit)
    let mid : Config (Vertex h) := (.u (s ++ [b]) ⟨by simp, hs⟩,
      s.length, substitution^[s.length] (original m q x),
      t ++ [.read s.length (literal q s.length) (rawReply s.length b)])
    have first : nativeStep (program q)
        (.q s lt, s.length, substitution^[s.length] (original m q x), t) = some mid := by
      have short : s.length+1 < h := by simpa using hs
      simp [nativeStep, program, read, response, decode_raw, child, short, mid]
    have second : nativeStep (program q) mid =
        some (.q (s ++ [b]) hs, (s ++ [b]).length,
          substitution^[(s ++ [b]).length] (original m q x),
          mid.2.2.2 ++ [.update s.length]) := by
      simp [nativeStep, program, mid, Function.iterate_succ_apply', List.length_append, List.length_singleton]
      rfl
    exact ⟨_, (reach.tail first).tail second⟩

private theorem uz_reached {h m : Nat} (positive : 0 < h) (q : Fin h → Address) (injective : Function.Injective q)
    (lengths : ∀ i, (q i).length = m) (x : List Bool) (size : x.length = h)
    (s : List Bool) (nonempty : 0 < s.length) (bound : s.length ≤ h) (pre : s <+: x) :
    Reached positive q (original m q x) (if hs : s.length < h then .u s ⟨nonempty, hs⟩ else .z s (by omega))
      (substitution^[s.length-1] (original m q x)) := by
  cases s using List.reverseRecOn with
  | nil => simp at nonempty
  | append_singleton s b =>
    have lt : s.length < h := by simp at bound; omega
    have preS : s <+: x := (List.prefix_append _ _).trans pre
    obtain ⟨log, reach⟩ := q_reached positive q injective lengths x size s lt preS
    obtain ⟨rest, hx⟩ := List.prefix_iff_exists_append_eq.mp pre
    have bit : x.getD s.length false = b := by
      rw [← hx, List.append_assoc, List.getD_append_right _ _ _ _ le_rfl]
      simp
    have read := (original_reply q injective lengths x s.length lt).trans (congrArg (rawReply s.length) bit)
    refine ⟨s.length, log ++ [.read s.length (literal q s.length) (rawReply s.length b)], ?_⟩
    apply reach.tail
    change nativeStep (program q) _ = some _
    simp [nativeStep, program, read, response, decode_raw, child]

private theorem actual_supports {h m : Nat} (positive : 0 < h) (q : Fin h → Address) (injective : Function.Injective q)
    (lengths : ∀ i, (q i).length = m) (x : List Bool) (size : x.length = h) (v : Vertex h) (r : Source) :
    Reached positive q (original m q x) v r ↔ Fits v x ∧ r = substitution^[epochOf v] (original m q x) := by
  constructor
  · exact reached_support positive q injective lengths x size v r
  · rintro ⟨pre, rfl⟩
    cases v with
    | q s hs =>
      obtain ⟨log, reach⟩ := q_reached positive q injective lengths x size s hs pre
      exact ⟨s.length, log, reach⟩
    | u s hs =>
      simpa [hs.2, epochOf] using uz_reached positive q injective lengths x size s hs.1 (by omega) pre
    | z s hs =>
      have equal : s = x := pre
      cases equal
      simpa [size, epochOf] using uz_reached positive q injective lengths x size x
        (by omega) (by omega) (List.prefix_refl x)

def width (h : Nat) : Nat := 5*h-3

/-- Permanent separators occupy residues two and four; the last block is a Read. -/
def encode {h : Nat} (v : Vertex h) (c : Fin (width h)) : Bool :=
  decide ((c.val % 5 = 0 ∧ c.val/5 < (prefixOf v).length ∧
              (prefixOf v).getD (c.val/5) false = false) ∨
          (c.val % 5 = 1 ∧ c.val/5 < (prefixOf v).length ∧
              (prefixOf v).getD (c.val/5) false = true) ∨
          (c.val % 5 = 3 ∧ c.val/5 < epochOf v))

private theorem vertex_bounds {h : Nat} (v : Vertex h) : (prefixOf v).length ≤ h ∧ epochOf v ≤ h-1 := by
  cases v <;> dsimp [prefixOf, epochOf] <;> omega

private theorem encode_legal {h : Nat} (v : Vertex h) :
    D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm (width h) (encode v) := by
  apply (D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant.adm_iff_no_adjacent_true _ _).mpr
  intro i j adjacent
  by_contra no
  have hi : encode v i = true := (not_or.mp no).1 |> Bool.eq_true_of_not_eq_false
  have hj : encode v j = true := (not_or.mp no).2 |> Bool.eq_true_of_not_eq_false
  simp only [encode, decide_eq_true_eq] at hi hj
  have di := Nat.mod_add_div i.val 5
  have dj := Nat.mod_add_div j.val 5
  have mi := Nat.mod_lt i.val (by decide : 0 < 5)
  have mj := Nat.mod_lt j.val (by decide : 0 < 5)
  rcases hi with ⟨ri, ni, bi⟩ | ⟨ri, ni, bi⟩ | ⟨ri, ni⟩ <;>
    rcases hj with ⟨rj, nj, bj⟩ | ⟨rj, nj, bj⟩ | ⟨rj, nj⟩ <;>
    try omega
  have same : i.val/5 = j.val/5 := by omega
  rw [same, bj] at bi
  cases bi

private theorem read_coordinates {h : Nat} (positive : 0 < h) (v : Vertex h) (n : Nat) (hn : n < h) :
    (encode v ⟨5*n, by dsimp [width]; omega⟩ = true ∨ encode v ⟨5*n+1, by dsimp [width]; omega⟩ = true) ↔
      n < (prefixOf v).length := by
  have div : (5*n+1)/5 = n := by omega
  cases hb : (prefixOf v).getD n false <;> simp only [List.getD_eq_getElem?_getD] at hb <;> simp [encode, div, hb]

private theorem bit_coordinate {h : Nat} (positive : 0 < h) (v : Vertex h) (n : Nat) (hn : n < h) :
    encode v ⟨5*n+1, by dsimp [width]; omega⟩ = true ↔ n < (prefixOf v).length ∧ (prefixOf v).getD n false = true := by
  have div : (5*n+1)/5 = n := by omega
  simp [encode, div]

private theorem update_coordinate {h : Nat} (positive : 0 < h) (v : Vertex h) (n : Nat) (hn : n < h-1) :
    encode v ⟨5*n+3, by dsimp [width]; omega⟩ = true ↔ n < epochOf v := by
  have div : (5*n+3)/5 = n := by omega
  simp [encode, div]

private theorem encode_injective {h : Nat} (positive : 0 < h) :
    Function.Injective (encode : Vertex h → (Fin (width h) → Bool)) := by
  intro v w equal
  have boundsV := vertex_bounds v
  have boundsW := vertex_bounds w
  have len : (prefixOf v).length = (prefixOf w).length := by
    by_contra no
    rcases lt_or_gt_of_ne no with lt | gt
    · have hn : (prefixOf v).length < h := by omega
      have ev := read_coordinates positive v _ hn
      have ew := read_coordinates positive w _ hn
      rw [equal] at ev
      exact (Nat.lt_irrefl _)
        (ev.mp (ew.mpr lt))
    · have hn : (prefixOf w).length < h := by omega
      have ev := read_coordinates positive v _ hn
      have ew := read_coordinates positive w _ hn
      rw [equal] at ev
      exact (Nat.lt_irrefl _) (ew.mp (ev.mpr gt))
  have prefixEq : prefixOf v = prefixOf w := by
    apply List.ext_getElem len
    intro n hn hm
    have hnH : n < h := by omega
    have bits : (prefixOf v).getD n false = (prefixOf w).getD n false := by
      have ev := bit_coordinate positive v n hnH
      have ew := bit_coordinate positive w n hnH
      rw [equal] at ev
      have equiv : (prefixOf v).getD n false = true ↔ (prefixOf w).getD n false = true := by
        simpa [hn, hm] using ev.symm.trans ew
      cases hv : (prefixOf v).getD n false <;> cases hw : (prefixOf w).getD n false <;>
        simp only [hv, hw, Bool.false_eq_true, iff_false, iff_true, not_true_eq_false] at equiv ⊢ <;>
        tauto
    rw [List.getD_eq_getElem _ _ hn, List.getD_eq_getElem _ _ hm] at bits
    exact bits
  have epochs : epochOf v = epochOf w := by
    by_contra no
    rcases lt_or_gt_of_ne no with lt | gt
    · have hn : epochOf v < h-1 := by omega
      have ev := update_coordinate positive v _ hn
      have ew := update_coordinate positive w _ hn
      rw [equal] at ev
      exact (Nat.lt_irrefl _) (ev.mp (ew.mpr lt))
    · have hn : epochOf w < h-1 := by omega
      have ev := update_coordinate positive v _ hn
      have ew := update_coordinate positive w _ hn
      rw [equal] at ev
      exact (Nat.lt_irrefl _) (ew.mp (ev.mpr gt))
  cases v <;> cases w <;> simp only [prefixOf, epochOf] at prefixEq epochs
  all_goals first
    | cases prefixEq; rfl
    | cases prefixEq; omega

private def boundedListsEquiv (h : Nat) : {s : List Bool // s.length < h} ≃ (Σ n : Fin h, List.Vector Bool n.val) where
  toFun s := ⟨⟨s.val.length, s.property⟩, ⟨s.val, rfl⟩⟩
  invFun t := ⟨t.2.val, by rw [t.2.property]; exact t.1.isLt⟩
  left_inv s := by cases s; rfl
  right_inv t := by
    rcases t with ⟨⟨n, hn⟩, ⟨s, hs⟩⟩
    dsimp
    cases hs
    rfl

private def exactListsEquiv (h : Nat) : {s : List Bool // s.length = h} ≃ List.Vector Bool h := Equiv.refl _

private def nonemptyListsEquiv (h : Nat) : {s : List Bool // 0 < s.length ∧ s.length < h} ≃
      {s : {s : List Bool // s.length < h} // s.val ≠ []} where
  toFun s := ⟨⟨s.val, s.property.2⟩, List.length_pos_iff_ne_nil.mp s.property.1⟩
  invFun s := ⟨s.val.val, ⟨List.length_pos_iff_ne_nil.mpr s.property, s.val.property⟩⟩
  left_inv s := rfl
  right_inv s := rfl

private def vertexEquiv (h : Nat) : Vertex h ≃ ({s : List Bool // s.length < h} ⊕
      ({s : List Bool // 0 < s.length ∧ s.length < h} ⊕ {s : List Bool // s.length = h})) where
  toFun v := match v with
    | .q s hs => .inl ⟨s, hs⟩
    | .u s hs => .inr (.inl ⟨s, hs⟩)
    | .z s hs => .inr (.inr ⟨s, hs⟩)
  invFun v := match v with
    | .inl s => .q s.val s.property
    | .inr (.inl s) => .u s.val s.property
    | .inr (.inr s) => .z s.val s.property
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with a | (a | a) <;> rfl

noncomputable instance boundedListsFintype (h : Nat) :
    Fintype {s : List Bool // s.length < h} := (List.finite_length_lt Bool h).fintype

noncomputable instance exactListsFintype (h : Nat) : Fintype {s : List Bool // s.length = h} :=
  Fintype.ofEquiv (Fin h → Bool) (Equiv.vectorEquivFin Bool h).symm

noncomputable instance nonemptyListsFintype (h : Nat) : Fintype {s : List Bool // 0 < s.length ∧ s.length < h} := by
  classical
  exact Fintype.ofEquiv _ (nonemptyListsEquiv h).symm

noncomputable instance vertexFintype (h : Nat) : Fintype (Vertex h) :=
  Fintype.ofEquiv _ (vertexEquiv h).symm

private theorem q_count (h : Nat) : Fintype.card {s : List Bool // s.length < h} = 2^h-1 := by
  classical
  rw [Fintype.card_congr (boundedListsEquiv h), Fintype.card_sigma]
  have card (n : Fin h) : Fintype.card (List.Vector Bool n.val) = 2^n.val := by
    rw [Fintype.card_congr (Equiv.vectorEquivFin Bool n.val)]
    simp
  simp_rw [card]
  rw [Fin.sum_univ_eq_sum_range]
  simpa using Nat.geomSum_eq (by decide : 2 ≤ 2) h

private theorem u_count (h : Nat) (positive : 0 < h) :
    Fintype.card {s : List Bool // 0 < s.length ∧ s.length < h} = 2^h-2 := by
  classical
  let A := {s : List Bool // s.length < h}
  have empty : Fintype.card {s : A // s.val = []} = 1 := by
    have unique : Unique {s : A // s.val = []} :=
      { default := ⟨⟨[], positive⟩, rfl⟩
        uniq := by rintro ⟨⟨s, hs⟩, eq⟩; cases eq; rfl }
    letI := unique
    exact Fintype.card_unique
  rw [Fintype.card_congr (nonemptyListsEquiv h)]
  rw [Fintype.card_subtype_compl (fun s : A => s.val = []), empty]
  dsimp [A]
  rw [q_count]
  omega

private theorem z_count (h : Nat) : Fintype.card {s : List Bool // s.length = h} = 2^h := by
  rw [Fintype.card_congr (exactListsEquiv h)]
  rw [Fintype.card_congr (Equiv.vectorEquivFin Bool h)]
  simp

private theorem vertex_count (h : Nat) (positive : 0 < h) : Fintype.card (Vertex h) = 3*2^h-3 := by
  rw [Fintype.card_congr (vertexEquiv h), Fintype.card_sum, Fintype.card_sum,
    q_count, u_count h positive, z_count]
  have atLeast : 2 ≤ 2^h := by
    exact le_trans (by decide : 2 ≤ 2^1) (Nat.pow_le_pow_right (by decide) positive)
  omega

/-- Every allowed prefix has a complete promised original vector. -/
private theorem installed_vertex_occurs {h m : Nat} (positive : 0 < h)
    (q : Fin h → Address) (injective : Function.Injective q) (lengths : ∀ i, (q i).length = m) (v : Vertex h) :
    ∃ x : List Bool, x.length = h ∧ ∃ r, Reached positive q (original m q x) v r := by
  let x := prefixOf v ++ List.replicate (h-(prefixOf v).length) false
  have bound := (vertex_bounds v).1
  have size : x.length = h := by simp [x]; omega
  refine ⟨x, size, substitution^[epochOf v] (original m q x), ?_⟩
  apply (actual_supports positive q injective lengths x size v _).mpr
  refine ⟨?_, rfl⟩
  cases v with
  | q s hs => exact List.prefix_append _ _
  | u s hs => exact List.prefix_append _ _
  | z s hs => simp [Fits, x, prefixOf, hs]

private theorem family_injective {h m : Nat} (q : Fin h → Address)
    (injective : Function.Injective q) (lengths : ∀ i, (q i).length = m) :
    Function.Injective (fun x : {x : List Bool // x.length = h} => original m q x.val) := by
  intro x y equal
  change original m q x.val = original m q y.val at equal
  apply Subtype.ext
  apply List.ext_getElem (x.property.trans y.property.symm)
  intro n hn hm
  have nh : n < h := by omega
  have atX := selected_leaf q injective lengths x.val ⟨n, nh⟩
  have atY := selected_leaf q injective lengths y.val ⟨n, nh⟩
  rw [equal, atY] at atX
  have leafEq := Option.some.inj atX
  have bits : x.val.getD n false = y.val.getD n false := by
    injection leafEq with hb
    have hb' := congrArg Bool.not hb.symm
    simpa using hb'
  rw [List.getD_eq_getElem _ _ hn, List.getD_eq_getElem _ _ hm] at bits
  exact bits

private theorem unselected_leaf {h m : Nat} (q : Fin h → Address) (x : List Bool)
    (a : Address) (size : a.length = m) (unselected : ∀ i, q i ≠ a) : subtree a (original m q x) = some (.of true) := by
  classical
  rw [original_at q x a size, leafValue, dif_neg (by simpa using unselected)]

private theorem one_bit {n : Nat} (a b : Fin n → Bool) (c : Fin n)
    (different : a c ≠ b c) (same : ∀ j, j ≠ c → a j = b j) : hammingDist a b = 1 := by
  classical
  have filter : Finset.univ.filter (fun j => a j ≠ b j) = {c} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      by_contra ne
      exact h (same j ne)
    · rintro rfl
      exact different
  rw [hammingDist, filter, Finset.card_singleton]

private theorem child_coordinates {h : Nat} (s : List Bool) (hs : s.length < h) (b : Bool) :
    prefixOf (child s hs b) = s ++ [b] ∧ epochOf (child s hs b) = s.length := by
  unfold child
  split
  · simp [prefixOf, epochOf]
  · rename_i no
    have size : s.length+1 = h := by simp at no; omega
    exact ⟨rfl, by dsimp [epochOf]; omega⟩

private theorem read_bit_change {h : Nat} (positive : 0 < h) (s : List Bool) (hs : s.length < h) (b : Bool) :
    hammingDist (encode (.q s hs)) (encode (child s hs b)) = 1 := by
  let c : Fin (width h) := ⟨5*s.length + b.toNat, by
    have bit := Bool.toNat_le b
    dsimp [width]
    omega⟩
  have coords := child_coordinates s hs b
  have div1 : (5*s.length+1)/5 = s.length := by omega
  have old : encode (.q s hs) c = false := by
    cases b <;> simp [encode, c, prefixOf, epochOf, div1]
  have new : encode (child s hs b) c = true := by
    have div0 : (5*s.length)/5 = s.length := by omega
    have div1 : (5*s.length+1)/5 = s.length := by omega
    cases b <;> simp [encode, c, coords.1, coords.2, div0, div1, List.getD_append_right]
  apply one_bit _ _ c (by rw [old, new]; decide)
  intro j ne
  have notc : j.val ≠ 5*s.length+b.toNat := by
    intro he; apply ne; exact Fin.ext he
  unfold encode
  rw [coords.1, coords.2]
  dsimp only [prefixOf, epochOf]
  by_cases before : j.val/5 < s.length
  · have get := List.getD_append s [b] false (j.val/5) before
    have before' : j.val/5 < s.length+1 := by omega
    simp only [List.length_append, List.length_singleton, get, before, before',
      true_and, and_true]
  · by_cases equal : j.val/5 = s.length
    · have get := List.getD_append_right s [b] false (j.val/5) (by omega)
      simp only [equal, Nat.sub_self, List.getD_cons_zero] at get
      have rem := Nat.mod_add_div j.val 5
      have lenNext : j.val/5 < s.length+1 := by omega
      simp only [List.length_append, List.length_singleton, equal, get, before, lenNext,
        false_and, and_false, false_or, true_and, and_true]
      cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] at notc ⊢
      all_goals
        congr 1
        apply propext
        simp only [Bool.false_eq_true, Bool.true_eq_false, true_and, and_true, false_and, and_false, false_or, or_false]
        omega
    · have later : ¬ j.val/5 < s.length+1 := by omega
      simp only [List.length_append, List.length_singleton, before, later,
        false_and, and_false, false_or]

private theorem update_bit_change {h : Nat} (positive : 0 < h) (s : List Bool) (hs : 0 < s.length ∧ s.length < h) :
    hammingDist (encode (.u s hs)) (encode (.q s hs.2)) = 1 := by
  let c : Fin (width h) := ⟨5*(s.length-1)+3, by dsimp [width]; omega⟩
  have div : (5*(s.length-1)+3)/5 = s.length-1 := by omega
  have old : encode (.u s hs) c = false := by simp [encode, c, prefixOf, epochOf, div]
  have new : encode (.q s hs.2) c = true := by
    simp [encode, c, prefixOf, epochOf, div]
    omega
  apply one_bit _ _ c (by rw [old, new]; decide)
  intro j ne
  have notc : j.val ≠ 5*(s.length-1)+3 := by
    intro he; apply ne; exact Fin.ext he
  have rem := Nat.mod_add_div j.val 5
  have only : (j.val%5 = 3 ∧ j.val/5 < s.length-1) ↔
      (j.val%5 = 3 ∧ j.val/5 < s.length) := by
    constructor
    · rintro ⟨mod, bound⟩
      exact ⟨mod, by omega⟩
    · rintro ⟨mod, bound⟩
      refine ⟨mod, ?_⟩
      by_contra no
      have divEq : j.val/5 = s.length-1 := by omega
      apply notc
      omega
  simp only [encode, prefixOf, epochOf]
  congr 1
  apply propext
  exact or_congr Iff.rfl (or_congr Iff.rfl only)

private theorem unsupported_hold {h : Nat} (s : List Bool) (hs : s.length < h)
    (r : Reply) (no : decode s.length r = none) :
    response s hs r = .q s hs ∧ hammingDist (encode (.q s hs)) (encode (response s hs r)) = 0 := by
  simp [response, no, hammingDist_self]

/-- Precisely the image words have rows. Ambient legal words are not installed. -/
def Installed (h : Nat) := {w : Fin (width h) → Bool // w ∈ Set.range (encode : Vertex h → _)}

def install {h : Nat} (v : Vertex h) : Installed h := ⟨encode v, ⟨v, rfl⟩⟩

/-- Immutable inverse lookup; its argument and result are never paired as mutable state. -/
noncomputable def inverse {h : Nat} (w : Installed h) : Vertex h := w.property.choose

private theorem install_inverse {h : Nat} (w : Installed h) : install (inverse w) = w := by
  apply Subtype.ext
  exact w.property.choose_spec

private theorem inverse_install {h : Nat} (positive : 0 < h) (v : Vertex h) : inverse (install v) = v := by
  apply encode_injective positive
  exact (install v).property.choose_spec

/-- Instruction, literal, response write and full fixed output are word-selected. -/
noncomputable def wordProgram {h : Nat} (q : Fin h → Address) (w : Installed h) : Op (Installed h) (List Bool) :=
  match program q (inverse w) with
  | .localStep v => .localStep (install v)
  | .read a next => .read a (fun r => install (next r))
  | .applyRho v => .applyRho (install v)
  | .stop x => .stop x

private theorem word_q {h : Nat} (positive : 0 < h) (q : Fin h → Address) (s : List Bool) (hs : s.length < h) :
    wordProgram q (install (.q s hs)) = .read (literal q s.length) (fun r => install (response s hs r)) := by
  simp [wordProgram, inverse_install positive, program]

private theorem word_u {h : Nat} (positive : 0 < h) (q : Fin h → Address)
    (s : List Bool) (hs : 0 < s.length ∧ s.length < h) :
    wordProgram q (install (.u s hs)) = .applyRho (install (.q s hs.2)) := by
  simp [wordProgram, inverse_install positive, program]

private theorem word_z {h : Nat} (positive : 0 < h) (q : Fin h → Address) (s : List Bool) (hs : s.length = h) :
    wordProgram q (install (.z s hs)) = .stop s := by
  simp [wordProgram, inverse_install positive, program]

private theorem word_native_run {h : Nat} (positive : 0 < h) (q : Fin h → Address)
    (v : Vertex h) (e : Nat) (r : Source) (t : Trace) (x : List Bool) (run : Run (program q) v e r t x) :
    Run (wordProgram q) (install v) e r t x := by
  induction run with
  | stop row =>
    apply Run.stop
    simp [wordProgram, inverse_install positive, row]
  | @localStep c next e r t o row run ih =>
    apply Run.localStep (c' := install next)
    · simp [wordProgram, inverse_install positive, row]
    · exact ih
  | @update c next e r t o row run ih =>
    apply Run.update (c' := install next)
    · simp [wordProgram, inverse_install positive, row]
    · exact ih
  | @read c e r a k y t o row truth run ih =>
    apply Run.read (k := fun r => install (k r))
    · simp [wordProgram, inverse_install positive, row]
    · exact truth
    · exact ih

private theorem word_native_step {h : Nat} (positive : 0 < h) (q : Fin h → Address)
    (v : Vertex h) (e : Nat) (r : Source) (t : Trace) : nativeStep (wordProgram q) (install v, e, r, t) =
      (nativeStep (program q) (v,e,r,t)).map (fun a => (install a.1, a.2.1, a.2.2.1, a.2.2.2)) := by
  simp only [nativeStep, wordProgram, inverse_install positive]
  cases program q v <;> rfl

private theorem word_native_reaches {h : Nat} (positive : 0 < h) (q : Fin h → Address)
    (a b : Config (Vertex h)) (reach : StateTransition.Reaches (nativeStep (program q)) a b) :
    StateTransition.Reaches (nativeStep (wordProgram q)) (install a.1, a.2.1, a.2.2.1, a.2.2.2)
      (install b.1, b.2.1, b.2.2.1, b.2.2.2) := by
  induction reach with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c reach step ih =>
    apply ih.tail
    change nativeStep (wordProgram q) _ = some _
    rcases b with ⟨v,e,r,t⟩
    change nativeStep (program q) (v,e,r,t) = some c at step
    rw [word_native_step positive q, step]
    rfl

private theorem inverse_native_step {h : Nat} (positive : 0 < h)
    (q : Fin h → Address) (w : Installed h) (e : Nat) (r : Source) (t : Trace) :
    nativeStep (program q) (inverse w,e,r,t) = (nativeStep (wordProgram q) (w,e,r,t)).map
        (fun a => (inverse a.1,a.2.1,a.2.2.1,a.2.2.2)) := by
  rw [← install_inverse w, word_native_step positive]
  simp only [inverse_install positive]
  cases hs : nativeStep (program q) (inverse w,e,r,t) with
  | none => rfl
  | some c =>
    rcases c with ⟨v,e,r,t⟩
    simp only [Option.map, inverse_install positive]
    rfl

private theorem inverse_native_reaches {h : Nat} (positive : 0 < h) (q : Fin h → Address) (a b : Config (Installed h))
    (reach : StateTransition.Reaches (nativeStep (wordProgram q)) a b) :
    StateTransition.Reaches (nativeStep (program q)) (inverse a.1,a.2.1,a.2.2.1,a.2.2.2)
      (inverse b.1,b.2.1,b.2.2.1,b.2.2.2) := by
  induction reach with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c reach step ih =>
    apply ih.tail
    rcases b with ⟨w,e,r,t⟩
    change nativeStep (wordProgram q) (w,e,r,t) = some c at step
    rw [inverse_native_step positive q, step]
    rfl

private theorem word_actual_supports {h m : Nat} (positive : 0 < h)
    (q : Fin h → Address) (injective : Function.Injective q)
    (lengths : ∀ i, (q i).length = m) (x : List Bool) (size : x.length = h) (w : Installed h) (r : Source) :
    (∃ e t, StateTransition.Reaches (nativeStep (wordProgram q))
      (install (initial h positive),0,original m q x,[]) (w,e,r,t)) ↔
      Fits (inverse w) x ∧ r = substitution^[epochOf (inverse w)] (original m q x) := by
  rw [← actual_supports positive q injective lengths x size (inverse w) r]
  constructor
  · rintro ⟨e,t,reach⟩
    refine ⟨e,t,?_⟩
    simpa [inverse_install positive] using inverse_native_reaches positive q _ _ reach
  · rintro ⟨e,t,reach⟩
    refine ⟨e,t,?_⟩
    simpa [install_inverse] using word_native_reaches positive q _ _ reach

private noncomputable def installedEquiv (h : Nat) (positive : 0 < h) : Vertex h ≃ Installed h where
  toFun := install
  invFun := inverse
  left_inv := inverse_install positive
  right_inv := install_inverse

noncomputable instance installedFintype (h : Nat) : Fintype (Installed h) := by
  classical
  unfold Installed
  infer_instance

private theorem installed_count (h : Nat) (positive : 0 < h) : Fintype.card (Installed h) = 3*2^h-3 := by
  rw [← Fintype.card_congr (installedEquiv h positive), vertex_count h positive]

private theorem every_word_occurs {h m : Nat} (positive : 0 < h)
    (q : Fin h → Address) (injective : Function.Injective q) (lengths : ∀ i, (q i).length = m) (w : Installed h) :
    ∃ x : List Bool, x.length = h ∧ ∃ e r t, StateTransition.Reaches (nativeStep (wordProgram q))
        (install (initial h positive), 0, original m q x, []) (w,e,r,t) := by
  obtain ⟨x, size, r, e, t, reach⟩ :=
    installed_vertex_occurs positive q injective lengths (inverse w)
  refine ⟨x, size, e, r, t, ?_⟩
  simpa [install_inverse] using word_native_reaches positive q _ _ reach

private def sourcePathEquiv {h : Nat} (positive : 0 < h) (x : List Bool) (size : x.length = h) :
    {v : Vertex h // Fits v x} ≃ (Fin h ⊕ (Fin (h-1) ⊕ Unit)) where
  toFun v := match v with
    | ⟨.q s hs, _⟩ => .inl ⟨s.length, hs⟩
    | ⟨.u s hs, _⟩ => .inr (.inl ⟨s.length-1, by omega⟩)
    | ⟨.z s hs, _⟩ => .inr (.inr ())
  invFun v := match v with
    | .inl n => ⟨.q (x.take n.val) (by simpa [List.length_take, size] using n.isLt), List.take_prefix _ _⟩
    | .inr (.inl n) => ⟨.u (x.take (n.val+1)) (by
        have lt : n.val+1 < h := by omega
        simp [List.length_take, size, Nat.min_eq_left lt.le]
        omega), List.take_prefix _ _⟩
    | .inr (.inr _) => ⟨.z x size, rfl⟩
  left_inv v := by
    rcases v with ⟨v, fits⟩
    apply Subtype.ext
    cases v with
    | q s hs =>
      have eq : s = x.take s.length := List.prefix_iff_eq_take.mp fits
      change Vertex.q (x.take s.length) _ = Vertex.q s hs
      congr 1
      exact eq.symm
    | u s hs =>
      have eq : s = x.take s.length := List.prefix_iff_eq_take.mp fits
      have len : s.length-1+1 = s.length := by omega
      simp only [len]
      change Vertex.u (x.take s.length) _ = Vertex.u s hs
      congr 1
      exact eq.symm
    | z s hs =>
      have eq : s = x := fits
      cases eq
      rfl
  right_inv v := by
    rcases v with n | (n | u)
    · simp [List.length_take, size, Nat.min_eq_left n.isLt.le]
    · have lt : n.val+1 < h := by omega
      simp [List.length_take, size, Nat.min_eq_left lt.le]
    · cases u; rfl

private theorem source_path_count {h m : Nat} (positive : 0 < h)
    (q : Fin h → Address) (injective : Function.Injective q)
    (lengths : ∀ i, (q i).length = m) (x : List Bool) (size : x.length = h) :
    Nat.card {v : Vertex h // ∃ r, Reached positive q (original m q x) v r} = 2*h := by
  classical
  have fits (v : Vertex h) :
      (∃ r, Reached positive q (original m q x) v r) ↔ Fits v x := by
    constructor
    · rintro ⟨r, reach⟩
      exact ((actual_supports positive q injective lengths x size v r).mp reach).1
    · intro fits
      exact ⟨_, (actual_supports positive q injective lengths x size v _).mpr ⟨fits, rfl⟩⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight fits), Nat.card_congr (sourcePathEquiv positive x size)]
  simp only [Nat.card_sum, Nat.card_fin, Nat.card_unique]
  omega

private theorem word_no_local {h : Nat} (q : Fin h → Address) (w : Installed h)
    (c : Installed h) : wordProgram q w ≠ .localStep c := by
  unfold wordProgram
  cases inverse w <;> simp [program]

/-- A mathematical installation conditional on the complete-word table services. -/
theorem interleaved_word_recovery {h : Nat} (positive : 0 < h) (q : Fin h → Address) (injective : Function.Injective q)
    (lengths : ∀ i, (q i).length = Nat.clog 2 h) : Function.Injective (fun x : {x : List Bool // x.length = h} =>
      original (Nat.clog 2 h) q x.val) ∧ (∀ x a, a.length = Nat.clog 2 h → (∀ i, q i ≠ a) →
      subtree a (original (Nat.clog 2 h) q x) = some (.of true)) ∧ (∀ x i, subtree (q i) (original (Nat.clog 2 h) q x) =
      some (.of (!(x.getD i.val false)))) ∧ (∀ x, x.length = h →
      Run (program q) (initial h positive) 0 (original (Nat.clog 2 h) q x) (chronology q 0 x) x ∧
      Run (wordProgram q) (install (initial h positive)) 0 (original (Nat.clog 2 h) q x) (chronology q 0 x) x ∧
      (∀ t z, Run (wordProgram q) (install (initial h positive)) 0
          (original (Nat.clog 2 h) q x) t z → t = chronology q 0 x ∧ z = x) ∧ (answers (chronology q 0 x)).length = h ∧
      (chronology q 0 x).length = 2*h-1 ∧
      (chronology q 0 x).countP (fun e => match e with | .update _ => true | _ => false) = h-1 ∧
      Event.localStep ∉ chronology q 0 x ∧
      Nat.card {v : Vertex h // ∃ r, Reached positive q (original (Nat.clog 2 h) q x) v r} = 2*h) ∧
    (∀ x, x.length = h → ∀ v r, Reached positive q (original (Nat.clog 2 h) q x) v r ↔
        Fits v x ∧ r = substitution^[epochOf v] (original (Nat.clog 2 h) q x)) ∧ Fintype.card (Vertex h) = 3*2^h-3 ∧
    Fintype.card (Installed h) = 3*2^h-3 ∧ (∀ w : Installed h,
      D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm (5*h-3) w.val) ∧
    Function.Injective (encode : Vertex h → (Fin (5*h-3) → Bool)) ∧
    (∀ (s : List Bool) (hs : s.length < h) (b : Bool), hammingDist (encode (.q s hs)) (encode (child s hs b)) = 1) ∧
    (∀ (s : List Bool) (hs : 0 < s.length ∧ s.length < h), hammingDist (encode (.u s hs)) (encode (.q s hs.2)) = 1) ∧
    (∀ (s : List Bool) (hs : s.length < h) (r : Reply), decode s.length r = none →
      response s hs r = .q s hs ∧ hammingDist (encode (.q s hs)) (encode (response s hs r)) = 0) ∧
    (∀ w : Installed h, ∃ x : List Bool, x.length = h ∧ ∃ e r t, StateTransition.Reaches (nativeStep (wordProgram q))
        (install (initial h positive), 0, original (Nat.clog 2 h) q x, []) (w,e,r,t)) ∧
    (∀ s hs, wordProgram q (install (.q s hs)) = .read (literal q s.length) (fun r => install (response s hs r))) ∧
    (∀ s hs, wordProgram q (install (.u s hs)) = .applyRho (install (.q s hs.2))) ∧
    (∀ s hs, wordProgram q (install (.z s hs)) = .stop s) ∧ (∀ w c, wordProgram q w ≠ .localStep c) ∧
    Function.Injective (fun x => answers (chronology q 0 x)) ∧ (∀ x, x.length = h → ∀ w r,
      (∃ e t, StateTransition.Reaches (nativeStep (wordProgram q))
        (install (initial h positive),0,original (Nat.clog 2 h) q x,[]) (w,e,r,t)) ↔ Fits (inverse w) x ∧
          r = substitution^[epochOf (inverse w)] (original (Nat.clog 2 h) q x)) ∧
    (∀ v e r t, nativeStep (wordProgram q) (install v,e,r,t) = (nativeStep (program q) (v,e,r,t)).map
        (fun a => (install a.1,a.2.1,a.2.2.1,a.2.2.2))) ∧ (∀ x a, a.length = Nat.clog 2 h →
      subtree a (original (Nat.clog 2 h) q x) = some (leafValue q x a)) ∧ (∀ u : Source, substitution u ≠ u) := by
  refine ⟨family_injective q injective lengths, ?_, selected_leaf q injective lengths,
    ?_, ?_, vertex_count h positive, installed_count h positive, ?_,
    encode_injective positive, read_bit_change positive, update_bit_change positive,
    unsupported_hold, every_word_occurs positive q injective lengths,
    word_q positive q, word_u positive q, word_z positive q, word_no_local q,
    raw_answers_injective q, ?_, word_native_step positive q, ?_, genuine_update⟩
  · intro x a ha unused
    exact unselected_leaf q x a ha unused
  · intro x size
    obtain ⟨run, unique, reads, primitives, updates, noLocal, genuine⟩ :=
      native_original_recovery positive q injective lengths x size
    have wordRun := word_native_run positive q _ _ _ _ _ run
    exact ⟨run, wordRun, fun t z other => NativeSerialDepth.run_unique other wordRun,
      reads, primitives, updates, noLocal, source_path_count positive q injective lengths x size⟩
  · intro x size v r
    exact actual_supports positive q injective lengths x size v r
  · intro w
    rw [← install_inverse w]
    exact encode_legal (inverse w)
  · intro x size w r
    exact word_actual_supports positive q injective lengths x size w r
  · intro x a ha
    exact original_at q x a ha

end D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.InterleavedWordRecovery
