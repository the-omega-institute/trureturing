/- GID: D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every native parity run reads every independent original cone. -/

import D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
import D5.S3.Arith.FibonacciAtomic.Observer.NativePolynomialDescriptorObstruction
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
import D5.S1.Words.AdmissibleWords.AdmissibleCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralControlTable

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeSerialMachine (Event Trace)

/-- The two supported reply labels at an even or odd delayed epoch. -/
def decodeBit (epoch : Nat) : Reply → Option Bool :=
  if epoch % 2 = 0 then
    fun r => match r with
      | .alpha => some false
      | .beta => some true
      | .branch | .absent => none
  else
    fun r => match r with
      | .beta => some false
      | .branch => some true
      | .alpha | .absent => none

/-- The three kinds of vertices in Construction 3.2. -/
inductive Control where
  | q (pref : List Bool)
  | u (pref : List Bool)
  | z (target : List Bool)
  deriving DecidableEq

/-- The response successor at a Q-row, including the legal hold completion. -/
def responseSuccessor (height : Nat) (pref : List Bool) (reply : Reply) : Control :=
  match decodeBit pref.length reply with
  | some bit =>
      if pref.length + 1 < height then
        .u (pref ++ [bit])
      else
        .z (pref ++ [bit])
  | none => .q pref

/-- The complete source-aware instruction table. -/
def controlProgram (height : Nat) (addresses : Nat → Address) :
    Control → NativeSerialMachine.Op Control (List Bool)
  | .q pref => .read (addresses pref.length) (responseSuccessor height pref)
  | .u pref => .applyRho (.q pref)
  | .z target => .stop target

/-- The certified supported chronology.  It records exactly the relation that
    the Q/U/Z table needs; no decoder correctness is hidden in its definition. -/
inductive DecodedPath (addresses : Nat → Address) :
    Nat → Nat → Source → List Bool → Prop
  | nil (epoch : Nat) (source : Source) :
      DecodedPath addresses epoch 0 source []
  | cons {epoch remaining : Nat} {source : Source} {bit : Bool}
      {tail : List Bool} :
      decodeBit epoch (readout (addresses epoch) source) = some bit →
      DecodedPath addresses (epoch + 1) remaining (substitution source) tail →
      DecodedPath addresses epoch (remaining + 1) source (bit :: tail)

/-- The trace prescribed by the table, before proving that it is executable. -/
def chronology (addresses : Nat → Address) : Nat → Nat → Source → Trace
  | 0, _, _ => []
  | 1, epoch, source =>
      [.read epoch (addresses epoch) (readout (addresses epoch) source)]
  | remaining + 2, epoch, source =>
      .read epoch (addresses epoch) (readout (addresses epoch) source) ::
        .update epoch :: chronology addresses (remaining + 1) (epoch + 1)
          (substitution source)

def updateCount : Trace → Nat
  | [] => 0
  | .update _ :: rest => updateCount rest + 1
  | _ :: rest => updateCount rest

def readCount : Trace → Nat
  | [] => 0
  | .read _ _ _ :: rest => readCount rest + 1
  | _ :: rest => readCount rest

/-- The descending rank on the supported control graph. -/
def rank (height : Nat) : Control → Nat
  | .q pref => 2 * (height - pref.length) - 1
  | .u pref => 2 * (height - pref.length)
  | .z _ => 0

private theorem q_supported_rank {height : Nat} {pref : List Bool} (bit : Bool)
    (bound : pref.length < height) :
    rank height (if pref.length + 1 < height then
      .u (pref ++ [bit]) else .z (pref ++ [bit])) + 1 =
      rank height (.q pref) := by
  by_cases hnext : pref.length + 1 < height
  · simp [rank, hnext]
    omega
  · have hlast : pref.length + 1 = height := by omega
    simp [rank, hlast]
    omega

private theorem u_rank_step {height : Nat} {pref : List Bool}
    (bound : pref.length < height) :
    rank height (.q pref) + 1 = rank height (.u pref) := by
  simp [rank]
  omega

private theorem response_rank_step {height : Nat} {pref : List Bool} {reply : Reply}
    (bound : pref.length < height)
    {bit : Bool}
    (supported : decodeBit pref.length reply = some bit) :
    rank height (responseSuccessor height pref reply) + 1 =
      rank height (.q pref) := by
  simpa only [responseSuccessor, supported] using q_supported_rank bit bound

private theorem chronology_length (addresses : Nat → Address) (remaining epoch : Nat)
    (source : Source) :
    (chronology addresses remaining epoch source).length = 2 * remaining - 1 := by
  induction remaining generalizing epoch source with
  | zero => simp [chronology]
  | succ remaining ih =>
      cases remaining with
      | zero => simp [chronology]
      | succ remaining =>
          simp only [chronology, List.length_cons]
          rw [ih]
          omega

private theorem chronology_updateCount (addresses : Nat → Address) (remaining epoch : Nat)
    (source : Source) :
    updateCount (chronology addresses remaining epoch source) = remaining - 1 := by
  induction remaining generalizing epoch source with
  | zero => simp [chronology, updateCount]
  | succ remaining ih =>
      cases remaining with
      | zero => simp [chronology, updateCount]
      | succ remaining =>
          simp only [chronology, updateCount]
          rw [ih]
          omega

private theorem chronology_readCount (addresses : Nat → Address) (remaining epoch : Nat)
    (source : Source) :
    readCount (chronology addresses remaining epoch source) = remaining := by
  induction remaining generalizing epoch source with
  | zero => simp [chronology, readCount]
  | succ remaining ih =>
      cases remaining with
      | zero => simp [chronology, readCount]
      | succ remaining =>
          simp only [chronology, readCount]
          rw [ih]

/-- The control table executes every certified decoded path exactly. -/
private theorem sparse_literal_control_run
    {height : Nat} {addresses : Nat → Address}
    {pref : List Bool} {epoch count : Nat} {source : Source}
    {bits : List Bool}
    (path : DecodedPath addresses epoch count source bits)
    (pref_epoch : pref.length = epoch)
    (height_bound : pref.length + count = height)
    (count_pos : 0 < count) :
    NativeSerialMachine.Run (controlProgram height addresses)
      (.q pref) epoch source (chronology addresses count epoch source)
      (pref ++ bits) := by
  induction path generalizing pref with
  | nil => omega
  | @cons epoch remaining source bit tail supported tailPath ih =>
      cases remaining with
      | zero =>
          cases tailPath
          have supported' :
              decodeBit pref.length (readout (addresses pref.length) source) =
                some bit := by
            simpa [pref_epoch] using supported
          have no_child : ¬ pref.length + 1 < height := by omega
          have next :
              responseSuccessor height pref
                  (readout (addresses pref.length) source) = .z (pref ++ [bit]) := by
            simp [responseSuccessor, supported', no_child]
          have stop : NativeSerialMachine.Run (controlProgram height addresses)
              (.z (pref ++ [bit])) epoch source [] (pref ++ [bit]) := by
            exact .stop rfl
          have read_step := NativeSerialMachine.Run.read
            (δ := controlProgram height addresses) (c := .q pref)
            (e := epoch) (r := source) (a := addresses pref.length)
            (k := responseSuccessor height pref)
            (y := readout (addresses pref.length) source) (t := [])
            (o := pref ++ [bit]) (by rfl) rfl (by simpa [next] using stop)
          simpa [chronology, pref_epoch] using read_step
      | succ remaining =>
          have supported' :
              decodeBit pref.length (readout (addresses pref.length) source) =
                some bit := by
            simpa [pref_epoch] using supported
          have child_pref : (pref ++ [bit]).length = epoch + 1 := by
            simp [pref_epoch]
          have child_bound :
              (pref ++ [bit]).length + (remaining + 1) = height := by
            simp [child_pref]
            omega
          have child_run := ih (pref := pref ++ [bit])
            (pref_epoch := child_pref) (height_bound := child_bound)
            (count_pos := by omega)
          have next :
              responseSuccessor height pref
                  (readout (addresses pref.length) source) =
                .u (pref ++ [bit]) := by
            have has_child : pref.length + 1 < height := by omega
            simp [responseSuccessor, supported', has_child]
          have update_run : NativeSerialMachine.Run (controlProgram height addresses)
              (.u (pref ++ [bit])) epoch source
              (.update epoch :: chronology addresses (remaining + 1) (epoch + 1)
                (substitution source))
              (pref ++ (bit :: tail)) := by
            have qrun : NativeSerialMachine.Run (controlProgram height addresses)
                (.q (pref ++ [bit])) (epoch + 1) (substitution source)
                (chronology addresses (remaining + 1) (epoch + 1)
                  (substitution source)) ((pref ++ [bit]) ++ tail) := by
              simpa [List.append_assoc] using child_run
            have upd := NativeSerialMachine.Run.update
              (δ := controlProgram height addresses)
              (c := .u (pref ++ [bit])) (c' := .q (pref ++ [bit]))
              (e := epoch) (r := source)
              (t := chronology addresses (remaining + 1) (epoch + 1)
                (substitution source)) (o := (pref ++ [bit]) ++ tail)
              (by rfl) qrun
            simpa [List.append_assoc] using upd
          have read_step := NativeSerialMachine.Run.read
            (δ := controlProgram height addresses) (c := .q pref)
            (e := epoch) (r := source) (a := addresses pref.length)
            (k := responseSuccessor height pref)
            (y := readout (addresses pref.length) source)
            (t := .update epoch :: chronology addresses (remaining + 1) (epoch + 1)
              (substitution source)) (o := pref ++ (bit :: tail))
            (by rfl) rfl (by simpa [next] using update_run)
          simpa [chronology, pref_epoch] using read_step

private theorem sparse_literal_control_genuine_update
    {source : Source} (epoch : Nat) :
    substitution^[epoch + 1] source ≠ substitution^[epoch] source := by
  intro equal
  have left :=
    D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.right_clock_iterate
      (epoch + 1) source
  have right :=
    D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.right_clock_iterate
      epoch source
  rw [equal] at left
  omega



open ActualLeafHistoryRigidity (subtree)
open DelayedOriginalReadout (rights rightClock)

/-- A literal is compiled once from its original address and its read position. -/
def queries (q : Nat → Address) (i : Nat) : Address := q i ++ rights (i / 2)

private theorem delayed_leaf_decode (epoch : Nat) (a : Address) (source : Source)
    (bit : Bool) (leaf : subtree a source = some (.of (!bit))) :
    decodeBit epoch (readout (a ++ rights (epoch / 2)) (substitution^[epoch] source)) =
      some bit := by
  have app := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨y, hy, hc⟩ := (DelayedOriginalReadout.address_clock_bounds epoch a source).1 _ leaf
  rw [app, hy]
  change decodeBit epoch (readout (rights (epoch / 2)) y) = some bit
  have intervals := DelayedOriginalReadout.right_clock_readout (epoch / 2) y
  have mod_lt := Nat.mod_lt epoch (by decide : 0 < 2)
  have div_eq := Nat.mod_add_div epoch 2
  cases bit <;> simp only [Bool.not_false, Bool.not_true, rightClock] at hc
  · by_cases even : epoch % 2 = 0
    · rw [intervals.2.1.mpr (by omega)]
      simp [decodeBit, even]
    · rw [intervals.2.2.1.mpr (by omega)]
      simp [decodeBit, even]
  · by_cases even : epoch % 2 = 0
    · rw [intervals.2.2.1.mpr (by omega)]
      simp [decodeBit, even]
    · rw [intervals.2.2.2.mpr (by omega)]
      simp [decodeBit, even]

private theorem original_decoded_path (q : Nat → Address) (source : Source)
    (bits : List Bool) (offset : Nat)
    (leaves : ∀ i (hi : i < bits.length),
      subtree (q (offset + i)) source = some (.of (Bool.not (bits[i])))) :
    DecodedPath (queries q) offset bits.length (substitution^[offset] source) bits := by
  induction bits generalizing offset with
  | nil => exact .nil _ _
  | cons b bs ih =>
      apply DecodedPath.cons
      · have first := leaves 0 (by simp)
        change subtree (q (offset + 0)) source = some (.of (Bool.not b)) at first
        exact delayed_leaf_decode offset (q offset) source b (by simpa using first)
      · rw [← Function.iterate_succ_apply' (f := (substitution : Source → Source))]
        apply ih
        intro i hi
        have next := leaves (i+1) (by simpa using hi)
        change subtree (q (offset + (i+1))) source = some (.of (Bool.not (bs[i]))) at next
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

/-- Exactly the Q, U and Z vertices specified by the finite table. -/
def Installed (height : Nat) : Control → Prop
  | .q s => s.length < height
  | .u s => 0 < s.length ∧ s.length < height
  | .z s => s.length = height

private theorem response_installed {height : Nat} {s : List Bool}
    (hs : s.length < height) (r : Reply) : Installed height (responseSuccessor height s r) := by
  unfold responseSuccessor
  cases decodeBit s.length r with
  | none => exact hs
  | some b =>
      split_ifs with h
      · simp only [Installed, List.length_append, List.length_singleton]
        exact ⟨by omega, h⟩
      · simp only [Installed, List.length_append, List.length_singleton]
        omega

private theorem installed_finite (height : Nat) : Set.Finite {c | Installed height c} := by
  let lists : Set (List Bool) := {s | s.length ≤ height}
  have finiteLists : lists.Finite := List.finite_length_le Bool height
  apply ((finiteLists.image Control.q).union
    ((finiteLists.image Control.u).union (finiteLists.image Control.z))).subset
  intro c hc
  cases c with
  | q s => exact Or.inl ⟨s, Nat.le_of_lt hc, rfl⟩
  | u s => exact Or.inr (Or.inl ⟨s, Nat.le_of_lt hc.2, rfl⟩)
  | z s => exact Or.inr (Or.inr ⟨s, Nat.le_of_eq hc, rfl⟩)

/-- Only members of the installed finite carrier have instruction rows. -/
abbrev Vertex (height : Nat) := {c : Control // Installed height c}

instance (height : Nat) : Finite (Vertex height) := (installed_finite height).to_subtype

/-- The executable finite table has total Read reply rows and no local actions. -/
def table (height : Nat) (q : Nat → Address) :
    Vertex height → NativeSerialMachine.Op (Vertex height) (List Bool)
  | ⟨.q s, hs⟩ => .read (queries q s.length)
      (fun r => ⟨responseSuccessor height s r, response_installed hs r⟩)
  | ⟨.u s, hs⟩ => .applyRho ⟨.q s, hs.2⟩
  | ⟨.z s, _⟩ => .stop s

private theorem restrict_run {height : Nat} {q : Nat → Address} {c : Control}
    {epoch : Nat} {source : Source} {trace : Trace} {out : List Bool}
    (run : NativeSerialMachine.Run (controlProgram height (queries q)) c epoch source trace out)
    (hc : Installed height c) :
    NativeSerialMachine.Run (table height q) ⟨c, hc⟩ epoch source trace out := by
  induction run with
  | @stop c e r o row =>
      cases c <;> simp only [controlProgram] at row
      case q s => cases row
      case u s => cases row
      case z s => cases row; exact .stop rfl
  | @localStep c c' e r t o row rest ih =>
      cases c <;> simp [controlProgram] at row
  | @update c c' e r t o row rest ih =>
      cases c <;> simp only [controlProgram] at row
      case q s => cases row
      case z s => cases row
      case u s =>
        cases row
        exact .update rfl (ih hc.2)
  | @read c e r a k y t o row response rest ih =>
      cases c <;> simp only [controlProgram] at row
      case u s => cases row
      case z s => cases row
      case q s =>
        cases row
        exact .read rfl response (ih (response_installed hc y))


/-- The source and epoch at a control, always referring to the same original tree. -/
def Support (bits : List Bool) (original : Source) (c : Control)
    (epoch : Nat) (current : Source) : Prop :=
  current = substitution^[epoch] original ∧
  match c with
  | .q s => s.IsPrefix bits ∧ epoch = s.length
  | .u s => s.IsPrefix bits ∧ epoch + 1 = s.length
  | .z x => x = bits ∧ epoch + 1 = bits.length

private theorem read_support (q : Nat → Address) (original : Source) (bits s : List Bool)
    (leaves : ∀ i (hi : i < bits.length), subtree (q i) original = some (.of (Bool.not (bits[i]))))
    (pref : s.IsPrefix bits) (bound : s.length < bits.length) :
    Support bits original
      (responseSuccessor bits.length s
        (readout (queries q s.length) (substitution^[s.length] original)))
      s.length (substitution^[s.length] original) ∧
    rank bits.length (responseSuccessor bits.length s
        (readout (queries q s.length) (substitution^[s.length] original))) + 1 =
      rank bits.length (.q s) := by
  obtain ⟨rest, rfl⟩ := pref
  cases rest with
  | nil => simp at bound
  | cons b rest =>
      have leaf : subtree (q s.length) original = some (.of (!b)) := by
        simpa using leaves s.length bound
      have decoded := delayed_leaf_decode s.length (q s.length) original b leaf
      change decodeBit s.length
        (readout (queries q s.length) (substitution^[s.length] original)) = some b at decoded
      refine ⟨?_, response_rank_step bound decoded⟩
      simp only [responseSuccessor, decoded]
      split_ifs with h
      · refine ⟨rfl, ?_, ?_⟩
        · exact ⟨rest, by simp⟩
        · simp
      · have empty : rest = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_append, List.length_cons] at h
          omega
        subst rest
        exact ⟨rfl, rfl, by simp⟩

private theorem update_support (bits s : List Bool) (original : Source)
    (nonempty : 0 < s.length) (bound : s.length < bits.length) (pref : s.IsPrefix bits) :
    Support bits original (.q s) s.length
      (substitution (substitution^[s.length-1] original)) ∧
    rank bits.length (.q s) + 1 = rank bits.length (.u s) ∧
    substitution (substitution^[s.length-1] original) ≠
      substitution^[s.length-1] original := by
  have next : substitution (substitution^[s.length-1] original) =
      substitution^[s.length] original := by
    rw [← Function.iterate_succ_apply' (f := (substitution : Source → Source))]
    congr 1
    omega
  refine ⟨⟨next, pref, rfl⟩, u_rank_step bound, ?_⟩
  simpa only [Function.iterate_succ_apply'] using
    (sparse_literal_control_genuine_update (source := original) (s.length-1))

/-- Exact native execution and the same-source support/rank certificate. -/
def Recovery (q : Nat → Address) (original : Source) (bits : List Bool)
    (positive : 0 < bits.length) : Prop :=
    Finite (Vertex bits.length) ∧
    NativeSerialMachine.Run (table bits.length q)
      ⟨.q [], positive⟩ 0 original (chronology (queries q) bits.length 0 original) bits ∧
    (chronology (queries q) bits.length 0 original).length = 2 * bits.length - 1 ∧
    readCount (chronology (queries q) bits.length 0 original) = bits.length ∧
    updateCount (chronology (queries q) bits.length 0 original) = bits.length - 1 ∧
    (∀ s, s.IsPrefix bits → s.length < bits.length →
      Support bits original (responseSuccessor bits.length s
        (readout (queries q s.length) (substitution^[s.length] original)))
        s.length (substitution^[s.length] original) ∧
      rank bits.length (responseSuccessor bits.length s
        (readout (queries q s.length) (substitution^[s.length] original))) + 1 =
        rank bits.length (.q s)) ∧
    (∀ s, s.IsPrefix bits → 0 < s.length → s.length < bits.length →
      Support bits original (.q s) s.length
        (substitution (substitution^[s.length-1] original)) ∧
      rank bits.length (.q s) + 1 = rank bits.length (.u s) ∧
      substitution (substitution^[s.length-1] original) ≠
        substitution^[s.length-1] original) ∧
    Support bits original (.q []) 0 original ∧
    Support bits original (.z bits) (bits.length-1) (substitution^[bits.length-1] original) ∧
    table bits.length q ⟨.z bits, rfl⟩ = .stop bits ∧
    (∀ (c : Vertex bits.length) out, table bits.length q c = .stop out → c.val = .z out) ∧
    (∀ s r, decodeBit s.length r = none → responseSuccessor bits.length s r = .q s)

private theorem original_recovery (q : Nat → Address) (original : Source) (bits : List Bool)
    (positive : 0 < bits.length)
    (leaves : ∀ i (hi : i < bits.length),
      subtree (q i) original = some (.of (Bool.not (bits[i])))) :
    Recovery q original bits positive := by
  have decoded := original_decoded_path q original bits 0 (by simpa using leaves)
  have run := sparse_literal_control_run (height := bits.length) (pref := [])
    decoded rfl (by simp) positive
  have actual : NativeSerialMachine.Run (controlProgram bits.length (queries q))
      (.q []) 0 original (chronology (queries q) bits.length 0 original) bits := by
    simpa using run
  refine ⟨inferInstance, restrict_run actual positive, chronology_length _ _ _ _,
    chronology_readCount _ _ _ _, chronology_updateCount _ _ _ _,
    fun s hs hb => read_support q original bits s leaves hs hb,
    (fun s hs hp hb => update_support bits s original hp hb hs),
    ⟨rfl, by simp, rfl⟩, ⟨rfl, rfl, by omega⟩, rfl, ?_, ?_⟩
  · rintro ⟨c, hc⟩ out row
    cases c <;> simp only [table] at row
    case q s => cases row
    case u s => cases row
    case z s => cases row; rfl
  · intro s r hr
    simp [responseSuccessor, hr]


open NativeDepthPatterns (Frontier fill frontierAddress frontier_geometry)
open NativePolynomialDescriptorObstruction (fullPattern)

/-- Locate any length-d literal in the complete binary skeleton. -/
def fullIndex : (depth : Nat) → (a : Address) → a.length = depth → Frontier (fullPattern depth)
  | 0, [], _ => ()
  | 0, _ :: _, impossible => False.elim (by simp at impossible)
  | _ + 1, [], impossible => False.elim (by simp at impossible)
  | depth + 1, false :: rest, h => .inl (fullIndex depth rest (Nat.succ.inj h))
  | depth + 1, true :: rest, h => .inr (fullIndex depth rest (Nat.succ.inj h))

theorem full_index_address (depth : Nat) (a : Address) (h : a.length = depth) :
    frontierAddress (fullPattern depth) (fullIndex depth a h) = a := by
  induction depth generalizing a with
  | zero => cases a with
    | nil => rfl
    | cons b a => simp at h
  | succ depth ih => cases a with
    | nil => simp at h
    | cons b a =>
      cases b <;> simp only [fullIndex, fullPattern, frontierAddress, ih]

/-- A chosen original leaf has the corresponding independent bit; every other
leaf is alpha. Numerical false/true means alpha/beta, respectively. -/
noncomputable def familyLabel (q : Nat → Address) (bits : List Bool) (a : Address) : Bool :=
  if found : ∃ i : Fin bits.length, q i = a then Bool.not (bits[found.choose]) else true

/-- The complete depth-d source with independent labels at the selected literals. -/
noncomputable def familySource (depth : Nat) (q : Nat → Address) (bits : List Bool) : Source :=
  fill (fullPattern depth) (fun j => .of (familyLabel q bits (frontierAddress _ j)))

private theorem family_leaf (depth : Nat) (q : Nat → Address) (bits : List Bool)
    (lengths : ∀ i < bits.length, (q i).length = depth)
    (distinct : Function.Injective (fun i : Fin bits.length => q i))
    (i : Nat) (hi : i < bits.length) :
    subtree (q i) (familySource depth q bits) = some (.of (Bool.not (bits[i]))) := by
  have index := full_index_address depth (q i) (lengths i hi)
  have geometry := (frontier_geometry depth (fullPattern depth)).2.1
    (fun j => .of (familyLabel q bits (frontierAddress _ j)))
    (fullIndex depth (q i) (lengths i hi))
  simp only [index] at geometry
  change subtree (q i) (familySource depth q bits) =
    some (.of (familyLabel q bits (q i))) at geometry
  rw [geometry]
  have found : ∃ j : Fin bits.length, q j = q i := ⟨⟨i, hi⟩, rfl⟩
  rw [familyLabel, dif_pos found]
  have same : found.choose = ⟨i, hi⟩ := distinct found.choose_spec
  simp only [same]
  rfl

/-- Construction 3.2 for every selected order and every independent bit vector.
The depth is arbitrary, hence includes the prescribed ceiling-logarithm depth
and the root-only height-one boundary. No decoded-path premise is required. -/
theorem complete_skeleton_recovery (depth : Nat) (q : Nat → Address) (bits : List Bool)
    (positive : 0 < bits.length)
    (lengths : ∀ i < bits.length, (q i).length = depth)
    (distinct : Function.Injective (fun i : Fin bits.length => q i)) :
    Recovery q (familySource depth q bits) bits positive := by
  exact original_recovery q _ bits positive (family_leaf depth q bits lengths distinct)

end D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralControlTable

namespace D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeDepthPatterns (Frontier fill frontierAddress frontier_geometry)
open NativePolynomialDescriptorObstruction (fullPattern)
open NativeSerialMachine (Op Event Trace Run reads)
open scoped BigOperators

/-- The original target is the parity bit of all selected independent labels. -/
def parity {h : Nat} (x : Fin h → Bool) : Bool :=
  decide ((∑ i, (x i).toNat) % 2 = 1)

/-- The numerical original bit is zero at every unselected skeleton leaf. -/
noncomputable def assigned {h depth : Nat} (slots : Fin h → Frontier (fullPattern depth))
    (x : Fin h → Bool) (j : Frontier (fullPattern depth)) : Bool :=
  if found : ∃ i, slots i = j then x found.choose else false

/-- All selected labels vary independently on the same complete original skeleton. -/
noncomputable def source {h depth : Nat} (slots : Fin h → Frontier (fullPattern depth))
    (x : Fin h → Bool) : Source :=
  fill (fullPattern depth) (fun j => .of (!(assigned slots x j)))

theorem parity_flip {h : Nat} (x : Fin h → Bool) (i : Fin h) :
    parity (Function.update x i (!(x i))) ≠ parity x := by
  let base := ∑ j ∈ Finset.univ.erase i, (x j).toNat
  have old : (∑ j, (x j).toNat) = base + (x i).toNat :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  have new : (∑ j, ((Function.update x i (!(x i))) j).toNat) = base + (!(x i)).toNat := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hm := Nat.mod_lt base (by decide : 0 < 2)
  have cases_mod : base % 2 = 0 ∨ base % 2 = 1 := by omega
  unfold parity
  rw [new, old]
  rcases cases_mod with hm0 | hm1
  · have hs : (base+1)%2 = 1 := by omega
    cases x i <;> simp [hm0, hs]
  · have hs : (base+1)%2 = 0 := by omega
    cases x i <;> simp [hm1, hs]

private theorem assigned_off_slot {h depth : Nat}
    (slots : Fin h → Frontier (fullPattern depth)) (x : Fin h → Bool)
    (i : Fin h) (j : Frontier (fullPattern depth)) (ne : j ≠ slots i) :
    assigned slots (Function.update x i (!(x i))) j = assigned slots x j := by
  classical
  unfold assigned
  split_ifs with found
  · have choice_ne : found.choose ≠ i := by
      intro same
      exact ne (same ▸ found.choose_spec).symm
    exact Function.update_of_ne choice_ne _ _
  · rfl

private theorem full_readout_local (depth : Nat)
    (f g : Frontier (fullPattern depth) → Source) (a : Address) (epoch : Nat)
    (same : ∀ j, (frontierAddress (fullPattern depth) j).IsPrefix a → f j = g j) :
    readout a (substitution^[epoch] (fill (fullPattern depth) f)) =
      readout a (substitution^[epoch] (fill (fullPattern depth) g)) := by
  induction depth generalizing a with
  | zero =>
      have eq := same () (by simp [frontierAddress])
      simpa only [fullPattern, fill] using congrArg (fun z => readout a (substitution^[epoch] z)) eq
  | succ depth ih =>
      have rho (s t : Source) : substitution^[epoch] (.mul s t) =
          .mul (substitution^[epoch] s) (substitution^[epoch] t) :=
        Function.Semiconj₂.iterate
          (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
            fun s t => substitution.map_mul s t) epoch s t
      simp only [fullPattern, fill, rho]
      cases a with
      | nil => rfl
      | cons b a =>
          cases b
          · apply ih (fun j => f (.inl j)) (fun j => g (.inl j)) a
            intro j hj
            exact same (.inl j) (by simpa [fullPattern, frontierAddress] using hj)
          · apply ih (fun j => f (.inr j)) (fun j => g (.inr j)) a
            intro j hj
            exact same (.inr j) (by simpa [fullPattern, frontierAddress] using hj)

private theorem off_cone_reply {h depth : Nat}
    (slots : Fin h → Frontier (fullPattern depth)) (x : Fin h → Bool) (i : Fin h)
    (a : Address) (epoch : Nat)
    (outside : ¬ (frontierAddress (fullPattern depth) (slots i)).IsPrefix a) :
    readout a (substitution^[epoch] (source slots (Function.update x i (!(x i))))) =
      readout a (substitution^[epoch] (source slots x)) := by
  apply full_readout_local
  intro j hj
  have ne : j ≠ slots i := by
    intro eq
    exact outside (eq ▸ hj)
  rw [assigned_off_slot slots x i j ne]

private theorem replay_avoiding {C O : Type} {δ : C → Op C O}
    {c : C} {epoch : Nat} {u : Source} {trace : Trace} {out : O}
    (run : Run δ c epoch (substitution^[epoch] u) trace out)
    (v : Source)
    (same : ∀ e a r, Event.read e a r ∈ trace →
      readout a (substitution^[e] v) = readout a (substitution^[e] u)) :
    Run δ c epoch (substitution^[epoch] v) trace out := by
  obtain ⟨_, _, _, _, _, truth⟩ :=
    NativeSerialMachine.actual_register_execution δ run u rfl []
  exact NativeSerialDepth.transfer run u v rfl
    (fun e a r hr => (same e a r hr).trans (truth e a r hr))

private theorem cone_must_be_read {h depth : Nat} {C : Type}
    (slots : Fin h → Frontier (fullPattern depth)) (δ : C → Op C Bool) (start : C)
    (sound : ∀ x t out, Run δ start 0 (source slots x) t out → out = parity x)
    (x : Fin h → Bool) (trace : Trace) (out : Bool)
    (run : Run δ start 0 (source slots x) trace out) (i : Fin h) :
    ∃ e a r, Event.read e a r ∈ trace ∧
      (frontierAddress (fullPattern depth) (slots i)).IsPrefix a := by
  classical
  by_contra missing
  have avoid : ∀ e a r, Event.read e a r ∈ trace →
      ¬ (frontierAddress (fullPattern depth) (slots i)).IsPrefix a := by
    intro e a r hr hp
    exact missing ⟨e,a,r,hr,hp⟩
  have second : Run δ start 0 (source slots (Function.update x i (!(x i)))) trace out := by
    exact replay_avoiding (u := source slots x) run
      (source slots (Function.update x i (!(x i))))
      (fun e a r hr => off_cone_reply slots x i a e (avoid e a r hr))
  exact parity_flip x i ((sound _ _ _ second).symm.trans (sound _ _ _ run))

private theorem read_event_mem {trace : Trace} {e : Nat} {a : Address} {r : Reply}
    (mem : Event.read e a r ∈ trace) : (e,a,r) ∈ reads trace := by
  induction trace with
  | nil => simp at mem
  | cons event trace ih =>
      rcases List.mem_cons.mp mem with eq | later
      · subst event
        simp [reads]
      · cases event <;> simp only [reads]
        · exact ih later
        · exact ih later
        · exact List.mem_cons_of_mem _ (ih later)

/-- Every independent original cone has its own actual read occurrence. The
controller may perform arbitrary finite local computation, choose arbitrary
literal depths and update adaptively; only sound terminating runs are required. -/
theorem parity_read_lower_bound {h depth : Nat} {C : Type}
    (slots : Fin h → Frontier (fullPattern depth))
    (distinct : Function.Injective (fun i => frontierAddress (fullPattern depth) (slots i)))
    (δ : C → Op C Bool) (start : C)
    (sound : ∀ x t out, Run δ start 0 (source slots x) t out → out = parity x)
    (x : Fin h → Bool) (trace : Trace) (out : Bool)
    (run : Run δ start 0 (source slots x) trace out) :
    h ≤ (reads trace).length ∧
    ∀ i : Fin h, ∃ e a r, Event.read e a r ∈ trace ∧
      (frontierAddress (fullPattern depth) (slots i)).IsPrefix a := by
  classical
  have cover := cone_must_be_read slots δ start sound x trace out run
  have witness (i : Fin h) : ∃ j : Fin (reads trace).length,
      (frontierAddress (fullPattern depth) (slots i)).IsPrefix ((reads trace).get j).2.1 := by
    obtain ⟨e,a,r,hr,hp⟩ := cover i
    obtain ⟨j,hj⟩ := List.get_of_mem (read_event_mem hr)
    exact ⟨j, by rw [hj]; exact hp⟩
  choose select selected using witness
  have inj : Function.Injective select := by
    intro i j eq
    apply distinct
    have hi := selected i
    have hj := selected j
    rw [eq] at hi
    have lengths := (frontier_geometry depth (fullPattern depth)).1
    exact (List.prefix_of_prefix_length_le hi hj (by rw [lengths, lengths])).eq_of_length
      (by rw [lengths, lengths])
  exact ⟨by simpa using Fintype.card_le_of_injective select inj, cover⟩


private theorem read_row {C O : Type} {δ : C → Op C O}
    {c : C} {epoch : Nat} {u : Source} {trace : Trace} {out : O}
    (run : Run δ c epoch u trace out) {e : Nat} {a : Address} {r : Reply}
    (mem : Event.read e a r ∈ trace) : ∃ state k, δ state = .read a k := by
  induction run with
  | stop row => simp at mem
  | localStep row tail ih => exact ih (by simpa using mem)
  | update row tail ih => exact ih (by simpa using mem)
  | @read c e u b k y t o row reply tail ih =>
      rcases List.mem_cons.mp mem with eq | later
      · cases eq
        exact ⟨c,k,row⟩
      · exact ih later

/-- The fixed literal and fixed output rows require h different query states and
both parity halts, irrespective of adaptive epochs and repeated visits. -/
private theorem parity_control_lower_bound {h depth : Nat} {C : Type} [Fintype C]
    (positive : 0 < h) (slots : Fin h → Frontier (fullPattern depth))
    (distinct : Function.Injective (fun i => frontierAddress (fullPattern depth) (slots i)))
    (δ : C → Op C Bool) (start : C)
    (sound : ∀ x t out, Run δ start 0 (source slots x) t out → out = parity x)
    (total : ∀ x, ∃ t out, Run δ start 0 (source slots x) t out) :
    h + 2 ≤ Fintype.card C ∧
    (∀ x trace out, Run δ start 0 (source slots x) trace out → h ≤ (reads trace).length) ∧
    ∀ (width : Nat) (encode : C → {w : Fin width → Bool //
      D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm width w}),
      Function.Injective encode → h + 2 ≤ Nat.fib (width + 2) := by
  classical
  obtain ⟨trace,out,run⟩ := total (fun _ => false)
  have covered := (parity_read_lower_bound slots distinct δ start sound _ trace out run).2
  have queries (i : Fin h) : ∃ c a k, δ c = .read a k ∧
      (frontierAddress (fullPattern depth) (slots i)).IsPrefix a := by
    obtain ⟨e,a,r,hr,hp⟩ := covered i
    obtain ⟨c,k,row⟩ := read_row run hr
    exact ⟨c,a,k,row,hp⟩
  choose query address continuation rows cones using queries
  have query_inj : Function.Injective query := by
    intro i j eq
    have ae : address i = address j :=
      (Op.read.inj ((rows i).symm.trans ((congrArg δ eq).trans (rows j)))).1
    apply distinct
    have hi := cones i
    rw [ae] at hi
    have lengths := (frontier_geometry depth (fullPattern depth)).1
    exact (List.prefix_of_prefix_length_le hi (cones j) (by rw [lengths, lengths])).eq_of_length
      (by rw [lengths, lengths])
  have target (b : Bool) : ∃ x : Fin h → Bool, parity x = b := by
    cases b
    · exact ⟨fun _ => false, by simp [parity]⟩
    · let zero : Fin h → Bool := fun _ => false
      have flipped := parity_flip zero ⟨0,positive⟩
      have pzero : parity zero = false := by simp [parity, zero]
      refine ⟨Function.update zero ⟨0,positive⟩ true, ?_⟩
      rw [pzero] at flipped
      change parity (Function.update zero ⟨0,positive⟩ true) ≠ false at flipped
      cases he : parity (Function.update zero ⟨0,positive⟩ true) <;> simp_all
  have halted (b : Bool) : ∃ c, δ c = .stop b := by
    obtain ⟨x,hx⟩ := target b
    obtain ⟨t,o,execution⟩ := total x
    obtain ⟨c,e,_,_,row,_⟩ := NativeSerialMachine.actual_register_execution δ execution
      (source slots x) (by simp) []
    exact ⟨c, by simpa [sound x t o execution, hx] using row⟩
  choose halt halt_row using halted
  let inject : Fin h ⊕ Bool → C := Sum.elim query halt
  have inj : Function.Injective inject := by
    intro a b eq
    cases a with
    | inl i => cases b with
      | inl j => exact congrArg Sum.inl (query_inj eq)
      | inr b =>
        have bad := (rows i).symm.trans ((congrArg δ eq).trans (halt_row b))
        cases bad
    | inr a => cases b with
      | inl j =>
        have bad := (halt_row a).symm.trans ((congrArg δ eq).trans (rows j))
        cases bad
      | inr b =>
        exact congrArg Sum.inr (Op.stop.inj
          ((halt_row a).symm.trans ((congrArg δ eq).trans (halt_row b))))
  have card_bound : h + 2 ≤ Fintype.card C := by
    simpa using Fintype.card_le_of_injective inject inj
  refine ⟨card_bound, (fun x t o execution =>
    (parity_read_lower_bound slots distinct δ start sound x t o execution).1), ?_⟩
  intro width encode faithful
  have capacity := Fintype.card_le_of_injective encode faithful
  rw [D5.S1.Words.AdmissibleWords.AdmissibleCount.admissibleWord_card_eq_fib] at capacity
  exact card_bound.trans capacity


/-- The prescribed distinct length-d literals, in their given order. -/
def sourceSlots {h : Nat} (depth : Nat) (q : Fin h → Address)
    (lengths : ∀ i, (q i).length = depth) : Fin h → Frontier (fullPattern depth) :=
  fun i => SparseLiteralControlTable.fullIndex depth (q i) (lengths i)

/-- Original sources with free labels at exactly the prescribed literals. -/
noncomputable def originalSource {h : Nat} (depth : Nat) (q : Fin h → Address)
    (lengths : ∀ i, (q i).length = depth) (x : Fin h → Bool) : Source :=
  source (sourceSlots depth q lengths) x

/-- Theorem 8.2's acquisition and complete-memory lower bounds, with the original
literal family and arbitrary adaptive serial controllers. Every selected
original label is realized; every nonselected skeleton leaf is alpha. -/
theorem literal_parity_lower_bounds {h depth : Nat} {C : Type} [Fintype C]
    (positive : 0 < h) (q : Fin h → Address) (lengths : ∀ i, (q i).length = depth)
    (distinct : Function.Injective q) (δ : C → Op C Bool) (start : C)
    (sound : ∀ x t out, Run δ start 0 (originalSource depth q lengths x) t out → out = parity x)
    (total : ∀ x, ∃ t out, Run δ start 0 (originalSource depth q lengths x) t out) :
    (∀ x i, ActualLeafHistoryRigidity.subtree (q i) (originalSource depth q lengths x) =
      some (.of (!(x i)))) ∧
    (∀ x j, (∀ i, frontierAddress (fullPattern depth) j ≠ q i) →
      ActualLeafHistoryRigidity.subtree (frontierAddress (fullPattern depth) j)
        (originalSource depth q lengths x) = some (.of true)) ∧
    h + 2 ≤ Fintype.card C ∧
    (∀ x trace out, Run δ start 0 (originalSource depth q lengths x) trace out →
      h ≤ (reads trace).length) ∧
    ∀ (width : Nat) (encode : C → {w : Fin width → Bool //
      D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm width w}),
      Function.Injective encode → h + 2 ≤ Nat.fib (width + 2) := by
  classical
  let slots := sourceSlots depth q lengths
  have addresses (i : Fin h) : frontierAddress (fullPattern depth) (slots i) = q i :=
    SparseLiteralControlTable.full_index_address depth (q i) (lengths i)
  have slot_inj : Function.Injective slots := by
    intro i j eq
    apply distinct
    rw [← addresses i, ← addresses j, eq]
  have address_inj : Function.Injective
      (fun i => frontierAddress (fullPattern depth) (slots i)) := by
    simpa only [addresses] using distinct
  refine ⟨?_, ?_, parity_control_lower_bound positive slots address_inj δ start sound total⟩
  · intro x i
    have found : ∃ j, slots j = slots i := ⟨i,rfl⟩
    have chosen : found.choose = i := slot_inj found.choose_spec
    change ActualLeafHistoryRigidity.subtree (q i)
      (fill (fullPattern depth) (fun j => .of (!(assigned slots x j)))) = _
    rw [← addresses i, (frontier_geometry depth (fullPattern depth)).2.1]
    simp only [assigned, dif_pos found, chosen]
  · intro x j missing
    have none : ¬ ∃ i, slots i = j := by
      rintro ⟨i,hi⟩
      apply missing i
      rw [← hi, addresses]
    change ActualLeafHistoryRigidity.subtree (frontierAddress (fullPattern depth) j)
      (fill (fullPattern depth) (fun j => .of (!(assigned slots x j)))) = _
    rw [(frontier_geometry depth (fullPattern depth)).2.1]
    simp only [assigned, dif_neg none, Bool.not_false]

end D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound
