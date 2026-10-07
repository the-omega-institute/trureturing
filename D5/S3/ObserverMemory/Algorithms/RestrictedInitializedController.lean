/- GID: D5/S3/ObserverMemory/Algorithms/RestrictedInitializedController
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/RestrictedInitializedController
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Restricted endpoint states realize exact operational first-rewrite dynamics. -/

import D5.S3.ObserverMemory.Algorithms.InitializedControllerCapacity
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.FieldTheory.Finiteness
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.RestrictedInitializedController

open D5.S3.ObserverMemory.Algorithms.InitializedControlProtocol
open D5.S3.ObserverMemory.Algorithms.ControlRewriteDirectionalBound
open D5.S3.ObserverMemory.Algorithms.FixedSplitRewriteBudget
open D5.S3.ObserverMemory.Algorithms.InitializedControllerCapacity
open D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Prediction.ActionGraphCommunicationBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
attribute [local instance] Classical.propDecidable

/-- A known local control is compatible with some original remote projection. -/
abbrev Known {d : Nat} (S T : Submodule (ZMod 2) (Source d)) :=
  {aq : S × ZMod 2 // ∃ b : T,
    aq.2 = controlRestriction S aq.1 + controlRestriction T b}

/-- The unknown copy and precisely the compatible known copy are disjoint. -/
abbrev Local {d : Nat} (S T : Submodule (ZMod 2) (Source d)) := S ⊕ Known S T

/-- The fixed original local projection is the readout in either mode. -/
def localRead {d : Nat} {S T : Submodule (ZMod 2) (Source d)} : Local S T → S
  | .inl a => a
  | .inr aq => aq.val.1

/-- The synchronized mode is persistent local state, including on a control owner. -/
def localMode {d : Nat} {S T : Submodule (ZMod 2) (Source d)} : Local S T → Bool
  | .inl _ => false
  | .inr _ => true

/-- Only known states provide a stored current control. -/
def localControl {d : Nat} {S T : Submodule (ZMod 2) (Source d)} : Local S T → ZMod 2
  | .inl _ => 0
  | .inr aq => aq.val.2

/-- This mathematical encoding certifies compatibility; it is not an executor. -/
noncomputable def knownLocal {d : Nat} {S T : Submodule (ZMod 2) (Source d)}
    (split : IsCompl S T) (z : Source d) : Local S T :=
  .inr ⟨(S.projectionOnto T split z, z.2),
    T.projectionOnto S split.symm z, by
      have h := congrArg Prod.snd (Submodule.projection_add_projection_eq_self split z)
      exact h.symm⟩

/-- A public translation increments only the local projection and stored control. -/
noncomputable def translateLocal {d : Nat} {S T : Submodule (ZMod 2) (Source d)}
    (split : IsCompl S T) (t : Source d) : Local S T → Local S T
  | .inl a => .inl (a + S.projectionOnto T split t)
  | .inr aq => .inr ⟨(aq.val.1 + S.projectionOnto T split t, aq.val.2 + t.2), by
      obtain ⟨b, hb⟩ := aq.property
      refine ⟨b + T.projectionOnto S split.symm t, ?_⟩
      have ht := congrArg Prod.snd (Submodule.projection_add_projection_eq_self split t)
      change controlRestriction S (S.projectionOnto T split t) +
        controlRestriction T (T.projectionOnto S split.symm t) = t.2 at ht
      rw [map_add, map_add, hb, ← ht]
      abel⟩

/-- A locally computed rewrite scalar gives a known-control-zero local successor. -/
noncomputable def resetLocal {d : Nat} {S T : Submodule (ZMod 2) (Source d)}
    (split : IsCompl S T) (i : Fin d) (q : ZMod 2) : Local S T :=
  knownLocal split (Pi.single i q, 0)

/-- Lift the existing fixed exchange's questions to old persistent local readouts. -/
def liftQuestion {d : Nat} {A B : Submodule (ZMod 2) (Source d)} :
    Question A B → Question (Local A B) (Local B A)
  | .inl f => .inl (fun m => f (localRead m))
  | .inr f => .inr (fun m => f (localRead m))

/-- This map preserves the paid Boolean transcript while reconstructing local labels. -/
def liftTrace {d : Nat} {A B : Submodule (ZMod 2) (Source d)}
    (t : Trace A B) : Trace (Local A B) (Local B A) :=
  t.map (fun e => ⟨liftQuestion e.1, e.2⟩)

/-- The endpoint-local implementation. Unknown rewrites use the established
exchange node policy; all translations and known rewrites select a leaf.
Every rewrite writes known control zero, even if the exchange sends no bits. -/
noncomputable def endpointProtocol {d : Nat} {A B : Submodule (ZMod 2) (Source d)}
    (split : IsCompl A B) (f : Action d) (known : Bool) :
    EndpointProtocol (Local A B) (Local B A) (Local A B) (Local B A) := by
  classical
  let ellA := controlRestriction A
  let ellB := controlRestriction B
  let pA := A.projectionOnto B split
  let pB := B.projectionOnto A split.symm
  match f with
  | .dataTranslation i => exact {
      node := fun _ => .inr ()
      outA := fun a _ => translateLocal split (Pi.single i 1, 0) a
      outB := fun b _ => translateLocal split.symm (Pi.single i 1, 0) b }
  | .controlTranslation => exact {
      node := fun _ => .inr ()
      outA := fun a _ => translateLocal split (0, 1) a
      outB := fun b _ => translateLocal split.symm (0, 1) b }
  | .rewrite i =>
      let alpha := pA (Pi.single i 1, 0)
      let beta := pB (Pi.single i 1, 0)
      let original := rewriteProtocol ellA ellB alpha beta
      exact {
        node := fun h => if known then .inr () else
          match original.node h with
          | .inl q => .inl (liftQuestion q)
          | .inr u => .inr u
        outA := fun a h => resetLocal split i (if known then localControl a else
          if alpha = 0 then 0 else
            ellA (localRead a) + if ellB = 0 then 0 else
              if h[0]?.getD false then 1 else 0)
        outB := fun b h => resetLocal split.symm i (if known then localControl b else
          if beta = 0 then 0 else
            ellB (localRead b) + if ellA = 0 then 0 else
              if h[if alpha ≠ 0 ∧ ellB ≠ 0 then 1 else 0]?.getD false then 1 else 0) }

/-- Local preparation, local mode selection, and the actual sender-local protocols. -/
noncomputable def data {d : Nat} {A B : Submodule (ZMod 2) (Source d)}
    (split : IsCompl A B) : ControllerData d A B (Local A B) (Local B A) Bool := {
  readA := localRead
  readB := localRead
  initA := Sum.inl
  initB := Sum.inl
  read_initA := fun _ => rfl
  read_initB := fun _ => rfl
  rootA := fun _ => localMode
  rootB := fun _ => localMode
  protocol := endpointProtocol split }

/-- The proposed two-layer image is a proof-level representation of local pairs. -/
noncomputable def encode {d : Nat} {A B : Submodule (ZMod 2) (Source d)}
    (split : IsCompl A B) (known : Bool) (z : Source d) : Local A B × Local B A :=
  if known then (knownLocal split z, knownLocal split.symm z)
  else (.inl (A.projectionOnto B split z), .inl (B.projectionOnto A split.symm z))

/-- Every rewrite sets known mode, independently of its bit cost. -/
def nextMode {d : Nat} (known : Bool) : Action d → Bool
  | .rewrite _ => true
  | _ => known

/-- The source-specific edge charge reads the persistent mode and action. -/
noncomputable def protocolCharge {d : Nat} {A B : Submodule (ZMod 2) (Source d)}
    (split : IsCompl A B) (known : Bool) : Action d → Nat
  | .rewrite i => if known then 0 else splitCost split i
  | _ => 0

/-- First rewrite refers to its action label, including a zero-cost rewrite. -/
noncomputable def firstRewriteCost {d : Nat} {A B : Submodule (ZMod 2) (Source d)}
    (split : IsCompl A B) : List (Action d) → Nat
  | [] => 0
  | .rewrite i :: _ => splitCost split i
  | _ :: word => firstRewriteCost split word

/-- A genuine basis-translation word contains no rewrite. -/
def TranslationWord {d : Nat} (word : List (Action d)) : Prop :=
  ∀ f ∈ word, match f with | .rewrite _ => False | _ => True

/-- An actual fixed-width encoding is injective on the entire persistent carrier. -/
def BinaryEncoding (M : Type*) (k : Nat) : Prop := Nonempty (M ↪ (Fin k → Bool))

/-- One row evaluates the same controller's fibers, capacities, logarithmic
storage, separate endpoint widths, total fixed width, and uniform budget. -/
def StorageRow {d : Nat} {A B : Submodule (ZMod 2) (Source d)}
    (split : IsCompl A B) (fA fB tA tB logFactor overhead budget : Nat) : Prop :=
  let r := Module.finrank (ZMod 2) A
  let s := Module.finrank (ZMod 2) B
  (∀ a : A, Nat.card {m : Local A B // localRead m = a} = fA) ∧
  (∀ b : B, Nat.card {m : Local B A // localRead m = b} = fB) ∧
  Nat.card (Local A B) = fA * 2 ^ r ∧ Nat.card (Local B A) = fB * 2 ^ s ∧
  Real.logb 2 (Nat.card (Local A B)) + Real.logb 2 (Nat.card (Local B A)) =
    (d + 1 : Nat) + Real.logb 2 logFactor ∧
  Nat.clog 2 (Nat.card (Local A B)) = r + tA ∧
  Nat.clog 2 (Nat.card (Local B A)) = s + tB ∧
  ⌈Real.logb 2 (Nat.card (Local A B))⌉₊ = r + tA ∧
  ⌈Real.logb 2 (Nat.card (Local B A))⌉₊ = s + tB ∧
  ⌈Real.logb 2 (Nat.card (Local A B))⌉₊ +
    ⌈Real.logb 2 (Nat.card (Local B A))⌉₊ = d + overhead ∧ Cstar split = budget

universe u v w
/-- Universal bounds retain arbitrary carriers. Real logarithms are compared
only when both competing local carriers are finite. Finite encodings themselves
exclude infinite carriers. Centralized joint encoding is a separate resource. -/
def StorageOptimal {d : Nat} {A B : Submodule (ZMod 2) (Source d)}
    {split : IsCompl A B} (C : Controller split (Local A B) (Local B A) Bool) : Prop :=
  IsLeast {k | BinaryEncoding (Local A B) k} (Nat.clog 2 (Nat.card (Local A B))) ∧
  IsLeast {k | BinaryEncoding (Local B A) k} (Nat.clog 2 (Nat.card (Local B A))) ∧
  IsLeast {k | BinaryEncoding C.State k} (d + 2) ∧
  Real.logb 2 (Nat.card C.State) = (d + 2 : Nat) ∧
  (∀ {MA : Type u} {MB : Type v} {Root : Type w} (C' : Controller split MA MB Root)
    (K : Nat), UniformCumulativeBudget C' K →
    (∀ a : A, Nonempty (Fin (Nat.card {m : Local A B // localRead m = a}) ↪
      {m : MA // C'.readA m = a})) ∧
    (∀ b : B, Nonempty (Fin (Nat.card {m : Local B A // localRead m = b}) ↪
      {m : MB // C'.readB m = b})) ∧
    Nonempty (Fin (Nat.card (Local A B)) ↪ MA) ∧
    Nonempty (Fin (Nat.card (Local B A)) ↪ MB) ∧
    Nonempty (Fin (Nat.card C.State) ↪ C'.State) ∧
    (Finite MA → Finite MB →
      Real.logb 2 (Nat.card (Local A B)) + Real.logb 2 (Nat.card (Local B A)) ≤
        Real.logb 2 (Nat.card MA) + Real.logb 2 (Nat.card MB) ∧
      ⌈Real.logb 2 (Nat.card (Local A B))⌉₊ +
        ⌈Real.logb 2 (Nat.card (Local B A))⌉₊ ≤
        ⌈Real.logb 2 (Nat.card MA)⌉₊ + ⌈Real.logb 2 (Nat.card MB)⌉₊) ∧
    (∀ kA kB, BinaryEncoding MA kA → BinaryEncoding MB kB →
      Nat.clog 2 (Nat.card (Local A B)) ≤ kA ∧
      Nat.clog 2 (Nat.card (Local B A)) ≤ kB) ∧
    (∀ k, BinaryEncoding C'.State k → d + 2 ≤ k) ∧ Cstar split ≤ K) ∧
  Module.finrank (ZMod 2) A + Module.finrank (ZMod 2) B = d + 1 ∧
  (controlRestriction A ≠ 0 ∨ controlRestriction B ≠ 0) ∧
  (controlRestriction A = 0 → controlRestriction B ≠ 0 →
    StorageRow split 3 2 2 1 6 4 1) ∧
  (controlRestriction B = 0 → controlRestriction A ≠ 0 →
    StorageRow split 2 3 1 2 6 4 1) ∧
  (controlRestriction A ≠ 0 → controlRestriction B ≠ 0 →
    StorageRow split 3 3 2 2 9 5 2)

set_option maxHeartbeats 1000000 in
-- Evaluator lifting, operational reachability and word invariance share one proof.
/-- The restricted local implementation is a compliant initialized controller.
Its support is exactly the two operationally reached layers. Every known source
is obtained by rewriting initialized zero and a genuine basis-translation word.
All original action words preserve source readouts and pay exactly their first
rewrite, including a first rewrite whose cost is zero. The proved support gives
exact fiber, local and joint capacities. This same witness attains the least
uniform cumulative budget, finite logarithmic storage, separate endpoint widths
and centralized joint width, with universal arbitrary-carrier lower bounds and
all three control-allocation resource rows. -/
theorem restricted_initialized_controller (d : Nat) (hd : 2 ≤ d)
    (A B : Submodule (ZMod 2) (Source d)) (split : IsCompl A B)
    (hA : 0 < Module.finrank (ZMod 2) A) (hB : 0 < Module.finrank (ZMod 2) B) :
    ∃ C : Controller split (Local A B) (Local B A) Bool,
      C.toControllerData = data split ∧
      (∀ m, (data split).Reachable m ↔ ∃ k z, m = encode split k z) ∧
      (∀ k z f t, (data split).Exec f (encode split k z) t →
        (data split).commit f (encode split k z) t =
          encode split (nextMode k f) (f.apply z) ∧
        t.length = protocolCharge split k f) ∧
      (∀ z, ∃ i : Fin d, ∃ word, TranslationWord word ∧
        (runWord C.step (.rewrite i :: word) (C.initial 0 0)).val = encode split true z) ∧
      (∀ z word,
        C.readout (runWord C.step word
          (C.initial (A.projectionOnto B split z)
            (B.projectionOnto A split.symm z))) = runWord Action.apply word z ∧
        Comm C.step C.cost
          (C.initial (A.projectionOnto B split z)
            (B.projectionOnto A split.symm z)) word = firstRewriteCost split word) ∧
      UniformCumulativeBudget C (Cstar split) ∧
      (∀ a : A, Nat.card {m : Local A B // localRead m = a} =
        1 + 2 ^ Module.finrank (ZMod 2) (LinearMap.range (controlRestriction B))) ∧
      (∀ b : B, Nat.card {m : Local B A // localRead m = b} =
        1 + 2 ^ Module.finrank (ZMod 2) (LinearMap.range (controlRestriction A))) ∧
      Nat.card (Local A B) = (1 + 2 ^ Module.finrank (ZMod 2)
        (LinearMap.range (controlRestriction B))) * 2 ^ Module.finrank (ZMod 2) A ∧
      Nat.card (Local B A) = (1 + 2 ^ Module.finrank (ZMod 2)
        (LinearMap.range (controlRestriction A))) * 2 ^ Module.finrank (ZMod 2) B ∧
      Finite C.State ∧ Nat.card C.State = 2 ^ (d + 2) ∧
      IsLeast {K : Nat | ∃ (MA MB Root : Type) (C' : Controller split MA MB Root),
        UniformCumulativeBudget C' K} (Cstar split) ∧ StorageOptimal.{u, v, w} C := by
  classical
  let pA := A.projectionOnto B split
  let pB := B.projectionOnto A split.symm
  let ellA := controlRestriction A
  let ellB := controlRestriction B
  let e : Fin d → Source d := fun i => (Pi.single i 1, 0)
  have scalar (i : Fin d) (q : ZMod 2) : (Pi.single i q, 0) = q • e i := by
    ext j <;> simp [e, Pi.single_apply, smul_eq_mul]
  have controlSum (z : Source d) : ellA (pA z) + ellB (pB z) = z.2 := by
    exact congrArg Prod.snd (Submodule.projection_add_projection_eq_self split z)
  have sourceRewrite (i : Fin d) (z : Source d) :
      (Action.rewrite i).apply z = z.2 • e i := scalar i z.2
  have localExt {S T : Submodule (ZMod 2) (Source d)} (m n : Local S T)
      (hr : localRead m = localRead n) (hk : localMode m = localMode n)
      (hc : localControl m = localControl n) : m = n := by
    cases m with
    | inl a => cases n with
      | inl b => exact congrArg Sum.inl hr
      | inr b => simp [localMode] at hk
    | inr a => cases n with
      | inl b => simp [localMode] at hk
      | inr b => exact congrArg Sum.inr (Subtype.ext (Prod.ext hr hc))
  have reads (k : Bool) (z : Source d) :
      localRead (encode split k z).1 = pA z ∧
      localRead (encode split k z).2 = pB z := by
    cases k <;> exact ⟨rfl, rfl⟩
  have modes (k : Bool) (z : Source d) :
      localMode (encode split k z).1 = k ∧ localMode (encode split k z).2 = k := by
    cases k <;> exact ⟨rfl, rfl⟩
  have translate {S T : Submodule (ZMod 2) (Source d)} (h : IsCompl S T)
      (t z : Source d) : translateLocal h t (knownLocal h z) = knownLocal h (z + t) := by
    apply localExt
    · exact (map_add _ _ _).symm
    · rfl
    · rfl
  have liftBits (t : Trace A B) : bits (liftTrace t) = bits t := by
    simp [bits, liftTrace, List.map_map, Function.comp_def]
  have liftAppend (h t : Trace A B) : liftTrace (h ++ t) = liftTrace h ++ liftTrace t := by
    simp [liftTrace]
  have lifted (i : Fin d) : ∀ n h (a : Local A B) (b : Local B A),
      execute answer (endpointProtocol split (.rewrite i) false).policy n
          (liftTrace h) (a, b) =
        (execute answer (rewriteProtocol ellA ellB (pA (e i)) (pB (e i))).policy
          n h (localRead a, localRead b)).map (fun r => (liftTrace r.1, r.2)) := by
    let p := rewriteProtocol ellA ellB (pA (e i)) (pB (e i))
    have nodes (h : Trace A B) :
        (endpointProtocol split (.rewrite i) false).policy (liftTrace h) =
          match p.policy h with
          | .inl q => .inl (liftQuestion q)
          | .inr l => .inr l := by
      simp [EndpointProtocol.policy, endpointProtocol, liftBits, p, ellA, ellB, pA, pB, e]
    intro n
    induction n with
    | zero => simp [execute]
    | succ n ih =>
      intro h a b
      simp only [execute, nodes]
      cases hp : p.policy h with
      | inr l => rfl
      | inl q =>
        dsimp only
        have ans : answer (liftQuestion q) (a, b) = answer q (localRead a, localRead b) := by
          cases q <;> rfl
        rw [ans]
        have ha : liftTrace (h ++ [⟨q, answer q (localRead a, localRead b)⟩]) =
            liftTrace h ++ [⟨liftQuestion q, answer q (localRead a, localRead b)⟩] := by
          rw [liftAppend]; rfl
        rw [← ha, ih]
        simp [Option.map_map, Function.comp_def, liftTrace]
  have unknownOutputs (i : Fin d) (a : Local A B) (b : Local B A) (h : List Bool) :
      localRead ((endpointProtocol split (.rewrite i) false).outA a h) =
        (rewriteProtocol ellA ellB (pA (e i)) (pB (e i))).outA (localRead a) h ∧
      localRead ((endpointProtocol split (.rewrite i) false).outB b h) =
        (rewriteProtocol ellA ellB (pA (e i)) (pB (e i))).outB (localRead b) h := by
    constructor
    · simp only [endpointProtocol, Bool.false_eq_true, if_false, resetLocal,
        knownLocal, localRead]
      rw [scalar, map_smul]
      by_cases hz : pA (e i) = 0 <;> simp [rewriteProtocol, pA, ellA, ellB, e, hz]
    · simp only [endpointProtocol, Bool.false_eq_true, if_false, resetLocal,
        knownLocal, localRead]
      rw [scalar, map_smul]
      by_cases hz : pB (e i) = 0 <;> simp [rewriteProtocol, pB, pA, ellA, ellB, e, hz]
  have attained (k : Bool) (z : Source d) (f : Action d) :
      ∃ t, (data split).Exec f (encode split k z) t ∧
        (data split).commit f (encode split k z) t =
          encode split (nextMode k f) (f.apply z) ∧
        t.length = (protocolCharge split k f) := by
    cases f with
    | dataTranslation i =>
      refine ⟨[], ⟨1, ?_⟩, ?_, rfl⟩
      · cases k <;> rfl
      · cases k
        · simp [data, ControllerData.commit, encode, endpointProtocol,
            translateLocal, Action.apply, map_add, nextMode]
        · exact Prod.ext (translate split _ z) (translate split.symm _ z)
    | controlTranslation =>
      refine ⟨[], ⟨1, ?_⟩, ?_, rfl⟩
      · cases k <;> rfl
      · cases k
        · simp [data, ControllerData.commit, encode, endpointProtocol,
            translateLocal, Action.apply, map_add, nextMode]
        · exact Prod.ext (translate split _ z) (translate split.symm _ z)
    | rewrite i =>
      cases k with
      | true =>
        refine ⟨[], ⟨1, rfl⟩, ?_, rfl⟩
        rfl
      | false =>
        obtain ⟨n, t, ht, _, _, hlen⟩ :=
          (rewrite_directional_sharpness.{0,0,0,0} ellA ellB (pA (e i)) (pB (e i))).2.2.2.2
            (pA z) (pB z)
        have hx : (data split).Exec (.rewrite i) (encode split false z) (liftTrace t) := by
          refine ⟨n, ?_⟩
          change execute answer (endpointProtocol split (.rewrite i) false).policy n []
            (.inl (pA z), .inl (pB z)) = some (liftTrace t, ())
          have he := lifted i n [] (.inl (pA z)) (.inl (pB z))
          simp only [localRead] at he
          rw [ht] at he
          exact he
        refine ⟨liftTrace t, hx, ?_, ?_⟩
        swap
        · simpa [liftTrace, protocolCharge, splitCost, ellA, ellB, pA, pB, e] using hlen
        have ho :=
          (rewrite_directional_sharpness.{0,0,0,0} ellA ellB (pA (e i)) (pB (e i))).2.2.2.1.2
            (pA z) (pB z) n t ht
        simp only [id_eq] at ho
        have outs := unknownOutputs i (.inl (pA z)) (.inl (pB z)) (bits (liftTrace t))
        apply Prod.ext
        · apply localExt
          · change localRead ((endpointProtocol split (.rewrite i) false).outA
              (.inl (pA z)) (bits (liftTrace t))) = pA ((Action.rewrite i).apply z)
            rw [outs.1, liftBits]
            simp only [localRead]
            rw [ho.1, controlSum, sourceRewrite, map_smul]
          · rfl
          · rfl
        · apply localExt
          · change localRead ((endpointProtocol split (.rewrite i) false).outB
              (.inl (pB z)) (bits (liftTrace t))) = pB ((Action.rewrite i).apply z)
            rw [outs.2, liftBits]
            simp only [localRead]
            rw [ho.2, controlSum, sourceRewrite, map_smul]
          · rfl
          · rfl
  -- Sufficient fuel uniqueness transports the attained result to every success.
  have executions (k : Bool) (z : Source d) (f : Action d)
      (t : Trace (Local A B) (Local B A)) (ht : (data split).Exec f (encode split k z) t) :
      (data split).commit f (encode split k z) t =
        encode split (nextMode k f) (f.apply z) ∧
      t.length = (protocolCharge split k f) := by
    obtain ⟨s, hs, hc, hl⟩ := attained k z f
    obtain ⟨n, hn⟩ := ht
    obtain ⟨m, hm⟩ := hs
    change execute answer (endpointProtocol split f
      (localMode (encode split k z).1)).policy n [] (encode split k z) = some (t, ()) at hn
    change execute answer (endpointProtocol split f
      (localMode (encode split k z).1)).policy m [] (encode split k z) = some (s, ()) at hm
    rw [(modes k z).1] at hn hm
    let p : EndpointProtocol (Local A B) (Local B A) A B := {
      node := (endpointProtocol split f k).node
      outA := fun a _ => localRead a
      outB := fun b _ => localRead b }
    have hu := (rewrite_directional_sharpness.{0,0,0,0} ellA ellB (0 : A) (0 : B)).2.1
      p (encode split k z).1 (encode split k z).2 n m t s hn hm
    rw [hu]
    exact ⟨hc, hl⟩
  have initialEncode (a : A) (b : B) :
      encode split false ((a : Source d) + (b : Source d)) = (.inl a, .inl b) := by
    simp [encode]
  have forward (m : Local A B × Local B A) (hm : (data split).Reachable m) :
      ∃ k z, m = encode split k z := by
    induction hm with
    | initial a b => exact ⟨false, a.val + b.val, (initialEncode a b).symm⟩
    | @next m hm f t ht ih =>
      obtain ⟨k, z, rfl⟩ := ih
      exact ⟨_, f.apply z, (executions k z f t ht).1⟩
  have runAppend (left right : List (Action d)) (z : Source d) :
      runWord Action.apply (left ++ right) z =
        runWord Action.apply right (runWord Action.apply left z) := by
    induction left generalizing z with
    | nil => rfl
    | cons f left ih => exact ih (f.apply z)
  let translations : AddSubgroup (Source d) := {
    carrier := {t | ∀ z, ∃ word, TranslationWord word ∧
      runWord Action.apply word z = z + t}
    zero_mem' := by
      intro z
      exact ⟨[], by simp [TranslationWord], (add_zero z).symm⟩
    add_mem' := by
      intro x y hx hy z
      obtain ⟨left, hleft, hl⟩ := hx z
      obtain ⟨right, hright, hr⟩ := hy (runWord Action.apply left z)
      refine ⟨left ++ right, ?_, ?_⟩
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact hleft f hf
        · exact hright f hf
      · rw [runAppend, hr, hl, add_assoc]
    neg_mem' := by
      intro t ht
      simpa only [ZModModule.neg_eq_self] using ht }
  have basisData (i : Fin d) : e i ∈ translations := by
    intro z
    exact ⟨[.dataTranslation i], by simp [TranslationWord], rfl⟩
  have basisControl : ((0, 1) : Source d) ∈ translations := by
    intro z
    exact ⟨[.controlTranslation], by simp [TranslationWord], rfl⟩
  let basis : Module.Basis (Fin d ⊕ Unit) (ZMod 2) (Source d) :=
    (Pi.basisFun (ZMod 2) (Fin d)).prod (Module.Basis.singleton Unit (ZMod 2))
  let translationSpace := AddSubgroup.toZModSubmodule 2 translations
  have allTranslations : translationSpace = ⊤ :=
    (Submodule.eq_top_iff_forall_basis_mem basis).2 (by
      intro j
      rcases j with i | j
      · change basis (.inl i) ∈ translations
        simpa [basis, Module.Basis.prod_apply, Pi.basisFun_apply, e] using basisData i
      · have hj : j = () := Subsingleton.elim _ _
        subst j
        change basis (.inr ()) ∈ translations
        simpa [basis, Module.Basis.prod_apply, Module.Basis.singleton_apply]
          using basisControl)
  have sourceWords (z : Source d) : ∃ word, TranslationWord word ∧
      runWord Action.apply word 0 = z := by
    have hz : z ∈ translationSpace := by rw [allTranslations]; exact Submodule.mem_top
    obtain ⟨word, ht, hw⟩ := hz 0
    exact ⟨word, ht, by simpa using hw⟩
  let i₀ : Fin d := ⟨0, by omega⟩
  have knownZero : (data split).Reachable (encode split true 0) := by
    obtain ⟨t, ht, hc, _⟩ := attained false 0 (.rewrite i₀)
    have hi : (data split).Reachable (encode split false 0) := by
      simpa [encode, data] using ControllerData.Reachable.initial (C := data split) (0 : A) (0 : B)
    have hn := ControllerData.Reachable.next hi (.rewrite i₀) t ht
    rw [hc] at hn
    have hz : (Action.rewrite i₀).apply (0 : Source d) = 0 := by
      simp [Action.apply, controlRewrite]
    rw [hz] at hn
    exact hn
  have knownRun : ∀ word z, (data split).Reachable (encode split true z) →
      (data split).Reachable (encode split true (runWord Action.apply word z)) := by
    intro word
    induction word with
    | nil => exact fun _ h => h
    | cons f word ih =>
      intro z hz
      obtain ⟨t, ht, hc, _⟩ := attained true z f
      have hn := ControllerData.Reachable.next hz f t ht
      have hm : (nextMode true f) = true := by
        cases f <;> rfl
      rw [hc, hm] at hn
      exact ih (f.apply z) hn
  have allKnown (z : Source d) : (data split).Reachable (encode split true z) := by
    obtain ⟨word, _, hw⟩ := sourceWords z
    rw [← hw]
    exact knownRun word 0 knownZero
  have backward (k : Bool) (z : Source d) : (data split).Reachable (encode split k z) := by
    cases k with
    | false => exact .initial (pA z) (pB z)
    | true => exact allKnown z
  have actualLeft (a : Local A B) : ∃ b : Local B A, (data split).Reachable (a, b) := by
    cases a with
    | inl a => exact ⟨.inl 0, .initial a 0⟩
    | inr aq =>
      obtain ⟨b, hb⟩ := aq.property
      let z := (aq.val.1 : Source d) + (b : Source d)
      have he : knownLocal split z = .inr aq := by
        apply localExt
        · simp [knownLocal, localRead, z]
        · rfl
        · exact hb.symm
      refine ⟨knownLocal split.symm z, ?_⟩
      have hn := allKnown z
      change (data split).Reachable (knownLocal split z, knownLocal split.symm z) at hn
      rwa [he] at hn
  have actualRight (b : Local B A) : ∃ a : Local A B, (data split).Reachable (a, b) := by
    cases b with
    | inl b => exact ⟨.inl 0, .initial 0 b⟩
    | inr bq =>
      obtain ⟨a, ha⟩ := bq.property
      let z := (a : Source d) + (bq.val.1 : Source d)
      have he : knownLocal split.symm z = .inr bq := by
        apply localExt
        · simp [knownLocal, localRead, z]
        · rfl
        · change controlRestriction A a + controlRestriction B bq.val.1 = bq.val.2
          rw [add_comm]
          exact ha.symm
      refine ⟨knownLocal split z, ?_⟩
      have hn := allKnown z
      change (data split).Reachable (knownLocal split z, knownLocal split.symm z) at hn
      rwa [he] at hn
  let C : Controller split (Local A B) (Local B A) Bool := {
    toControllerData := data split
    root_agree := by
      intro m hm f
      obtain ⟨k, z, rfl⟩ := forward m hm
      exact (modes k z).1.trans (modes k z).2.symm
    terminates := by
      intro m hm f
      obtain ⟨k, z, rfl⟩ := forward m hm
      obtain ⟨t, ht, _⟩ := attained k z f
      exact ⟨t, ht⟩
    actualA := actualLeft
    actualB := actualRight
    correct := by
      intro m hm f t ht
      obtain ⟨k, z, rfl⟩ := forward m hm
      dsimp only
      change localRead ((data split).commit f (encode split k z) t).1 =
          pA (f.apply ((localRead (encode split k z).1 : Source d) +
            (localRead (encode split k z).2 : Source d))) ∧
        localRead ((data split).commit f (encode split k z) t).2 =
          pB (f.apply ((localRead (encode split k z).1 : Source d) +
            (localRead (encode split k z).2 : Source d)))
      rw [(executions k z f t ht).1, (reads k z).1, (reads k z).2]
      have hsum : (pA z : Source d) + (pB z : Source d) = z :=
        Submodule.projection_add_projection_eq_self split z
      rw [hsum]
      exact reads _ _
    free_translation := by
      intro m hm t
      obtain ⟨k, z, rfl⟩ := forward m hm
      constructor
      · intro i ht
        exact List.eq_nil_of_length_eq_zero (executions k z (.dataTranslation i) t ht).2
      · intro ht
        exact List.eq_nil_of_length_eq_zero (executions k z .controlTranslation t ht).2 }
  have stepLaw (k : Bool) (z : Source d) (m : C.State) (hm : m.val = encode split k z)
      (f : Action d) :
      (C.step f m).val = encode split
        (nextMode k f) (f.apply z) ∧
      C.cost m f = (protocolCharge split k f) := by
    have ht : (data split).Exec f m.val (C.trace f m) :=
      Classical.choose_spec (C.terminates m.val m.property f)
    rw [hm] at ht
    have he := executions k z f (C.trace f m) ht
    constructor
    · change (data split).commit f m.val (C.trace f m) = _
      rw [hm]
      exact he.1
    · exact he.2
  have knownWord : ∀ word z (m : C.State), m.val = encode split true z →
      (runWord C.step word m).val = encode split true (runWord Action.apply word z) ∧
        Comm C.step C.cost m word = 0 := by
    intro word
    induction word with
    | nil => exact fun _ _ h => ⟨h, rfl⟩
    | cons f word ih =>
      intro z m hm
      have hs := stepLaw true z m hm f
      have hk : (nextMode true f) = true := by
        cases f <;> rfl
      rw [hk] at hs
      have hh := ih (f.apply z) (C.step f m) hs.1
      refine ⟨hh.1, ?_⟩
      change C.cost m f + Comm C.step C.cost (C.step f m) word = 0
      rw [hh.2, hs.2]
      cases f <;> rfl
  have unknownWord : ∀ word z (m : C.State), m.val = encode split false z →
      (∃ k, (runWord C.step word m).val = encode split k (runWord Action.apply word z)) ∧
        Comm C.step C.cost m word = firstRewriteCost split word := by
    intro word
    induction word with
    | nil => exact fun _ _ h => ⟨⟨false, h⟩, rfl⟩
    | cons f word ih =>
      intro z m hm
      have hs := stepLaw false z m hm f
      cases f with
      | dataTranslation i =>
        have hh := ih ((Action.dataTranslation i).apply z) (C.step (.dataTranslation i) m) hs.1
        exact ⟨hh.1, by
          simpa only [Comm, firstRewriteCost, hs.2, protocolCharge, zero_add] using hh.2⟩
      | controlTranslation =>
        have hh := ih (Action.controlTranslation.apply z) (C.step .controlTranslation m) hs.1
        exact ⟨hh.1, by
          simpa only [Comm, firstRewriteCost, hs.2, protocolCharge, zero_add] using hh.2⟩
      | rewrite i =>
        have hh := knownWord word ((Action.rewrite i).apply z) (C.step (.rewrite i) m) hs.1
        exact ⟨⟨true, hh.1⟩, by simp only [Comm, firstRewriteCost, hs.2, hh.2, add_zero,
          protocolCharge, Bool.false_eq_true, if_false]⟩
  have allWords (z : Source d) (word : List (Action d)) :
      C.readout (runWord C.step word (C.initial (pA z) (pB z))) =
          runWord Action.apply word z ∧
        Comm C.step C.cost (C.initial (pA z) (pB z)) word = firstRewriteCost split word := by
    have hh := unknownWord word z (C.initial (pA z) (pB z)) rfl
    obtain ⟨k, hk⟩ := hh.1
    refine ⟨?_, hh.2⟩
    change (localRead (runWord C.step word (C.initial (pA z) (pB z))).val.1 : Source d) +
      (localRead (runWord C.step word (C.initial (pA z) (pB z))).val.2 : Source d) = _
    rw [hk, (reads k _).1, (reads k _).2]
    exact Submodule.projection_add_projection_eq_self split _
  have firstBound : ∀ word, firstRewriteCost split word ≤ Cstar split := by
    intro word
    induction word with
    | nil => exact Nat.zero_le _
    | cons f word ih => cases f with
      | dataTranslation _ => exact ih
      | controlTranslation => exact ih
      | rewrite i => exact Finset.le_sup (Finset.mem_univ i)
  let knownEquiv {S T : Submodule (ZMod 2) (Source d)} :
      Known S T ≃ S × LinearMap.range (controlRestriction T) := {
    toFun := fun aq => (aq.val.1, ⟨aq.val.2 - controlRestriction S aq.val.1, by
      obtain ⟨b, hb⟩ := aq.property
      exact ⟨b, by rw [hb]; abel⟩⟩)
    invFun := fun ar => ⟨(ar.1, controlRestriction S ar.1 + ar.2.val), by
      obtain ⟨b, hb⟩ := ar.2.property
      exact ⟨b, by rw [hb]⟩⟩
    left_inv := by
      intro aq
      apply Subtype.ext
      dsimp only
      apply Prod.ext
      · rfl
      · abel
    right_inv := by
      intro ar
      dsimp only
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        dsimp only
        abel }
  let fiberEquiv {S T : Submodule (ZMod 2) (Source d)} (a : S) :
      {m : Local S T // localRead m = a} ≃ Unit ⊕ LinearMap.range (controlRestriction T) := {
    toFun := fun m => match m.val with
      | .inl _ => .inl ()
      | .inr aq => .inr (knownEquiv aq).2
    invFun := fun q => match q with
      | .inl _ => ⟨.inl a, rfl⟩
      | .inr q => ⟨.inr (knownEquiv.symm (a, q)), rfl⟩
    left_inv := by
      intro m
      apply Subtype.ext
      rcases m with ⟨m, hm⟩
      cases m with
      | inl b => exact congrArg Sum.inl hm.symm
      | inr aq =>
        apply congrArg Sum.inr
        have ha : a = (knownEquiv aq).1 := hm.symm
        rw [ha, Prod.mk.eta, Equiv.symm_apply_apply]
    right_inv := by
      intro q
      cases q with
      | inl q => cases q; rfl
      | inr q =>
        change Sum.inr (knownEquiv (knownEquiv.symm (a, q))).2 = Sum.inr q
        rw [Equiv.apply_symm_apply] }
  have localCount {S T : Submodule (ZMod 2) (Source d)} :
      Nat.card (Local S T) = (1 + 2 ^ Module.finrank (ZMod 2)
        (LinearMap.range (controlRestriction T))) * 2 ^ Module.finrank (ZMod 2) S := by
    rw [Nat.card_sum, Nat.card_congr knownEquiv, Nat.card_prod,
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S),
      Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := LinearMap.range (controlRestriction T)), Nat.card_zmod]
    ring
  have fiberCount {S T : Submodule (ZMod 2) (Source d)} (a : S) :
      Nat.card {m : Local S T // localRead m = a} =
        1 + 2 ^ Module.finrank (ZMod 2) (LinearMap.range (controlRestriction T)) := by
    rw [Nat.card_congr (fiberEquiv a), Nat.card_sum, Nat.card_unique,
      Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := LinearMap.range (controlRestriction T)), Nat.card_zmod]
  have encodedRead (k : Bool) (z : Source d) (m : C.State)
      (hm : m.val = encode split k z) : C.readout m = z := by
    change (localRead m.val.1 : Source d) + (localRead m.val.2 : Source d) = z
    rw [hm, (reads k z).1, (reads k z).2]
    exact Submodule.projection_add_projection_eq_self split z
  let jointEquiv : C.State ≃ Bool × Source d := {
    toFun := fun m => (localMode m.val.1, C.readout m)
    invFun := fun kz => ⟨encode split kz.1 kz.2, backward kz.1 kz.2⟩
    left_inv := by
      intro m
      obtain ⟨k, z, hm⟩ := forward m.val m.property
      apply Subtype.ext
      change encode split (localMode m.val.1) (C.readout m) = m.val
      rw [encodedRead k z m hm, hm, (modes k z).1]
    right_inv := by
      intro kz
      apply Prod.ext
      · exact (modes kz.1 kz.2).1
      · exact encodedRead kz.1 kz.2 _ rfl }
  have jointFinite : Finite C.State := Finite.of_injective jointEquiv jointEquiv.injective
  have jointCount : Nat.card C.State = 2 ^ (d + 2) := by
    rw [Nat.card_congr jointEquiv, Nat.card_prod]
    have hs : Nat.card (Source d) = 2 ^ d * 2 := by
      rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    rw [hs]
    simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
    rw [show d + 2 = d + 1 + 1 by omega, pow_succ, pow_succ]
    ring
  have uniform : UniformCumulativeBudget C (Cstar split) := by
    intro a b word
    let z := (a : Source d) + (b : Source d)
    have hm : (C.initial a b).val = encode split false z := (initialEncode a b).symm
    rw [(unknownWord word z (C.initial a b) hm).2]
    exact firstBound word
  have least : IsLeast {K : Nat | ∃ (MA MB Root : Type) (C' : Controller split MA MB Root),
      UniformCumulativeBudget C' K} (Cstar split) := by
    refine ⟨⟨Local A B, Local B A, Bool, C, uniform⟩, ?_⟩
    intro K ⟨MA, MB, Root, C', hK⟩
    exact ((fixed_split_rewrite_budget d hd A B split hA hB).2.2.2.2.2 C' K hK).1
  refine ⟨C, rfl, ?_, executions, ?_, allWords, uniform,
    fiberCount, fiberCount, localCount, localCount, jointFinite, jointCount, least, ?_⟩
  · intro m
    exact ⟨forward m, fun ⟨k, z, hz⟩ => hz ▸ backward k z⟩
  · intro z
    obtain ⟨word, hword, hw⟩ := sourceWords z
    refine ⟨i₀, word, hword, ?_⟩
    have hs := (stepLaw false 0 (C.initial 0 0) (by simp [C, Controller.initial, encode, data])
      (.rewrite i₀)).1
    have hz : (Action.rewrite i₀).apply (0 : Source d) = 0 := by
      simp [Action.apply, controlRewrite]
    rw [hz] at hs
    have hh := (knownWord word 0 (C.step (.rewrite i₀) (C.initial 0 0)) hs).1
    simpa only [runWord, hw] using hh

  · have : Finite C.State := jointFinite
    have encodingIff {M : Type} [Finite M] (k : Nat) :
        BinaryEncoding M k ↔ Nat.card M ≤ 2 ^ k := by
      let _ := Fintype.ofFinite M
      simpa [BinaryEncoding, Nat.card_eq_fintype_card] using
        (Function.Embedding.nonempty_iff_card_le (α := M) (β := Fin k → Bool))
    have encodingLeast {M : Type} [Finite M] :
        IsLeast {k | BinaryEncoding M k} (Nat.clog 2 (Nat.card M)) := by
      refine ⟨(encodingIff (M := M) _).2 (Nat.le_pow_clog (by decide) _), ?_⟩
      intro k hk
      exact (Nat.clog_le_iff_le_pow (by decide)).2 ((encodingIff (M := M) k).1 hk)
    have jointWidth : Nat.clog 2 (Nat.card C.State) = d + 2 := by
      rw [jointCount, Nat.clog_pow _ _ (by decide)]
    have jointLog : Real.logb 2 (Nat.card C.State) = (d + 2 : Nat) := by
      rw [jointCount, Nat.cast_pow, Real.logb_pow]
      simp
    have controls : controlRestriction A ≠ 0 ∨ controlRestriction B ≠ 0 := by
      by_cases ha : ellA = 0
      · right
        intro hb
        change ellB = 0 at hb
        have hh := controlSum (0, 1)
        simp only [ha, hb, LinearMap.zero_apply, zero_add] at hh
        exact zero_ne_one hh
      · exact Or.inl ha
    have dimension : Module.finrank (ZMod 2) A + Module.finrank (ZMod 2) B = d + 1 := by
      simpa [Source, Module.finrank_prod, Module.finrank_pi] using
        Submodule.finrank_add_eq_of_isCompl split
    have rangeRank (S : Submodule (ZMod 2) (Source d)) :
        Module.finrank (ZMod 2) (LinearMap.range (controlRestriction S)) =
          if controlRestriction S = 0 then 0 else 1 := by
      by_cases h : controlRestriction S = 0
      · rw [if_pos h, h, LinearMap.range_zero]
        exact finrank_bot (ZMod 2) (ZMod 2)
      · have hr : LinearMap.range (controlRestriction S) = ⊤ :=
          LinearMap.range_eq_top.2
            (surjective_of_nonzero_of_finrank_eq_one
              (CommSemiring.finrank_self (ZMod 2)) h)
        rw [if_neg h, hr]
        exact (finrank_top (ZMod 2) (ZMod 2)).trans
          (CommSemiring.finrank_self (ZMod 2))
    have ceilLog (n : Nat) : ⌈Real.logb 2 n⌉₊ = Nat.clog 2 n := by
      simpa using Real.natCeil_logb_natCast 2 n
    have widths (r : Nat) (f t : Nat) (hf : f = 2 ∧ t = 1 ∨ f = 3 ∧ t = 2) :
        Nat.clog 2 (f * 2 ^ r) = r + t := by
      rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [show 2 * 2 ^ r = 2 ^ (r + 1) by rw [pow_succ]; ring,
          Nat.clog_pow _ _ (by decide)]
      · apply Nat.le_antisymm
        · apply (Nat.clog_le_iff_le_pow (by decide)).2
          rw [pow_add]
          norm_num
          omega
        · have hh : 2 ^ (r + 1) < 3 * 2 ^ r := by
            rw [pow_succ]
            have hp : 0 < 2 ^ r := by positivity
            omega
          have hh' := (Nat.lt_clog_iff_pow_lt (by decide)).2 hh
          omega
    have logCount (r : Nat) (f : Nat) (hf : f ≠ 0) :
        Real.logb 2 (f * 2 ^ r : Nat) = Real.logb 2 f + r := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.logb_mul (by exact_mod_cast hf) (by positivity),
        Real.logb_pow]
      simp
    have row (fA fB tA tB logFactor overhead budget : Nat)
        (ha : 1 + 2 ^ Module.finrank (ZMod 2) (LinearMap.range ellB) = fA)
        (hb : 1 + 2 ^ Module.finrank (ZMod 2) (LinearMap.range ellA) = fB)
        (hta : fA = 2 ∧ tA = 1 ∨ fA = 3 ∧ tA = 2)
        (htb : fB = 2 ∧ tB = 1 ∨ fB = 3 ∧ tB = 2)
        (hl : fA * fB = logFactor) (ht : tA + tB + 1 = overhead)
        (hk : Cstar split = budget) : StorageRow split fA fB tA tB logFactor overhead budget := by
      have ca : Nat.card (Local A B) = fA * 2 ^ Module.finrank (ZMod 2) A := by
        change 1 + 2 ^ Module.finrank (ZMod 2)
          (LinearMap.range (controlRestriction B)) = fA at ha
        rw [localCount, ha]
      have cb : Nat.card (Local B A) = fB * 2 ^ Module.finrank (ZMod 2) B := by
        change 1 + 2 ^ Module.finrank (ZMod 2)
          (LinearMap.range (controlRestriction A)) = fB at hb
        rw [localCount, hb]
      have hfa : fA ≠ 0 := by rcases hta with h | h <;> omega
      have hfb : fB ≠ 0 := by rcases htb with h | h <;> omega
      have wa := widths (Module.finrank (ZMod 2) A) fA tA hta
      have wb := widths (Module.finrank (ZMod 2) B) fB tB htb
      dsimp only [StorageRow]
      refine ⟨?_, ?_, ca, cb, ?_, ca ▸ wa, cb ▸ wb, ?_, ?_, ?_, hk⟩
      · intro a; exact (fiberCount a).trans ha
      · intro b; exact (fiberCount b).trans hb
      · rw [ca, cb, logCount _ _ hfa, logCount _ _ hfb]
        have hlogs : Real.logb 2 (fA : Real) + Real.logb 2 (fB : Real) =
            Real.logb 2 (logFactor : Real) := by
          rw [← Real.logb_mul (by exact_mod_cast hfa) (by exact_mod_cast hfb),
            ← Nat.cast_mul, hl]
        have hdims : (Module.finrank (ZMod 2) A : Real) +
            Module.finrank (ZMod 2) B = (d + 1 : Nat) := by exact_mod_cast dimension
        linarith
      · rw [ceilLog, ca, wa]
      · rw [ceilLog, cb, wb]
      · rw [ceilLog, ceilLog, ca, cb, wa, wb]
        omega
    refine ⟨encodingLeast, encodingLeast, jointWidth ▸ (encodingLeast (M := C.State)),
      jointLog, ?_, dimension, controls, ?_, ?_, ?_⟩
    · intro MA MB Root C' K hK
      obtain ⟨fa, fb, ⟨ea⟩, ⟨eb⟩, ⟨eq⟩⟩ :=
        initialized_controller_capacity d hd A B split hA hB C' K hK
      have la : Nat.card (Local A B) = _ := localCount
      have lb : Nat.card (Local B A) = _ := localCount
      refine ⟨?_, ?_, la ▸ ⟨ea⟩, lb ▸ ⟨eb⟩, jointCount ▸ ⟨eq⟩, ?_, ?_, ?_, ?_⟩
      · intro a; simpa only [fiberCount a] using fa a
      · intro b; simpa only [fiberCount b] using fb b
      · intro finiteA finiteB
        have := finiteA; have := finiteB
        have ha : Nat.card (Local A B) ≤ Nat.card MA := by
          rw [la]; simpa using Nat.card_le_card_of_injective ea ea.injective
        have hb : Nat.card (Local B A) ≤ Nat.card MB := by
          rw [lb]; simpa using Nat.card_le_card_of_injective eb eb.injective
        have logA : Real.logb 2 (Nat.card (Local A B)) ≤ Real.logb 2 (Nat.card MA) :=
          Real.logb_le_logb_of_le (by norm_num)
            (by exact_mod_cast Nat.card_pos (α := Local A B)) (by exact_mod_cast ha)
        have logB : Real.logb 2 (Nat.card (Local B A)) ≤ Real.logb 2 (Nat.card MB) :=
          Real.logb_le_logb_of_le (by norm_num)
            (by exact_mod_cast Nat.card_pos (α := Local B A)) (by exact_mod_cast hb)
        exact ⟨add_le_add logA logB, add_le_add (Nat.ceil_mono logA) (Nat.ceil_mono logB)⟩
      · rintro kA kB ⟨codeA⟩ ⟨codeB⟩
        constructor
        · apply (Nat.clog_le_iff_le_pow (by decide)).2
          rw [la]
          simpa using Nat.card_le_card_of_injective (ea.trans codeA) (ea.trans codeA).injective
        · apply (Nat.clog_le_iff_le_pow (by decide)).2
          rw [lb]
          simpa using Nat.card_le_card_of_injective (eb.trans codeB) (eb.trans codeB).injective
      · rintro k ⟨code⟩
        have hh : 2 ^ (d + 2) ≤ 2 ^ k := by
          simpa using Nat.card_le_card_of_injective (eq.trans code) (eq.trans code).injective
        exact (Nat.pow_le_pow_iff_right (by decide)).1 hh
      · exact ((fixed_split_rewrite_budget d hd A B split hA hB).2.2.2.2.2 C' K hK).1
    · intro ha hb
      apply row 3 2 2 1 6 4 1
        (by rw [rangeRank, if_neg hb]; norm_num)
        (by rw [rangeRank, if_pos ha]; norm_num)
        (by tauto) (by tauto) (by norm_num) (by norm_num)
      exact (fixed_split_rewrite_budget.{0, 0, 0} d hd A B split hA hB).1 ha
    · intro hb ha
      apply row 2 3 1 2 6 4 1
        (by rw [rangeRank, if_pos hb]; norm_num)
        (by rw [rangeRank, if_neg ha]; norm_num)
        (by tauto) (by tauto) (by norm_num) (by norm_num)
      exact (fixed_split_rewrite_budget.{0, 0, 0} d hd A B split hA hB).2.1 hb
    · intro ha hb
      apply row 3 3 2 2 9 5 2
        (by rw [rangeRank, if_neg hb]; norm_num)
        (by rw [rangeRank, if_neg ha]; norm_num)
        (by tauto) (by tauto) (by norm_num) (by norm_num)
      exact (fixed_split_rewrite_budget.{0, 0, 0} d hd A B split hA hB).2.2.1 ha hb

#print axioms restricted_initialized_controller

end D5.S3.ObserverMemory.Algorithms.RestrictedInitializedController
