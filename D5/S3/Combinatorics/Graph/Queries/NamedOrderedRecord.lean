/- GID: D5/S3/Combinatorics/Graph/Queries/NamedOrderedRecord
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/NamedOrderedRecord
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: A complete ordered name-query record has one inverse-factorial factor per distinct successful query name. -/

import D5.S3.Combinatorics.Graph.Queries.FixedNeighborOrder
import D5.S3.Combinatorics.Probability.NamingRestrictionLaw
import Mathlib.Data.List.FinRange

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Queries.NamedOrderedRecord

open D5.S3.Combinatorics.Graph.Queries.FixedNeighborOrder
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open D5.S3.Combinatorics.Probability.NamingRestrictionLaw (namingMass)
open scoped ENNReal BigOperators

universe u

variable {N : Type u}

abbrev LocalOrder (r : Option (Set N)) : Type u :=
  match r with
  | none => PUnit.{u + 1}
  | some s => Fin s.ncard ≃ s

noncomputable def orderedAnswer (r : Option (Set N)) : LocalOrder r → Option (List N) :=
  match r with
  | none => fun _ => none
  | some _ => fun order => some (List.ofFn fun i => (order i : N))

def eraseReply (r : Option (List N)) : Option (Set N) :=
  r.map fun l => {n | n ∈ l}

private theorem erase_orderedAnswer (r : Option (Set N)) (f : LocalOrder r) :
    eraseReply (orderedAnswer r f) = r := by
  cases r with
  | none => rfl
  | some s =>
    change some {n | n ∈ List.ofFn (fun i => (f i : N))} = some s
    congr 1
    ext n
    simp only [Set.mem_ofPred_eq, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      exact (f i).2
    · intro hn
      obtain ⟨i, hi⟩ := f.surjective ⟨n, hn⟩
      exact ⟨i, congrArg Subtype.val hi⟩

private theorem orderedAnswer_injective (r : Option (Set N)) :
    Function.Injective (orderedAnswer r) := by
  cases r with
  | none => intro f g _; exact Subsingleton.elim f g
  | some s =>
    intro f g h
    change some (List.ofFn (fun i => (f i : N))) = some (List.ofFn (fun i => (g i : N))) at h
    have pointwise := List.ofFn_injective (Option.some.inj h)
    apply Equiv.ext
    intro i
    exact Subtype.ext (congrFun pointwise i)

private noncomputable instance localOrderNonempty [Finite N] (r : Option (Set N)) : Nonempty (LocalOrder r) := by
  cases r with
  | none => exact ⟨PUnit.unit⟩
  | some s =>
    let _ : Fintype s := Fintype.ofFinite s
    exact ⟨(Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card (α := s)).symm).symm⟩

private noncomputable instance localOrderFintype [Finite N] (r : Option (Set N)) : Fintype (LocalOrder r) := by
  classical
  cases r with
  | none => exact inferInstanceAs (Fintype PUnit.{u + 1})
  | some s =>
    letI : Fintype s := Fintype.ofFinite s
    exact Fintype.ofFinite _

private theorem localOrder_card [Finite N] (r : Option (Set N)) :
    Fintype.card (LocalOrder r) = (r.elim 0 Set.ncard).factorial := by
  classical
  cases r with
  | none =>
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_unique
  | some s =>
    obtain ⟨f⟩ := localOrderNonempty (some s)
    let _ : Fintype (LocalOrder (some s)) := localOrderFintype (some s)
    let e : Equiv.Perm (Fin s.ncard) ≃ LocalOrder (some s) :=
      Equiv.equivCongr (Equiv.refl _) f
    rw [← Fintype.card_congr e, Fintype.card_perm, Fintype.card_fin]
    rfl

private theorem run_with_reply_table {Q : Type*} {Y : Q → Type*} {S : Type*}
    (read : ∀ q, S → Y q) (p : PassiveProtocol Q Y) (s : S) :
    runPassiveProtocol (fun q (answers : ∀ v, Y v) => answers q) p (fun q => read q s) =
      runPassiveProtocol read p s := by
  induction p with
  | stop => rfl
  | query q next ih =>
    simp only [runPassiveProtocol, List.cons.injEq, true_and]
    exact ih (read q s)

private theorem sameRecord {Q : Type*} {Y : Q → Type*} {S T : Type*}
    (left : ∀ q, S → Y q) (right : ∀ q, T → Y q)
    (p : PassiveProtocol Q Y) (s : S) (t : T) :
    runPassiveProtocol left p s = runPassiveProtocol right p t ↔
      ∀ e ∈ runPassiveProtocol right p t, left e.1 s = e.2 := by
  have replay := same_history_iff (fun q => Y q) (fun _ answer => answer) p
    (fun q => left q s) (fun q => right q t)
  change runPassiveProtocol (fun q (answers : ∀ v, Y v) => answers q) p
      (fun q => left q s) = _ ↔ _ at replay
  rw [run_with_reply_table left, run_with_reply_table right] at replay
  exact replay

variable [Fintype N] [DecidableEq N]

abbrev OrderTable (reply : N → Option (Set N)) := ∀ q, LocalOrder (reply q)

private noncomputable instance tableNonempty (reply : N → Option (Set N)) : Nonempty (OrderTable reply) :=
  ⟨fun q => (localOrderNonempty (reply q)).some⟩

noncomputable def readOrdered (reply : N → Option (Set N)) (q : N) (t : OrderTable reply) :
    Option (List N) := orderedAnswer (reply q) (t q)

/-- A realized adaptive ordered record fixes one persistent local order per queried name. -/
theorem orderedRecord_mass
    (reply ref : N → Option (Set N)) (p : PassiveProtocol N (fun _ => Option (List N)))
    (refTable : OrderTable ref) :
    let trace := runPassiveProtocol (fun q => readOrdered ref q) p refTable
    let seen := (trace.map Sigma.fst).toFinset
    let mass := namingMass (∏ q ∈ seen, ((ref q).elim 0 Set.ncard).factorial)
    (uniformPmf (∀ q, LocalOrder (reply q))).toOuterMeasure
        {t | runPassiveProtocol (fun q => readOrdered reply q) p t = trace} =
      @ite ℝ≥0∞ (∀ q ∈ seen, reply q = ref q) (Classical.propDecidable _) mass 0 := by
  classical
  intro trace seen mass
  have hRead (e : Σ _ : N, Option (List N)) (he : e ∈ trace) :
      e.2 = readOrdered ref e.1 refTable :=
    ((sameRecord (readOrdered ref) (readOrdered ref) p refTable refTable).mp rfl e he).symm
  by_cases compatible : ∀ q ∈ seen, reply q = ref q
  · rw [ite_eq_left compatible]
    let a (q : seen) : LocalOrder (reply q) := (compatible q q.2).symm ▸ refTable q
    have hAt (q : seen) : orderedAnswer (reply q) (a q) = readOrdered ref q refTable := by
      have hTransport {x y : Option (Set N)} (h : x = y) (s : LocalOrder y) :
          orderedAnswer x (h.symm ▸ s) = orderedAnswer y s := by
        subst x
        rfl
      exact hTransport (compatible q q.2) (refTable q)
    have hEvent :
        {t : OrderTable reply | runPassiveProtocol (fun q => readOrdered reply q) p t = trace} =
          {t : OrderTable reply | ∀ q : seen, t q = a q} := by
      ext t
      change _ = trace ↔ ∀ q : seen, t q = a q
      rw [sameRecord (fun q => readOrdered reply q) (fun q => readOrdered ref q)]
      constructor
      · intro h q
        obtain ⟨e, he, hq⟩ := List.mem_map.mp (List.mem_toFinset.mp q.2)
        apply orderedAnswer_injective (reply q)
        change readOrdered reply q t = _
        rw [hAt]
        rw [← hq]
        exact (h e he).trans (hRead e he)
      · intro h e he
        let q : seen := ⟨e.1, List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, rfl⟩)⟩
        change orderedAnswer (reply q) (t q) = e.2
        rw [h q, hAt]
        exact (hRead e he).symm
    rw [hEvent]
    have hUniform := uniform_coordinate_cylinder (fun q => LocalOrder (reply q)) seen a
    have hCount (q : N) (hq : q ∈ seen) :
        Fintype.card (LocalOrder (reply q)) = ((ref q).elim 0 Set.ncard).factorial := by
      rw [localOrder_card, compatible q hq]
    rw [hUniform, Finset.prod_congr rfl hCount]
    rfl
  · rw [ite_eq_right compatible]
    have hEmpty :
        {t : OrderTable reply | runPassiveProtocol (fun q => readOrdered reply q) p t = trace} =
          ∅ := by
      ext t
      change _ = trace ↔ False
      rw [sameRecord (fun q => readOrdered reply q) (fun q => readOrdered ref q)]
      refine ⟨fun h => compatible (fun q hq => ?_), False.elim⟩
      obtain ⟨e, he, hq⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
      subst q
      have hOrdered := (h e he).trans (hRead e he)
      exact (erase_orderedAnswer _ _).symm.trans
        ((congrArg eraseReply hOrdered).trans (erase_orderedAnswer _ _))
    rw [hEmpty]
    simp

end D5.S3.Combinatorics.Graph.Queries.NamedOrderedRecord
