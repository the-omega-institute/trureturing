/- GID: D5/S1/Dynamics/Shadowing/WholePathProjection
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/WholePathProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Whole-path projection of a finite hidden graph has a bounded prefix diagnostic. -/

import D5.S1.Dynamics.Shadowing.FiniteObservationSofic
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Computability.NFA
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Powerset

open Set CategoryTheory Opposite

namespace D5.S1.Dynamics.Shadowing

universe u v
variable {H : Type u} {P : Type v}

/-- A lift through time `m`, including the initial vertex. `m` counts edges;
the prefix has `m + 1` vertices, also when `m = 0`. -/
def PrefixLift (eH : H → H → Prop) (q : H → P) (a : ℕ → P) (m : ℕ) : Prop :=
  ∃ b : Fin (m + 1) → H,
    (∀ i : Fin m, eH (b i.castSucc) (b i.succ)) ∧
    ∀ i : Fin (m + 1), q (b i) = a i.val

private def prefixWitness (eH : H → H → Prop) (q : H → P) (a : ℕ → P) (m : ℕ) :=
  {b : Fin (m + 1) → H //
    (∀ i : Fin m, eH (b i.castSucc) (b i.succ)) ∧
    ∀ i : Fin (m + 1), q (b i) = a i.val}

private def restrictPrefix (eH : H → H → Prop) (q : H → P) (a : ℕ → P)
    {m n : ℕ} (h : m ≤ n) (b : prefixWitness eH q a n) : prefixWitness eH q a m :=
  ⟨fun i => b.1 ⟨i.val, by omega⟩,
    (fun i => b.2.1 ⟨i.val, by omega⟩), fun i => b.2.2 ⟨i.val, by omega⟩⟩

private def prefixSystem (eH : H → H → Prop) (q : H → P) (a : ℕ → P) :
    ℕᵒᵖ ⥤ Type u where
  obj m := prefixWitness eH q a m.unop
  map f := ↾(restrictPrefix eH q a (leOfHom f.unop))
  map_id _ := by
    apply TypeCat.Hom.ext; apply TypeCat.Fun.ext
    funext b; apply Subtype.ext; funext i; rfl
  map_comp _ _ := by
    apply TypeCat.Hom.ext; apply TypeCat.Fun.ext
    funext b; apply Subtype.ext; funext i; rfl

private theorem whole_lift_of_prefix_lifts [Finite H]
    (eH : H → H → Prop) (q : H → P) (a : ℕ → P)
    (ha : ∀ m, PrefixLift eH q a m) : a ∈ graphLanguage eH q := by
  let F := prefixSystem eH q a
  have : ∀ m : ℕᵒᵖ, Finite (F.obj m) := fun m => by
    dsimp [F, prefixSystem, prefixWitness]
    infer_instance
  have : ∀ m : ℕᵒᵖ, Nonempty (F.obj m) := fun m => by
    obtain ⟨b, hb⟩ := ha m.unop
    exact ⟨⟨b, hb⟩⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  let b : ℕ → H := fun n => (s (op n)).1 ⟨n, by simp⟩
  have hc (n : ℕ) : (s (op (n + 1))).1 ⟨n, by simp <;> omega⟩ = b n := by
    have h := hs (homOfLE (Nat.le_succ n)).op
    exact congrArg (fun z : F.obj (op n) => z.1 ⟨n, by simp⟩) h
  refine ⟨b, fun n => ?_, fun n => (s (op n)).2.2 ⟨n, by simp⟩⟩
  have h := (s (op (n + 1))).2.1 ⟨n, by simp <;> omega⟩
  change eH ((s (op (n + 1))).1 ⟨n, by simp <;> omega⟩) (b (n + 1)) at h
  rwa [hc] at h

private theorem prefix_lift_of_whole_lift
    (eH : H → H → Prop) (q : H → P) (a : ℕ → P)
    (ha : a ∈ graphLanguage eH q) (m : ℕ) : PrefixLift eH q a m := by
  obtain ⟨b, he, hq⟩ := ha
  exact ⟨fun i => b i.val, fun i => he i.val, fun i => hq i.val⟩

/-- Edge-preserving projection retains the entire visible path language exactly
when every prefix of every whole visible path lifts. Hidden finiteness supplies
the inverse-system compactness; no seriality or onto bonding map is assumed. -/
theorem graphLanguage_eq_iff_prefix_lifts [Finite H]
    (eH : H → H → Prop) (eP : P → P → Prop) (q : H → P)
    (hq : ∀ h h', eH h h' → eP (q h) (q h')) :
    graphLanguage eH q = graphLanguage eP id ↔
      ∀ a ∈ graphLanguage eP id, ∀ m, PrefixLift eH q a m := by
  constructor
  · intro heq a ha m
    exact prefix_lift_of_whole_lift eH q a (heq ▸ ha) m
  · intro h
    apply Set.Subset.antisymm
    · rintro a ⟨b, hb, hl⟩
      refine ⟨a, fun n => ?_, fun _ => rfl⟩
      rw [← hl n, ← hl (n + 1)]
      exact hq _ _ (hb n)
    · intro a ha
      exact whole_lift_of_prefix_lifts eH q a (h a ha)

private def tailWord (a : ℕ → P) (m : ℕ) : List P :=
  List.ofFn (fun i : Fin m => a (i.val + 1))

private theorem tailWord_succ (a : ℕ → P) (m : ℕ) :
    tailWord a (m + 1) = tailWord a m ++ [a (m + 1)] := by
  simpa [tailWord, List.concat_eq_append] using
    List.ofFn_succ' (fun i : Fin (m + 1) => a (i.val + 1))

private def liftNFA (eH : H → H → Prop) (q : H → P) : NFA P H where
  step h v := {h' | eH h h' ∧ q h' = v}
  start := Set.univ
  accept := Set.univ

private theorem reachable_endpoints (eH : H → H → Prop) (q : H → P)
    (a : ℕ → P) (m : ℕ) (t : H) :
    t ∈ (liftNFA eH q).evalFrom {h | q h = a 0} (tailWord a m) ↔
      ∃ b : prefixWitness eH q a m, b.1 (Fin.last m) = t := by
  induction m generalizing t with
  | zero =>
    change q t = a 0 ↔ ∃ b : prefixWitness eH q a 0, b.1 (Fin.last 0) = t
    constructor
    · intro ht
      exact ⟨⟨fun _ => t, (fun i => Fin.elim0 i), fun i => by
        simpa only [Fin.val_eq_zero] using ht⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact b.2.2 (Fin.last 0)
  | succ m ih =>
    rw [tailWord_succ, NFA.evalFrom_append, NFA.evalFrom_singleton, NFA.mem_stepSet]
    change (∃ s ∈ (liftNFA eH q).evalFrom {h | q h = a 0} (tailWord a m),
      eH s t ∧ q t = a (m + 1)) ↔ _
    constructor
    · rintro ⟨s, hs, het, hqt⟩
      obtain ⟨b, hb⟩ := (ih s).1 hs
      refine ⟨⟨Fin.snoc b.1 t, ?_, ?_⟩, by simp⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hb] using het
        · rw [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact b.2.1 j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hqt
        · simpa only [Fin.snoc_castSucc, Fin.val_castSucc] using b.2.2 j
    · rintro ⟨b, rfl⟩
      refine ⟨b.1 (Fin.last m).castSucc, (ih _).2
        ⟨restrictPrefix eH q a (Nat.le_succ m) b, rfl⟩, ?_, ?_⟩
      · exact b.2.1 (Fin.last m)
      · exact b.2.2 (Fin.last (m + 1))

private theorem prefixLift_iff_reachable (eH : H → H → Prop) (q : H → P)
    (a : ℕ → P) (m : ℕ) :
    PrefixLift eH q a m ↔
      ((liftNFA eH q).evalFrom {h | q h = a 0} (tailWord a m)).Nonempty := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b (Fin.last m), (reachable_endpoints eH q a m _).2 ⟨⟨b, hb⟩, rfl⟩⟩
  · rintro ⟨t, ht⟩
    obtain ⟨b, _⟩ := (reachable_endpoints eH q a m t).1 ht
    exact ⟨b.1, b.2⟩

private noncomputable def projectionDFA (eH : H → H → Prop)
    (eP : P → P → Prop) (q : H → P) (v₀ : P) : DFA P (Option (P × Set H)) := by
  classical
  exact {
    step := fun s v' => match s with
      | none => none
      | some (v, S) => if eP v v' then some (v', (liftNFA eH q).toDFA.step S v')
        else none
    start := some (v₀, {h | q h = v₀})
    accept := {s | ∃ v, s = some (v, ∅)} }

private theorem graphLanguage_id_iff (eP : P → P → Prop) (a : ℕ → P) :
    a ∈ graphLanguage eP id ↔ ∀ n, eP (a n) (a (n + 1)) := by
  constructor
  · rintro ⟨b, hb, hl⟩ n
    change ∀ n, b n = a n at hl
    simpa only [hl] using hb n
  · intro ha
    exact ⟨a, ha, fun _ => rfl⟩

private theorem projectionDFA_none (eH : H → H → Prop)
    (eP : P → P → Prop) (q : H → P) (v₀ : P) (w : List P) :
    (projectionDFA eH eP q v₀).evalFrom none w = none := by
  induction w with
  | nil => rfl
  | cons v w ih => simpa [DFA.evalFrom_cons, projectionDFA] using ih

private theorem projectionDFA_whole (eH : H → H → Prop)
    (eP : P → P → Prop) (q : H → P) (v₀ : P) (a : ℕ → P)
    (ha : a ∈ graphLanguage eP id) (S : Set H) (m : ℕ) :
    (projectionDFA eH eP q v₀).evalFrom (some (a 0, S)) (tailWord a m) =
      some (a m, (liftNFA eH q).evalFrom S (tailWord a m)) := by
  classical
  have he := (graphLanguage_id_iff eP a).1 ha
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [tailWord_succ, DFA.evalFrom_append_singleton, ih]
    simp only [projectionDFA, he m, if_true, NFA.toDFA,
      NFA.evalFrom_append, NFA.evalFrom_singleton]

private theorem projectionDFA_some_has_whole (eH : H → H → Prop)
    (eP : P → P → Prop) (q : H → P) (v₀ : P)
    (hP : ∀ v : P, ∃ a ∈ graphLanguage eP id, a 0 = v)
    (w : List P) (v t : P) (S T : Set H)
    (hw : (projectionDFA eH eP q v₀).evalFrom (some (v, S)) w = some (t, T)) :
    ∃ a ∈ graphLanguage eP id, a 0 = v ∧ tailWord a w.length = w ∧
      T = (liftNFA eH q).evalFrom S w := by
  classical
  induction w generalizing v S with
  | nil =>
    have h := Option.some.inj hw
    cases h
    obtain ⟨a, ha, h0⟩ := hP t
    exact ⟨a, ha, h0, rfl, rfl⟩
  | cons v' w ih =>
    by_cases he : eP v v'
    · have hw' : (projectionDFA eH eP q v₀).evalFrom
          (some (v', (liftNFA eH q).stepSet S v')) w = some (t, T) := by
        simpa only [DFA.evalFrom_cons, projectionDFA, he, if_true, NFA.toDFA] using hw
      obtain ⟨a, ha, h0, ht, hT⟩ := ih v' _ hw'
      let b : ℕ → P := fun n => match n with
        | 0 => v
        | n + 1 => a n
      refine ⟨b, (graphLanguage_id_iff eP b).2 ?_, rfl, ?_, hT⟩
      · intro n
        cases n with
        | zero => simpa only [b, h0] using he
        | succ n => exact (graphLanguage_id_iff eP a).1 ha n
      · simpa [tailWord, List.ofFn_succ, b, h0] using congrArg (List.cons v') ht
    · have hn := projectionDFA_none eH eP q v₀ w
      simp only [DFA.evalFrom_cons, projectionDFA, he, if_false] at hw
      change (projectionDFA eH eP q v₀).evalFrom none w = some (t, T) at hw
      rw [hn] at hw
      contradiction

/-- Failure of whole-path onto projection has a visible prefix of at most
`card P * 2 ^ card H + 1` vertices without a hidden lift. Every visible vertex
must start a whole path; the hidden graph need not be serial or live. -/
theorem exists_bounded_prefix_without_lift [Fintype P] [Fintype H]
    (eH : H → H → Prop) (eP : P → P → Prop) (q : H → P)
    (hq : ∀ h h', eH h h' → eP (q h) (q h'))
    (hP : ∀ v : P, ∃ a ∈ graphLanguage eP id, a 0 = v)
    (hnot : graphLanguage eH q ≠ graphLanguage eP id) :
    ∃ a ∈ graphLanguage eP id, ∃ m : ℕ,
      m ≤ Fintype.card P * 2 ^ Fintype.card H ∧ ¬ PrefixLift eH q a m := by
  classical
  have hn : ¬ ∀ a ∈ graphLanguage eP id, ∀ m, PrefixLift eH q a m := by
    intro h
    exact hnot ((graphLanguage_eq_iff_prefix_lifts eH eP q hq).2 h)
  push Not at hn
  obtain ⟨a, ha, m, hm⟩ := hn
  let D := projectionDFA eH eP q (a 0)
  have hempty : (liftNFA eH q).evalFrom {h | q h = a 0} (tailWord a m) = ∅ := by
    exact Set.not_nonempty_iff_eq_empty.1
      (fun h => hm ((prefixLift_iff_reachable eH q a m).2 h))
  have hacc : D.eval (tailWord a m) ∈ D.accept := by
    refine ⟨a m, ?_⟩
    change D.evalFrom (some (a 0, {h | q h = a 0})) (tailWord a m) = _
    rw [projectionDFA_whole eH eP q (a 0) a ha, hempty]
  have hex : ∃ n : ℕ, ∃ w : List P, w.length = n ∧ D.eval w ∈ D.accept :=
    ⟨m, tailWord a m, by simp [tailWord], hacc⟩
  obtain ⟨w, hwlen, hwacc⟩ := Nat.find_spec hex
  have hshort : w.length < Fintype.card (Option (P × Set H)) := by
    by_contra h
    obtain ⟨s, x, y, z, hw, _, hy, hx, _, hz⟩ :=
      D.evalFrom_split (s := D.start) (t := D.eval w) (by omega) rfl
    have heval : D.eval (x ++ z) = D.eval w := by
      change D.evalFrom D.start (x ++ z) = D.eval w
      rw [DFA.evalFrom_of_append, hx, hz]
    have hypos : 0 < y.length := List.length_pos_iff.2 hy
    have hlen : (x ++ z).length < Nat.find hex := by
      rw [hw, List.length_append, List.length_append] at hwlen
      simp only [List.length_append]
      omega
    exact (Nat.find_min hex hlen) ⟨x ++ z, rfl, heval ▸ hwacc⟩
  obtain ⟨t, ht⟩ := hwacc
  obtain ⟨b, hb, h0, htail, hT⟩ := projectionDFA_some_has_whole eH eP q (a 0)
    hP w (a 0) t {h | q h = a 0} ∅ ht
  refine ⟨b, hb, w.length, ?_, ?_⟩
  · have hcard : Fintype.card (Option (P × Set H)) =
        Fintype.card P * 2 ^ Fintype.card H + 1 := by simp
    rw [hcard] at hshort
    omega
  · intro hl
    have hr := (prefixLift_iff_reachable eH q b w.length).1 hl
    rw [htail, h0, ← hT] at hr
    exact Set.not_nonempty_empty hr

#print axioms graphLanguage_eq_iff_prefix_lifts
#print axioms exists_bounded_prefix_without_lift

end D5.S1.Dynamics.Shadowing
