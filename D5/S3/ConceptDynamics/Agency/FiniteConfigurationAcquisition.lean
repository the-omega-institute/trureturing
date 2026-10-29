/- GID: D5/S3/ConceptDynamics/Agency/FiniteConfigurationAcquisition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Agency/FiniteConfigurationAcquisition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: History-based safe acquisition is equivalent to common enabled events and has a finite table implementation. -/

import D5.S3.ConceptDynamics.Agency.DeterministicSafePolicyExistence
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! Legal insertion runs and finite-table acquisition for arbitrary configuration families. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Agency.FiniteConfigurationAcquisition

universe u v
variable {E : Type u} [Fintype E] [DecidableEq E]

abbrev State (F : Finset (Finset E)) := {C // C ∈ F}

def Enabled (F : Finset (Finset E)) (C : State F) (e : E) : Prop :=
  e ∉ C.val ∧ insert e C.val ∈ F

def Sink (F : Finset (Finset E)) (C : State F) : Prop :=
  ∀ e, ¬ Enabled F C e

def successor (F : Finset (Finset E)) (C : State F) (e : E)
    (h : Enabled F C e) : State F := ⟨insert e C.val, h.2⟩

def remaining (F : Finset (Finset E)) (C : State F) : ℕ :=
  Fintype.card E - C.val.card

/-- The first component is the current symbol; the list stores all earlier
requested events and their preceding symbols, in reverse chronological order. -/
abbrev History (E : Type u) (Q : Type v) := Q × List (E × Q)

abbrev Decision (F : Finset (Finset E)) := State F ⊕ E

def record {Q : Type v} (h : History E Q) (e : E) (q : Q) : History E Q :=
  (q, (e, h.1) :: h.2)

/-- Only a requested legal insertion changes the state. A stop is successful
exactly when its claim is the actual current configuration. -/
inductive Run {F : Finset (Finset E)} {Q : Type v}
    (r : State F → Q) (p : History E Q → Decision F) :
    State F → History E Q → ℕ → Prop
  | stop (C : State F) (h : History E Q) (hp : p h = Sum.inl C) : Run r p C h 0
  | step (C : State F) (h : History E Q) (e : E) (n : ℕ)
      (hp : p h = Sum.inr e) (he : Enabled F C e)
      (tail : Run r p (successor F C e he)
        (record h e (r (successor F C e he))) n) : Run r p C h (n + 1)

/-- No restriction on retained history or the mathematical decision function
is used in this semantic upper class of protocols. -/
def Acquires {F : Finset (Finset E)} {Q : Type v}
    (r : State F → Q) (p : History E Q → Decision F) : Prop :=
  ∀ C, ∃ n, Run r p C (r C, []) n

def CommonEnabled {F : Finset (Finset E)} {Q : Type v}
    (r : State F → Q) : Prop :=
  ∀ C, (∃ D, r D = r C ∧ D ≠ C) →
    ∃ e, ∀ D, r D = r C → Enabled F D e

def IsolatedSinks {F : Finset (Finset E)} {Q : Type v}
    (r : State F → Q) : Prop :=
  (∀ C, Sink F C → ∀ D, r D = r C → D = C) ∧
  (∀ C, ¬ Sink F C → ∃ e, ∀ D, r D = r C → Enabled F D e)

/-- A literal finite instruction table; equality tests are on natural symbol
codes. Evaluation recurses on this list, and does no query of the source. -/
def lookup {F : Finset (Finset E)} (q : ℕ) (fallback : Decision F) :
    List (ℕ × Decision F) → Decision F
  | [] => fallback
  | (key, value) :: tail => if q = key then value else lookup q fallback tail

def tablePolicy {F : Finset (Finset E)}
    (table : List (ℕ × Decision F)) (fallback : Decision F)
    (h : History E ℕ) : Decision F := lookup h.1 fallback table

/-- The code table is injective on the effective image. The actual policy is
the finite lookup program above, not an assumed successful executor. -/
def FiniteAcquirable {F : Finset (Finset E)} {Q : Type v}
    (r : State F → Q) : Prop :=
  ∃ encode : Q → ℕ,
    (∀ C D, encode (r C) = encode (r D) → r C = r D) ∧
    ∃ (table : List (ℕ × Decision F)) (fallback : Decision F),
      ∀ C, ∃ n, n ≤ remaining F C ∧
        Run (encode ∘ r) (tablePolicy table fallback) C (encode (r C), []) n

noncomputable def symbols {F : Finset (Finset E)} {Q : Type v}
    (r : State F → Q) : Finset Q := by
  classical
  exact Finset.univ.image r

private theorem mem_symbols {F : Finset (Finset E)} {Q : Type v}
    (r : State F → Q) (C : State F) : r C ∈ symbols r := by
  classical
  exact Finset.mem_image.mpr ⟨C, Finset.mem_univ _, rfl⟩

private theorem run_stop {F : Finset (Finset E)} {Q : Type v}
    {r : State F → Q} {p : History E Q → Decision F}
    {C A : State F} {h : History E Q} {n : ℕ}
    (hr : Run r p C h n) (hp : p h = Sum.inl A) : A = C := by
  cases hr with
  | stop C h hs => exact Sum.inl.inj (hp.symm.trans hs)
  | step C h e n hs he tail => simp [hp] at hs

private theorem run_request {F : Finset (Finset E)} {Q : Type v}
    {r : State F → Q} {p : History E Q → Decision F}
    {C : State F} {e : E} {h : History E Q} {n : ℕ}
    (hr : Run r p C h n) (hp : p h = Sum.inr e) : Enabled F C e := by
  cases hr with
  | stop C h hs => simp [hp] at hs
  | step C h a n hs he tail =>
    have : e = a := Sum.inr.inj (hp.symm.trans hs)
    simpa [this] using he

private theorem first_decision {F : Finset (Finset E)} {Q : Type v}
    {r : State F → Q} {p : History E Q → Decision F}
    (success : Acquires r p) : CommonEnabled r := by
  intro C hC
  cases hp : p (r C, []) with
  | inl A =>
    obtain ⟨D, hD, hne⟩ := hC
    obtain ⟨n, hn⟩ := success C
    obtain ⟨m, hm⟩ := success D
    have hAC := run_stop hn hp
    have hAD := run_stop hm (by simpa only [hD] using hp)
    exact (hne (hAD.symm.trans hAC)).elim
  | inr e =>
    refine ⟨e, ?_⟩
    intro D hD
    obtain ⟨n, hn⟩ := success D
    exact run_request hn (by simpa only [hD] using hp)

private theorem sink_equivalence {F : Finset (Finset E)} {Q : Type v}
    (r : State F → Q) : CommonEnabled r ↔ IsolatedSinks r := by
  classical
  constructor
  · intro hc
    constructor
    · intro C hs D hD
      by_contra hne
      obtain ⟨e, he⟩ := hc C ⟨D, hD, hne⟩
      exact hs e (he C rfl)
    · intro C hn
      by_cases hmany : ∃ D, r D = r C ∧ D ≠ C
      · exact hc C hmany
      · have hex : ∃ e, Enabled F C e := by simpa [Sink] using hn
        obtain ⟨e, he⟩ := hex
        refine ⟨e, ?_⟩
        intro D hD
        have : D = C := by by_contra hne; exact hmany ⟨D, hD, hne⟩
        simpa [this] using he
  · rintro ⟨hs, hn⟩ C ⟨D, hD, hne⟩
    apply hn C
    intro hc
    exact hne (hs C hc D hD)

private theorem rank_decreases {F : Finset (Finset E)} (C : State F)
    (e : E) (he : Enabled F C e) :
    remaining F (successor F C e he) + 1 = remaining F C := by
  have hcard := Finset.card_le_univ (s := insert e C.val)
  have hins := Finset.card_insert_of_notMem he.1
  simp only [remaining, successor]
  rw [hins] at hcard ⊢
  omega

private theorem execute_stationary {F : Finset (Finset E)} {Q : Type v}
    (r : State F → Q) (select : Q → Decision F)
    (safe : ∀ C, match select (r C) with
      | Sum.inl D => D = C
      | Sum.inr e => Enabled F C e) :
    ∀ C h, h.1 = r C → ∃ n, n ≤ remaining F C ∧
      Run r (fun h => select h.1) C h n := by
  have go : ∀ m C (h : History E Q), remaining F C = m → h.1 = r C →
      ∃ n, n ≤ remaining F C ∧ Run r (fun h => select h.1) C h n := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro C h hm hq
      cases hs : select (r C) with
      | inl D =>
        have hDC : D = C := by simpa only [hs] using safe C
        refine ⟨0, Nat.zero_le _, Run.stop C h ?_⟩
        simpa only [hq, hDC] using hs
      | inr e =>
        have he : Enabled F C e := by simpa only [hs] using safe C
        have hd := rank_decreases C e he
        have hlt : remaining F (successor F C e he) < m := by omega
        obtain ⟨n, hn, hr⟩ := ih _ hlt (successor F C e he)
          (record h e (r (successor F C e he))) rfl rfl
        refine ⟨n + 1, by omega, Run.step C h e n ?_ he hr⟩
        simpa only [hq] using hs
  intro C h hq
  exact go (remaining F C) C h rfl hq

private theorem lookup_map {F : Finset (Finset E)}
    (keys : List ℕ) (select : ℕ → Decision F) (fallback : Decision F)
    {q : ℕ} (hq : q ∈ keys) :
    lookup q fallback (keys.map fun k => (k, select k)) = select q := by
  induction keys with
  | nil => simp at hq
  | cons k keys ih =>
    by_cases he : q = k
    · simp [lookup, he]
    · simp only [List.mem_cons] at hq
      have ht : q ∈ keys := hq.resolve_left he
      simpa [lookup, he] using ih ht

private theorem finite_table {F : Finset (Finset E)} (hF : F.Nonempty)
    {Q : Type v} (r : State F → Q) (hc : CommonEnabled r) : FiniteAcquirable r := by
  classical
  let encode (q : Q) := (symbols r).toList.idxOf q
  have heq (C D : State F) (h : encode (r C) = encode (r D)) : r C = r D :=
    (List.idxOf_inj (by simpa using mem_symbols r C)).mp h
  let s : State F → ℕ := encode ∘ r
  have hcs : CommonEnabled s := by
    intro C ⟨D, hD, hne⟩
    obtain ⟨e, he⟩ := hc C ⟨D, heq D C hD, hne⟩
    exact ⟨e, fun A hA => he A (heq A C hA)⟩
  let legal (C : State F) : Set (Decision F) :=
    {a | match a with | Sum.inl D => D = C | Sum.inr e => Enabled F C e}
  have common : ∀ z : Set.range s,
      ({a | ∀ C, s C = z.val → a ∈ legal C} : Set (Decision F)).Nonempty := by
    intro z
    obtain ⟨C, hC⟩ := z.property
    by_cases hmany : ∃ D, s D = s C ∧ D ≠ C
    · obtain ⟨e, he⟩ := hcs C hmany
      exact ⟨Sum.inr e, fun D hD => he D (hD.trans hC.symm)⟩
    · refine ⟨Sum.inl C, ?_⟩
      intro D hD
      change C = D
      by_contra hne
      exact hmany ⟨D, hD.trans hC.symm, Ne.symm hne⟩
  obtain ⟨policy, hp⟩ :=
    (D5.S3.ConceptDynamics.Agency.DeterministicSafePolicyExistence.deterministic_safe_policy_exists_iff
      s legal).mpr common
  obtain ⟨C₀, hC₀⟩ := hF
  let fallback : Decision F := Sum.inl ⟨C₀, hC₀⟩
  let select (q : ℕ) : Decision F :=
    if hq : q ∈ Set.range s then policy ⟨q, hq⟩ else fallback
  have hsafe (C : State F) : select (s C) ∈ legal C := by
    have hmem : s C ∈ Set.range s := ⟨C, rfl⟩
    simpa only [select, dif_pos hmem] using hp ⟨s C, hmem⟩ C rfl
  let keys := (symbols s).toList
  let table := keys.map fun q => (q, select q)
  have heval (C : State F) : lookup (s C) fallback table = select (s C) :=
    lookup_map keys select fallback (by simpa [keys] using mem_symbols s C)
  have htable (C : State F) :
      (match lookup (s C) fallback table with
      | Sum.inl D => D = C | Sum.inr e => Enabled F C e) := by
    rw [heval]
    exact hsafe C
  refine ⟨encode, heq, table, fallback, ?_⟩
  intro C
  exact execute_stationary s (fun q => lookup q fallback table) htable C (s C, []) rfl

private theorem decoded_run {F : Finset (Finset E)} {Q : Type v}
    (r : State F → Q) (encode : Q → ℕ)
    (p : History E ℕ → Decision F) :
    ∀ C h n, Run (encode ∘ r) p C
      (encode h.1, h.2.map fun eq => (eq.1, encode eq.2)) n →
      Run r (fun h => p (encode h.1, h.2.map fun eq => (eq.1, encode eq.2))) C h n := by
  intro C h n hr
  generalize hx : (encode h.1, h.2.map fun eq => (eq.1, encode eq.2)) = code at hr
  induction hr generalizing h with
  | stop C code hp =>
    exact Run.stop C h (by simpa only [hx] using hp)
  | step C code e n hp he tail ih =>
    refine Run.step C h e n (by simpa only [hx] using hp) he ?_
    apply ih (record h e (r (successor F C e he)))
    simp [record, hx.symm]

/-- Full acquired-history policies, common enabled events on every nonsingleton
fiber, and isolated sinks with common events on the other fibers are equivalent.
The equivalent finite program performs at most the initial missing-event count
of legal insertions and returns its actual stopping configuration. -/
theorem acquisition_criterion {F : Finset (Finset E)} (hF : F.Nonempty)
    {Q : Type v} (r : State F → Q) :
    ((∃ p : History E Q → Decision F, Acquires r p) ↔ CommonEnabled r) ∧
    (CommonEnabled r ↔ IsolatedSinks r) ∧
    (CommonEnabled r ↔ FiniteAcquirable r) := by
  have finite_to_history : FiniteAcquirable r → ∃ p, Acquires r p := by
    rintro ⟨encode, _, table, fallback, hs⟩
    refine ⟨fun h => tablePolicy table fallback
      (encode h.1, h.2.map fun eq => (eq.1, encode eq.2)), ?_⟩
    intro C
    obtain ⟨n, _, hn⟩ := hs C
    exact ⟨n, decoded_run r encode (tablePolicy table fallback) C (r C, []) n hn⟩
  refine ⟨⟨?_, ?_⟩, sink_equivalence r, ⟨finite_table hF r, ?_⟩⟩
  · rintro ⟨p, hp⟩
    exact first_decision hp
  · intro hc
    exact finite_to_history (finite_table hF r hc)
  · intro hf
    obtain ⟨p, hp⟩ := finite_to_history hf
    exact first_decision hp

#print axioms acquisition_criterion

end D5.S3.ConceptDynamics.Agency.FiniteConfigurationAcquisition
