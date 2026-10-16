/- GID: D5/S3/Arith/FibonacciAtomic/Observer/CombLiteralInstallationBounds
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Literal installation and Read lower bounds for original parity on all tree shapes. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
import D5.S1.Words.AdmissibleWords.AdmissibleCount
import D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer
import Mathlib.Tactic

/- These are uniform symbolic lower bounds over arbitrary controllers, tree
shapes and finite entry intervals. They are not bounded enumeration, a checker,
a numeric reduction or a certified finite instance; hence utility is none. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout leaves)
open D5.S1.Words.AdmissibleWords.AdmissibleCount (Adm)

/-- Original-label XOR, with alpha contributing zero. -/
def parity : Source → Bool
  | .of b => !b
  | .mul s t => xor (parity s) (parity t)

/-- All mutable information is in E; no epoch or original source is supplied. -/
structure Controller (E : Type) where
  initial : E
  instruction : E → NativeSerialMachine.Op E Bool

/-- Actual first-halt execution. The list records Read occurrences and their
absolute substitution epochs; the following index counts genuine Updates.
These annotations are a mathematical trace, not control storage. -/
inductive Run {E : Type} (M : Controller E) (u : Source) :
    E → Nat → List (E × Nat) → Nat → E → Bool → Prop where
  | halt {e : E} {t : Nat} {b : Bool} :
      M.instruction e = .stop b → Run M u e t [] 0 e b
  | read {e f : E} {t : Nat} {p : Address} {k : Reply → E}
      {qs : List (E × Nat)} {updates : Nat} {b : Bool} :
      M.instruction e = .read p k →
      Run M u (k (readout p (substitution^[t] u))) t qs updates f b →
      Run M u e t ((e,t) :: qs) updates f b
  | update {e k f : E} {t : Nat} {qs : List (E × Nat)} {updates : Nat} {b : Bool} :
      M.instruction e = .applyRho k → Run M u k (t + 1) qs updates f b →
      Run M u e t qs (updates + 1) f b
  | internal {e k f : E} {t : Nat} {qs : List (E × Nat)} {updates : Nat} {b : Bool} :
      M.instruction e = .localStep k → Run M u k t qs updates f b →
      Run M u e t qs updates f b

/-- Correctness and sourcewise termination on every full ordered h-leaf tree
and every allowed entry. No uniform stopping time is required. -/
def Correct {E : Type} (M : Controller E) (h T : Nat) : Prop :=
  ∀ u : Source, u.length = h → ∀ t, t ≤ T →
    (∃ qs updates f b, Run M u M.initial t qs updates f b) ∧
    (∀ qs updates f b, Run M u M.initial t qs updates f b → b = parity u)

/-- Every successful promised run executes zero genuine Updates. Unreachable
Update rows are permitted. -/
def Static {E : Type} (M : Controller E) (h T : Nat) : Prop :=
  ∀ u : Source, u.length = h → ∀ t, t ≤ T →
    ∀ qs updates f b, Run M u M.initial t qs updates f b → updates = 0

/-- The query states include installed rows never reached on a promised run. -/
def IsQuery {E : Type} (M : Controller E) (e : E) : Prop :=
  ∃ p k, M.instruction e = .read p k

/-- A total readout of the fixed literal field, with a dummy value off queries. -/
def literal {E : Type} (M : Controller E) (e : E) : Address :=
  match M.instruction e with
  | .read p _ => p
  | _ => []

noncomputable def queries {E : Type} [Fintype E] (M : Controller E) : Finset E :=
  @Finset.filter E (IsQuery M) (Classical.decPred _) Finset.univ

noncomputable def halts {E : Type} [Fintype E] (M : Controller E) : Finset E :=
  @Finset.filter E (fun e => ∃ b, M.instruction e = .stop b)
    (Classical.decPred _) Finset.univ

noncomputable def queryCone {E : Type} [Fintype E]
    (M : Controller E) (p : Address) : Finset E := by
  classical
  exact (queries M).filter (fun e => p.IsPrefix (literal M e))

private theorem iterate_pair (t : Nat) (u v : Source) :
    substitution^[t] (.mul u v) = .mul (substitution^[t] u) (substitution^[t] v) :=
  Function.Semiconj₂.iterate (fun x y => substitution.map_mul x y) t u v

/-- One sibling alpha leaf at each strict prefix and a chosen tip label. -/
def comb : Address → Bool → Source
  | [], b => .of b
  | false :: p, b => .mul (comb p b) (.of true)
  | true :: p, b => .mul (.of true) (comb p b)

private theorem comb_data (p : Address) (b : Bool) :
    (comb p b).length = p.length + 1 ∧ parity (comb p b) = !b := by
  induction p with
  | nil => simp [comb, FreeMagma.length, parity]
  | cons d p ih =>
      cases d <;> simp [comb, FreeMagma.length, parity, ih.1, ih.2, Nat.add_comm]

private theorem comb_outside (p q : Address) (b c : Bool) (t : Nat)
    (outside : ¬ p.IsPrefix q) :
    readout q (substitution^[t] (comb p b)) =
      readout q (substitution^[t] (comb p c)) := by
  induction p generalizing q with
  | nil => exact (outside (by simp)).elim
  | cons d p ih =>
      cases q with
      | nil => cases d <;> simp [comb, readout]
      | cons a q =>
          cases d <;> cases a <;> simp only [comb, iterate_pair, readout]
          · exact ih q (fun h => outside (by simpa using h))
          · exact ih q (fun h => outside (by simpa using h))

private theorem comb_tip (p s : Address) (b : Bool) (t : Nat) :
    readout (p ++ s) (substitution^[t] (comb p b)) =
      readout s (substitution^[t] (.of b)) := by
  induction p with
  | nil => rfl
  | cons d p ih => cases d <;> simpa only [comb, iterate_pair, List.cons_append, readout] using ih

theorem run_halt {E : Type} {M : Controller E} {u : Source}
    {e f : E} {t : Nat} {qs : List (E × Nat)} {updates : Nat} {b : Bool}
    (run : Run M u e t qs updates f b) : M.instruction f = .stop b := by
  induction run with
  | halt row => exact row
  | read _ _ ih => exact ih
  | update _ _ ih => exact ih
  | internal _ _ ih => exact ih

theorem run_queries {E : Type} {M : Controller E} {u : Source}
    {e f : E} {t : Nat} {qs : List (E × Nat)} {updates : Nat} {b : Bool}
    (run : Run M u e t qs updates f b) : ∀ z ∈ qs, IsQuery M z.1 := by
  induction run with
  | halt => simp
  | @read e f t p k qs updates b row tail ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨p, k, row⟩
      · exact ih z hz
  | update _ _ ih => exact ih
  | internal _ _ ih => exact ih

theorem run_replay {E : Type} {M : Controller E} {u v : Source}
    {e f : E} {t : Nat} {qs : List (E × Nat)} {updates : Nat} {b : Bool}
    (run : Run M u e t qs updates f b)
    (agree : ∀ z ∈ qs, readout (literal M z.1) (substitution^[z.2] u) =
      readout (literal M z.1) (substitution^[z.2] v)) :
    Run M v e t qs updates f b := by
  induction run with
  | halt row => exact .halt row
  | @read e f t p k qs updates b row tail ih =>
      have hr := agree (e,t) (by simp)
      simp only [literal, row] at hr
      have rest := ih (fun z hz => agree z (by simp [hz]))
      rw [hr] at rest
      exact .read row rest
  | update row _ ih => exact .update row (ih agree)
  | internal row _ ih => exact .internal row (ih agree)

private theorem separating_read {E : Type} {M : Controller E} {h T : Nat}
    (correct : Correct M h T) {u v : Source} (hu : u.length = h)
    (hv : v.length = h) (different : parity u ≠ parity v)
    {t : Nat} (ht : t ≤ T) {qs : List (E × Nat)} {updates : Nat} {f : E} {b : Bool}
    (run : Run M u M.initial t qs updates f b) :
    ∃ z ∈ qs, readout (literal M z.1) (substitution^[z.2] u) ≠
      readout (literal M z.1) (substitution^[z.2] v) := by
  by_contra! same
  exact different (((correct u hu t ht).2 qs updates f b run).symm.trans
    ((correct v hv t ht).2 qs updates f b (run_replay run same)))

private theorem comb_separates {E : Type} [Fintype E] (M : Controller E)
    {n T : Nat} (correct : Correct M (n + 1) T) (p : Address) (hp : p.length = n)
    (t : Nat) (ht : t ≤ T) :
    ∃ e ∈ queryCone M p, ∃ a,
      readout (literal M e) (substitution^[a] (comb p true)) ≠
        readout (literal M e) (substitution^[a] (comb p false)) := by
  obtain ⟨qs, updates, f, b, run⟩ :=
    (correct (comb p true) (by rw [(comb_data p true).1, hp]) t ht).1
  obtain ⟨z, hz, different⟩ := separating_read correct
    (by rw [(comb_data p true).1, hp]) (by rw [(comb_data p false).1, hp])
    (by simp [(comb_data p true).2, (comb_data p false).2]) ht run
  have hpref : p.IsPrefix (literal M z.1) := by
    by_contra outside
    exact different (comb_outside p _ true false z.2 outside)
  refine ⟨z.1, ?_, z.2, different⟩
  simpa [queryCone, queries] using And.intro (run_queries run z hz) hpref

private theorem equal_depth_prefix {p q r : Address}
    (hp : p.IsPrefix r) (hq : q.IsPrefix r) (len : p.length = q.length) : p = q := by
  rw [List.prefix_iff_eq_take] at hp hq
  rw [hp, hq, len]

private theorem cone_disjoint {E : Type} [Fintype E] (M : Controller E)
    {p q : Address} (len : p.length = q.length) (ne : p ≠ q) :
    Disjoint (queryCone M p) (queryCone M q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e hp hq
  simp only [queryCone, Finset.mem_filter] at hp hq
  exact ne (equal_depth_prefix hp.2 hq.2 len)

private theorem cone_sum_le {E : Type} [Fintype E] (M : Controller E) (n : Nat) :
    (∑ p : Fin n → Bool, (queryCone M (List.ofFn p)).card) ≤ (queries M).card := by
  classical
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro e he
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hp).1
  · intro p _ q _ hpq
    exact cone_disjoint M (by simp) (fun eq => hpq (List.ofFn_injective eq))

private theorem two_halts {E : Type} [Fintype E] (M : Controller E)
    {n T : Nat} (correct : Correct M (n + 1) T) : 2 ≤ (halts M).card := by
  classical
  let p : Address := List.replicate n false
  obtain ⟨qa, ua, ea, ba, ra⟩ :=
    (correct (comb p true) (by simp [(comb_data p true).1, p]) 0 (by omega)).1
  obtain ⟨qb, ub, eb, bb, rb⟩ :=
    (correct (comb p false) (by simp [(comb_data p false).1, p]) 0 (by omega)).1
  have oa :=
    (correct (comb p true) (by simp [(comb_data p true).1, p]) 0 (by omega)).2 qa ua ea ba ra
  have ob :=
    (correct (comb p false) (by simp [(comb_data p false).1, p]) 0 (by omega)).2 qb ub eb bb rb
  have ha : M.instruction ea = .stop false := by
    simpa [(comb_data p true).2] using
      (run_halt ra).trans (congrArg NativeSerialMachine.Op.stop oa)
  have hb : M.instruction eb = .stop true := by
    simpa [(comb_data p false).2] using
      (run_halt rb).trans (congrArg NativeSerialMachine.Op.stop ob)
  have ne : ea ≠ eb := by intro eq; rw [eq, hb] at ha; cases ha
  have sub : {ea, eb} ⊆ halts M := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · simp [halts, ha]
    · have eq := Finset.mem_singleton.mp he
      subst e
      simp [halts, hb]
  simpa [ne] using Finset.card_le_card sub

theorem query_halt_card {E : Type} [Fintype E] (M : Controller E) :
    (queries M).card + (halts M).card ≤ Fintype.card E := by
  classical
  have disjoint : Disjoint (queries M) (halts M) := by
    apply Finset.disjoint_left.mpr
    intro e hq hh
    obtain ⟨p,k,hp⟩ : IsQuery M e := by simpa [queries] using hq
    obtain ⟨b,hb⟩ : ∃ b, M.instruction e = .stop b := by simpa [halts] using hh
    rw [hp] at hb
    cases hb
  rw [← Finset.card_union_of_disjoint disjoint]
  exact Finset.card_le_univ _


private theorem leaf_alternative (u : Source) (p : Address) (hp : p ∈ leaves u) :
    ∃ v : Source, v.length = u.length ∧ parity v ≠ parity u ∧
      ∀ (t : Nat) (q : Address), ¬ p.IsPrefix q →
        readout q (substitution^[t] u) = readout q (substitution^[t] v) := by
  induction u generalizing p with
  | of b =>
      have ep : p = [] := by simpa [leaves] using hp
      subst p
      refine ⟨.of (!b), rfl, ?_, ?_⟩
      · cases b <;> decide
      · intro t q outside
        exact (outside (by simp)).elim
  | mul l r il ir =>
      simp only [leaves, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
      · obtain ⟨v, hv, different, outside⟩ := il a ha
        refine ⟨.mul v r, by simp [FreeMagma.length, hv], ?_, ?_⟩
        · simp only [parity]
          intro equal
          exact different (Bool.xor_left_inj.mp equal)
        · intro t q hq
          rw [iterate_pair, iterate_pair]
          cases q with
          | nil => rfl
          | cons b q =>
              cases b with
              | false => exact outside t q (fun h => hq (by simpa using h))
              | true => rfl
      · obtain ⟨v, hv, different, outside⟩ := ir a ha
        refine ⟨.mul l v, by simp [FreeMagma.length, hv], ?_, ?_⟩
        · simp only [parity]
          intro equal
          exact different (Bool.xor_right_inj.mp equal)
        · intro t q hq
          rw [iterate_pair, iterate_pair]
          cases q with
          | nil => rfl
          | cons b q =>
              cases b with
              | false => rfl
              | true => exact outside t q (fun h => hq (by simpa using h))

private theorem leaf_subtree (u : Source) (p : Address) (hp : p ∈ leaves u) :
    ∃ b, ActualLeafHistoryRigidity.subtree p u = some (.of b) := by
  induction u generalizing p with
  | of b =>
      have ep : p = [] := by simpa [leaves] using hp
      exact ⟨b, by simp [ep, ActualLeafHistoryRigidity.subtree]⟩
  | mul l r il ir =>
      simp only [leaves, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
      · exact il a ha
      · exact ir a ha

private theorem leaf_cones_disjoint (u : Source) {p q r : Address}
    (hp : p ∈ leaves u) (hq : q ∈ leaves u)
    (pr : p.IsPrefix r) (qr : q.IsPrefix r) : p = q := by
  obtain ⟨b, hb⟩ := leaf_subtree u p hp
  obtain ⟨c, hc⟩ := leaf_subtree u q hq
  have rigid := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.1
  rcases List.prefix_or_prefix_of_prefix pr qr with pq | qp
  · exact (rigid u p q b c hb hc pq).1
  · exact (rigid u q p c b hc hb qp).1.symm

/-- Each independent original leaf forces its own actual Read occurrence on
any successful run, at the genuine common update epoch of the two sources. -/
theorem successful_run_read_lower_bound {E : Type} {M : Controller E} {h T : Nat}
    (correct : Correct M h T) {u : Source} (hu : u.length = h)
    {t : Nat} (ht : t ≤ T) {qs : List (E × Nat)} {updates : Nat} {f : E} {b : Bool}
    (run : Run M u M.initial t qs updates f b) : h ≤ qs.length := by
  classical
  let L := (leaves u).toFinset
  have needed (p : L) : ∃ z : {z // z ∈ qs.toFinset}, p.val.IsPrefix (literal M z.val.1) := by
    have hp : p.val ∈ leaves u := List.mem_toFinset.mp p.property
    obtain ⟨v, length, different, outside⟩ := leaf_alternative u p.val hp
    obtain ⟨z, hz, separates⟩ := separating_read correct hu (length.trans hu)
      (Ne.symm different) ht run
    refine ⟨⟨z, List.mem_toFinset.mpr hz⟩, ?_⟩
    by_contra absent
    exact separates (outside z.2 (literal M z.1) absent)
  choose pick property using needed
  have injective : Function.Injective pick := by
    intro p q eq
    apply Subtype.ext
    apply leaf_cones_disjoint u (List.mem_toFinset.mp p.property)
      (List.mem_toFinset.mp q.property) (property p)
    rw [eq]
    exact property q
  have count := Fintype.card_le_of_injective pick injective
  simp only [Fintype.card_coe] at count
  have leaves_count : L.card = u.length :=
    (ActualImageSevenLeafSeparation.seven_leaf_separation.1 u).1
  rw [leaves_count, hu] at count
  exact le_trans count (List.toFinset_card_le _)

/-- The installed union over all comb shapes requires exponentially many
fixed-literal query words and both output words, even with genuine updates
and arbitrary deterministic internal work. No restriction on control changes
is needed for this lower bound. Any injective no-11 encoding
therefore has the stated Fibonacci capacity. -/
theorem comb_installed_lower_bounds {E : Type} [Fintype E] (M : Controller E)
    {h T : Nat} (positive : 0 < h) (correct : Correct M h T) :
    2 ^ (h - 1) ≤ (queries M).card ∧ 2 ≤ (halts M).card ∧
    2 ^ (h - 1) + 2 ≤ Fintype.card E ∧
    (∀ (width : Nat) (encode : E → {w : Fin width → Bool // Adm width w}),
      Function.Injective encode → 2 ^ (h - 1) + 2 ≤ Nat.fib (width + 2)) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  have lower : 2 ^ n ≤ (queries M).card := by
    have each : ∀ p : Fin n → Bool, 1 ≤ (queryCone M (List.ofFn p)).card := by
      intro p
      obtain ⟨e, he, _⟩ := comb_separates M correct (List.ofFn p) (by simp) 0 (by omega)
      exact Finset.card_pos.mpr ⟨e, he⟩
    have sum := Finset.sum_le_sum (s := Finset.univ) (fun p _ => each p)
    have bound := le_trans sum (cone_sum_le M n)
    simpa using bound
  have halt_bound := two_halts M correct
  have total : 2 ^ n + 2 ≤ Fintype.card E := by
    have count := query_halt_card M
    omega
  refine ⟨by simpa using lower, halt_bound, by simpa using total, ?_⟩
  intro width encode injective
  have capacity := Fintype.card_le_of_injective encode injective
  rw [D5.S1.Words.AdmissibleWords.AdmissibleCount.admissibleWord_card_eq_fib] at capacity
  simpa using le_trans total capacity

/-- Weighted literal depth, with left cost one and right cost two. -/
def weight : Address → Nat
  | [] => 0
  | false :: p => weight p + 1
  | true :: p => weight p + 2

def atom (n : Nat) : Source := substitution^[n] (.of true)

private theorem atom_pair (n : Nat) : atom (n + 2) = .mul (atom (n + 1)) (atom n) := by
  have relation := (SourceTransportCentralizer.source_transport_centralizer.1 (atom n)).mpr ⟨n,rfl⟩
  simpa only [atom, Function.iterate_succ_apply', Nat.add_assoc] using relation

private theorem atomic_extremes (p : Address) (n : Nat) :
    (n < weight p → readout p (atom n) = .absent) ∧
    (weight p + 2 ≤ n → readout p (atom n) = .branch) := by
  induction p generalizing n with
  | nil =>
      constructor
      · simp [weight]
      · intro hn
        have he : n = (n - 2) + 2 := by simp only [weight] at hn; omega
        rw [he, atom_pair]
        rfl
  | cons d p ih =>
      cases n with
      | zero =>
          cases d <;> constructor
          all_goals first | intro; rfl | simp [weight]
      | succ n =>
          cases n with
          | zero =>
              cases d <;> constructor
              all_goals first | intro; rfl | simp [weight]
          | succ n =>
              rw [show n + 1 + 1 = n + 2 by omega, atom_pair]
              cases d <;> simp only [readout, weight]
              · exact ⟨fun h => (ih (n + 1)).1 (by omega),
                  fun h => (ih (n + 1)).2 (by omega)⟩
              · exact ⟨fun h => (ih n).1 (by omega),
                  fun h => (ih n).2 (by omega)⟩

theorem adjacent_window (p : Address) (t : Nat)
    (different : readout p (atom t) ≠ readout p (atom (t + 1))) :
    weight p ≤ t + 1 ∧ t ≤ weight p + 1 := by
  constructor
  · by_contra h
    exact different (((atomic_extremes p t).1 (by omega)).trans
      ((atomic_extremes p (t + 1)).1 (by omega)).symm)
  · by_contra h
    exact different (((atomic_extremes p t).2 (by omega)).trans
      ((atomic_extremes p (t + 1)).2 (by omega)).symm)

theorem static_epochs {E : Type} {M : Controller E} {u : Source}
    {e f : E} {t : Nat} {qs : List (E × Nat)} {updates : Nat} {b : Bool}
    (run : Run M u e t qs updates f b) (zero : updates = 0) :
    ∀ z ∈ qs, z.2 = t := by
  induction run with
  | halt => simp
  | read row tail ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · rfl
      · exact ih zero z hz
  | update row tail ih => omega
  | internal row tail ih => exact ih zero

private theorem static_comb_separates {E : Type} [Fintype E] (M : Controller E)
    {n T : Nat} (correct : Correct M (n + 1) T) (static : Static M (n + 1) T)
    (p : Address) (hp : p.length = n) (t : Nat) (ht : t ≤ T) :
    ∃ e ∈ queryCone M p,
      readout ((literal M e).drop n) (atom t) ≠
        readout ((literal M e).drop n) (atom (t + 1)) := by
  have hu : (comb p true).length = n + 1 := by rw [(comb_data p true).1, hp]
  obtain ⟨qs, updates, f, b, run⟩ :=
    (correct (comb p true) hu t ht).1
  obtain ⟨z, hz, different⟩ := separating_read correct hu
    (by rw [(comb_data p false).1, hp])
    (by simp [(comb_data p true).2, (comb_data p false).2]) ht run
  have epoch := static_epochs run (static _ hu _ ht qs updates f b run) z hz
  rw [epoch] at different
  have hpref : p.IsPrefix (literal M z.1) := by
    by_contra outside
    exact different (comb_outside p _ true false t outside)
  have suffix : p ++ (literal M z.1).drop n = literal M z.1 := by
    have take : (literal M z.1).take n = p := by
      simpa only [hp] using (List.prefix_iff_eq_take.mp hpref).symm
    rw [← take, List.take_append_drop]
  have next_atom : substitution^[t] (.of false) = atom (t + 1) := by
    rw [atom, Function.iterate_succ_apply]
    rfl
  refine ⟨z.1, ?_, ?_⟩
  · simpa [queryCone, queries] using And.intro (run_queries run z hz) hpref
  · rw [← suffix, comb_tip, comb_tip, next_atom] at different
    exact different

private theorem static_cone_bound {E : Type} [Fintype E] (M : Controller E)
    {n T : Nat} (correct : Correct M (n + 1) T) (static : Static M (n + 1) T)
    (p : Address) (hp : p.length = n) :
    (T + 3)/3 ≤ (queryCone M p).card := by
  classical
  have select (t : Fin (T + 1)) : ∃ e : queryCone M p,
      weight ((literal M e.val).drop n) ≤ t.val + 1 ∧
        t.val ≤ weight ((literal M e.val).drop n) + 1 := by
    obtain ⟨e, he, separates⟩ := static_comb_separates M correct static p hp t.val (by omega)
    exact ⟨⟨e,he⟩, adjacent_window _ _ separates⟩
  choose pick bounds using select
  let code (t : Fin (T + 1)) : (queryCone M p) × Fin 3 :=
    (pick t, ⟨t.val + 1-weight ((literal M (pick t).val).drop n), by
      have ht := bounds t
      omega⟩)
  have injective : Function.Injective code := by
    intro t s eq
    have same : pick t = pick s := congrArg Prod.fst eq
    have offset := congrArg (fun x : (queryCone M p) × Fin 3 => x.2.val) eq
    dsimp only [code] at offset
    have bt := bounds t
    have bs := bounds s
    rw [same] at offset bt
    apply Fin.ext
    omega
  have count := Fintype.card_le_of_injective code injective
  simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_coe] at count
  omega

/-- Static installations must cover every entry separately in every comb
cone. One installed literal covers at most three consecutive entries.
The ceiling is written as (T + 3)/3, including T=0. -/
theorem static_comb_installed_lower_bounds {E : Type} [Fintype E] (M : Controller E)
    {h T : Nat} (positive : 0 < h) (correct : Correct M h T)
    (static : Static M h T) :
    2 ^ (h - 1) * ((T + 3)/3) ≤ (queries M).card ∧ 2 ≤ (halts M).card ∧
    2 ^ (h - 1) * ((T + 3)/3) + 2 ≤ Fintype.card E ∧
    (∀ (width : Nat) (encode : E → {w : Fin width → Bool // Adm width w}),
      Function.Injective encode → 2 ^ (h - 1) * ((T + 3)/3) + 2 ≤ Nat.fib (width + 2)) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  have lower : 2 ^ n * ((T + 3)/3) ≤ (queries M).card := by
    have sum := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
      static_cone_bound M correct static (List.ofFn (p : Fin n → Bool)) (by simp))
    simpa using le_trans sum (cone_sum_le M n)
  have halt_bound := two_halts M correct
  have total : 2 ^ n * ((T + 3)/3) + 2 ≤ Fintype.card E := by
    have count := query_halt_card M
    omega
  refine ⟨by simpa using lower, halt_bound, by simpa using total, ?_⟩
  intro width encode injective
  have capacity := Fintype.card_le_of_injective encode injective
  rw [D5.S1.Words.AdmissibleWords.AdmissibleCount.admissibleWord_card_eq_fib] at capacity
  simpa using le_trans total capacity

end D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
