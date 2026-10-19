/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed outer low fillers recover every full-codebook choice at every large even weight. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.LowerRateLimit
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
open Filter Topology

/-- The positive representative of the half-weight modulo three. -/
def fillerJ (F : ℕ) : ℕ := if F / 2 % 3 = 0 then 3 else F / 2 % 3

/-- The extra six-letter blocks in the first low return. -/
def fillerQ (F : ℕ) : ℕ := (F / 2 - 13 * fillerJ F) / 3

def lowReturn (q : ℕ) : Return := ⟨1 + q, 1, by omega, by omega⟩

/-- Execution order puts the longer low return first. -/
def lowFiller (F : ℕ) : List Return :=
  lowReturn (fillerQ F) :: List.replicate (fillerJ F - 1) (lowReturn 0)

private theorem list_weight_append (xs ys : List Return) :
    listWeight (xs ++ ys) = listWeight xs + listWeight ys := by
  induction xs with
  | nil => simp [listWeight]
  | cons a xs ih => simp only [List.cons_append, listWeight, ih]; omega

/-- Every actual return list has even literal weight, irrespective of guards. -/
theorem actual_list_weight_even (xs : List Return) : Even (listWeight xs) := by
  induction xs with
  | nil => exact ⟨0, rfl⟩
  | cons a xs ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨3 * a.m + 10 * a.r + q, ?_⟩
    simp only [listWeight]
    omega

private theorem low_trace (K : ℕ) (hK : 2 ≤ K) (d : ℝ) (strict : Bool)
    (j : Side) (xs : List Return) (low : ∀ a ∈ xs, a.r = 1) (D : ℝ) :
    GuardTrace K d strict j xs D := by
  induction xs generalizing D with
  | nil => trivial
  | cons a xs ih =>
    have ha := low a (by simp)
    refine ⟨by omega, ?_, ?_⟩
    · intro high; omega
    · exact ih (fun a h => low a (by simp [h])) _

private theorem guard_append (K : ℕ) (d : ℝ) (strict : Bool) (j : Side)
    (xs ys : List Return) (D : ℝ) :
    GuardTrace K d strict j (xs ++ ys) D ↔
      GuardTrace K d strict j xs D ∧ GuardTrace K d strict j ys (execute j xs D) := by
  induction xs generalizing D with
  | nil => simp [GuardTrace, execute]
  | cons a xs ih => simp only [List.cons_append, GuardTrace, execute, ih]; tauto

/-- The prescribed filler realizes every even weight at least seventy-eight.
The congruence representative is unique, and every return is low at every seed. -/
theorem low_filler_geometry (F : ℕ) (even : Even F) (large : 78 ≤ F) :
    1 ≤ fillerJ F ∧ fillerJ F ≤ 3 ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 3 → F / 2 % 3 = i % 3 → i = fillerJ F) ∧
    F / 2 % 3 = fillerJ F % 3 ∧ 13 * fillerJ F ≤ F / 2 ∧
    3 ∣ F / 2 - 13 * fillerJ F ∧
    26 * fillerJ F + 6 * fillerQ F = F ∧
    listWeight (lowFiller F) = F ∧
    (∀ a ∈ lowFiller F, a.r = 1) ∧
    (∀ (K : ℕ), 2 ≤ K → ∀ (d : ℝ) (strict : Bool) (j : Side) (D : ℝ),
      GuardTrace K d strict j (lowFiller F) D) := by
  obtain ⟨v, hv⟩ := even
  have half : F / 2 * 2 = F := by omega
  have rem := Nat.mod_lt (F / 2) (by decide : 0 < 3)
  have bounds : 1 ≤ fillerJ F ∧ fillerJ F ≤ 3 := by
    dsimp [fillerJ]; split_ifs <;> omega
  have residue : F / 2 % 3 = fillerJ F % 3 := by
    dsimp [fillerJ]; split_ifs <;> omega
  have unique (i : ℕ) (hi : 1 ≤ i) (hi3 : i ≤ 3)
      (he : F / 2 % 3 = i % 3) : i = fillerJ F := by
    dsimp [fillerJ]; split_ifs <;> omega
  have nonnegative : 13 * fillerJ F ≤ F / 2 := by omega
  have divisible : 3 ∣ F / 2 - 13 * fillerJ F := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  have exactWeight : 26 * fillerJ F + 6 * fillerQ F = F := by
    have hd := Nat.mod_eq_zero_of_dvd divisible
    dsimp [fillerQ]
    omega
  have baseWeight (n : ℕ) : listWeight (List.replicate n (lowReturn 0)) = 26 * n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.replicate_succ, listWeight]
      rw [ih]
      change 6 * (1 + 0) + 20 * 1 + 26 * n = 26 * (n + 1)
      omega
  have weight : listWeight (lowFiller F) = F := by
    simp only [lowFiller, listWeight]
    rw [baseWeight]
    change 6 * (1 + fillerQ F) + 20 * 1 + 26 * (fillerJ F - 1) = F
    omega
  have low : ∀ a ∈ lowFiller F, a.r = 1 := by
    intro a ha
    simp only [lowFiller, List.mem_cons, List.mem_replicate] at ha
    rcases ha with rfl | ⟨_, rfl⟩ <;> rfl
  exact ⟨bounds.1, bounds.2, unique, residue, nonnegative, divisible, exactWeight,
    weight, low, fun K hK d strict j D => low_trace K hK d strict j _ low D⟩

def paddingCopies (L T : ℕ) : ℕ := (T - 78) / L
def paddingWeight (L T : ℕ) : ℕ := T - paddingCopies L T * L

/-- The quotient leaves a bounded positive outer filler at every even target. -/
theorem even_padding_arithmetic (L : ℕ) (positive : 0 < L) (evenL : Even L)
    (T : ℕ) (large : 78 ≤ T) (evenT : Even T) :
    Even (paddingWeight L T) ∧ 78 ≤ paddingWeight L T ∧
    paddingWeight L T < 78 + L ∧
    paddingCopies L T * L + paddingWeight L T = T := by
  have decomp := Nat.mod_add_div (T - 78) L
  rw [Nat.mul_comm L] at decomp
  have rem := Nat.mod_lt (T - 78) positive
  have bound : paddingCopies L T * L ≤ T := by dsimp [paddingCopies]; omega
  have exact : paddingCopies L T * L + paddingWeight L T = T := by
    dsimp [paddingWeight]; omega
  have range : 78 ≤ paddingWeight L T ∧ paddingWeight L T < 78 + L := by
    dsimp [paddingWeight, paddingCopies]; omega
  have ev : Even (paddingWeight L T) := by
    obtain ⟨l, hl⟩ := evenL.mul_left (paddingCopies L T)
    obtain ⟨t, ht⟩ := evenT
    refine ⟨t - l, ?_⟩
    dsimp [paddingWeight]
    omega
  exact ⟨ev, range.1, range.2, exact⟩

private theorem execution_word_append (xs ys : List Return) :
    executionWord (xs ++ ys) = executionWord xs ++ executionWord ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.cons_append, executionWord, ih, List.append_assoc]

private theorem reset_execution_word (R : Return) (words : List (List Return)) :
    executionWord (resetConcatenation R words) = resetFactor R words := by
  induction words with
  | nil => rfl
  | cons xs words ih =>
    simp only [resetConcatenation, execution_word_append, ih, resetFactor,
      List.map_cons, List.flatten_cons]

def paddedExecution (R : Return) (words : List (List Return)) (F : ℕ) : List Return :=
  resetConcatenation R words ++ lowFiller F

private theorem padded_parser (R : Return) (N F : ℕ) (p : List Return → Prop) :
    Function.Injective (fun words : List {xs : List Return // p xs ∧ listWeight xs = N} =>
      paddedExecution R (words.map Subtype.val) F) := by
  intro words words' he
  have unpadded := List.append_cancel_right he
  have encoded := congrArg executionWord unpadded
  simp only [reset_execution_word] at encoded
  exact (reset_factor_parser R N p).1 encoded

/-- A high return of the extended list already occurs at the identical prefix
of the original list. Thus its original complete suffix state is unchanged. -/
private theorem high_prefix_unchanged (K : ℕ) (hK : 2 ≤ K) (xs ys : List Return)
    (low : ∀ a ∈ ys, a.r = 1) (before : List Return) (a : Return) (after : List Return)
    (split : xs ++ ys = before ++ a :: after) (high : a.r = K) :
    ∃ rest, xs = before ++ a :: rest := by
  induction xs generalizing before with
  | nil =>
    have mem : a ∈ ys := by
      simp only [List.nil_append] at split
      rw [split]
      simp
    have := low a mem
    omega
  | cons x xs ih =>
    cases before with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at split
      exact ⟨xs, by simp [split.1]⟩
    | cons y before =>
      simp only [List.cons_append, List.cons.injEq] at split
      obtain ⟨rest, hr⟩ := ih before split.2
      exact ⟨rest, by simp only [List.cons_append, split.1, hr]⟩

private theorem append_low_supply (model : Model) (o : Ownership) (K : ℕ)
    (hK : 2 ≤ K) (budget : ℝ) (automatic : actualAutomaticCost K < budget)
    (xs ys : List Return) (cap : ∀ a ∈ xs, a.r ≤ K)
    (low : ∀ a ∈ ys, a.r = 1)
    (supply : ActualPairSupply model o budget .strict xs) :
    ActualPairSupply model o budget .strict (xs ++ ys) := by
  have control := ((actual_strict_cost_supply model o budget xs
    ((actual_automatic_cost_envelope K hK).2.1.trans_lt automatic)).mp supply).2.2
  apply actual_capped_strict_supply_of_high_costs model o K hK budget automatic (xs ++ ys)
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact cap a ha
    · have := low a ha; omega
  · intro before a after split high
    obtain ⟨rest, old⟩ := high_prefix_unchanged K hK xs ys low before a after split high
    simpa only [high] using
      (exact_control_iff_split .high budget xs _).mp control before a rest old

/-- The fixed outer filler and the original cumulative-weight parser recover
all choices from the full weak codebook, at every even target and both starts. -/
theorem same_reset_all_even_counts (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    ∃ R : Return, R.r = 1 ∧
    max (max (xSide .high) (ySide .high)) ((lam - b) / g ^ 2 / chi ^ K) <
      hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) ∧
    ∀ (sourceModel : Model) (N : ℕ), 0 < N →
      1 ≤ actualCount sourceModel K ((lam - b) / g ^ 2 / chi ^ K) false N →
    let d := (lam - b) / g ^ 2 / chi ^ K
    let delta := hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) -
      initial .high sourceModel
    let gamma := delta * g ^ N
    let eps := min (b - actualAutomaticCost K) (g ^ 2 * chi ^ K * gamma) / 2
    let V := {xs : List Return //
      GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs = N}
    let L := N + 20 + 6 * R.m
    Even N ∧ Even L ∧ 0 < L ∧ 0 < delta ∧ 0 < gamma ∧ 0 < eps ∧
    ∀ (targetModel : Model) (T : ℕ), 78 ≤ T → Even T →
    let k := paddingCopies L T
    let F := paddingWeight L T
    Even F ∧ 78 ≤ F ∧ F < 78 + L ∧ k * L + F = T ∧
    Function.Injective (fun z : Fin k → V =>
      paddedExecution R (List.ofFn (fun i => (z i).val)) F) ∧
    (∀ z : Fin k → V,
      let execution := paddedExecution R (List.ofFn (fun i => (z i).val)) F
      listWeight execution = T ∧
      GuardTrace K (d + gamma) false .high execution (initial .high targetModel) ∧
      ActualPairSupply targetModel o (b - eps) .strict execution ∧
      (∀ contract : Contract, ActualPairSupply targetModel o b contract execution) ∧
      (∀ (before : List Return) (a : Return) (after : List Return),
        execution = before ++ a :: after → a.r = K →
        ∃ rest, resetConcatenation R (List.ofFn (fun i => (z i).val)) =
          before ++ a :: rest) ∧
      (∀ side : Side, externalWord side execution =
        externalWord side (lowFiller F) ++
          externalWord side (resetConcatenation R (List.ofFn (fun i => (z i).val))))) ∧
    (∀ strict : Bool,
      actualCount sourceModel K d false N ^ k ≤ actualCount targetModel K d strict T) ∧
    (∀ contract : Contract,
      actualCount sourceModel K d false N ^ k ≤ contractCount targetModel o b contract T) ∧
    Function.Injective (fun z : Fin k → V =>
      history targetModel (paddedExecution R (List.ofFn (fun i => (z i).val)) F)) ∧
    (∀ side : Side, Function.Injective (fun z : Fin k → V =>
      source side targetModel (paddedExecution R (List.ofFn (fun i => (z i).val)) F))) := by
  classical
  obtain ⟨R, hr, hB, codebooks⟩ := reset_codebook_construction o b K hK hqb hbp
  refine ⟨R, hr, hB, ?_⟩
  intro sourceModel N hN ha
  dsimp only
  let d := (lam - b) / g ^ 2 / chi ^ K
  let delta := hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) -
    initial .high sourceModel
  let gamma := delta * g ^ N
  let eps := min (b - actualAutomaticCost K) (g ^ 2 * chi ^ K * gamma) / 2
  let V := {xs : List Return //
    GuardTrace K d false .high xs (initial .high sourceModel) ∧ listWeight xs = N}
  let L := N + 20 + 6 * R.m
  obtain ⟨dp, gp, ep, joint, _⟩ := codebooks sourceModel N hN
  have finite : Finite V := (actual_dictionary_bound sourceModel K d false N (by omega)).1
  letI : Finite V := finite
  change 1 ≤ actualCount sourceModel K d false N at ha
  obtain ⟨xs⟩ : Nonempty V := (Nat.card_pos_iff.mp (by
    change 0 < actualCount sourceModel K d false N
    exact lt_of_lt_of_le (by decide : 0 < 1) ha)).1
  have evenN : Even N := xs.property.2 ▸ actual_list_weight_even xs.val
  have evenL : Even L := by
    obtain ⟨n, hn⟩ := evenN
    refine ⟨n + 10 + 3 * R.m, ?_⟩
    dsimp [L]; omega
  have lp : 0 < L := by dsimp [L]; omega
  have ea : eps < b - actualAutomaticCost K := by
    have hm := min_le_left (b - actualAutomaticCost K) (g ^ 2 * chi ^ K * gamma)
    change 0 < eps at ep
    dsimp [eps] at *
    linarith
  refine ⟨evenN, evenL, lp, dp, gp, ep, ?_⟩
  intro targetModel T hT evenT
  let k := paddingCopies L T
  let F := paddingWeight L T
  obtain ⟨evenF, largeF, smallF, total⟩ := even_padding_arithmetic L lp evenL T hT evenT
  have filler := low_filler_geometry F evenF largeF
  let f : (Fin k → V) → List Return := fun z =>
    paddedExecution R (List.ofFn (fun i => (z i).val)) F
  have injection : Function.Injective f := by
    intro z z' he
    have mapped : paddedExecution R ((List.ofFn z).map Subtype.val) F =
        paddedExecution R ((List.ofFn z').map Subtype.val) F := by
      simpa only [List.map_ofFn, Function.comp_def, f] using he
    exact List.ofFn_injective (padded_parser R N F
      (fun xs => GuardTrace K d false .high xs (initial .high sourceModel)) mapped)
  have packet (z : Fin k → V) :
      listWeight (f z) = T ∧
      GuardTrace K (d + gamma) false .high (f z) (initial .high targetModel) ∧
      ActualPairSupply targetModel o (b - eps) .strict (f z) ∧
      (∀ contract : Contract, ActualPairSupply targetModel o b contract (f z)) ∧
      (∀ (before : List Return) (a : Return) (after : List Return),
        f z = before ++ a :: after → a.r = K →
        ∃ rest, resetConcatenation R (List.ofFn (fun i => (z i).val)) =
          before ++ a :: rest) ∧
      (∀ side : Side, externalWord side (f z) = externalWord side (lowFiller F) ++
        externalWord side (resetConcatenation R (List.ofFn (fun i => (z i).val)))) := by
    let execution := resetConcatenation R (List.ofFn (fun i => (z i).val))
    have old := joint targetModel (List.ofFn z)
    simp only [List.map_ofFn, Function.comp_def] at old
    have cap : ∀ a ∈ execution, a.r ≤ K := by
      intro a ha
      obtain ⟨before, after, split⟩ := List.mem_iff_append.mp ha
      exact ((uniform_guard_trace_iff_split K _ false .high execution _).mp old.1
        before a after split).1
    have weight : listWeight execution = k * L := by
      rw [← complete_execution_word_parser.2.2.2.1 execution, reset_execution_word]
      have hw := (reset_factor_parser R N
        (fun xs => GuardTrace K d false .high xs (initial .high sourceModel))).2
        (List.ofFn z)
      simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn, hr, Nat.mul_one,
        L, execution] using hw
    have tr : GuardTrace K (d + gamma) false .high (f z) (initial .high targetModel) := by
      apply (guard_append K _ false .high execution (lowFiller F) _).mpr
      exact ⟨old.1, filler.2.2.2.2.2.2.2.2.2 K hK _ false .high _⟩
    have supplied : ActualPairSupply targetModel o (b - eps) .strict (f z) :=
      append_low_supply targetModel o K hK (b - eps) (by linarith) execution
        (lowFiller F) cap filler.2.2.2.2.2.2.2.2.1 old.2
    have strict : ActualPairSupply targetModel o b .strict (f z) := by
      intro side
      obtain ⟨err, bound, observations, zero, future⟩ := supplied side
      refine ⟨err, ?_, observations, zero, future⟩
      intro p
      have hb := bound p
      change 0 < eps at ep
      linarith
    have contracts (contract : Contract) : ActualPairSupply targetModel o b contract (f z) := by
      cases contract with
      | strict => exact strict
      | recordMargin =>
        intro side
        obtain ⟨err, bound, observations, zero, future⟩ := supplied side
        exact ⟨err, ⟨eps, ep, fun p => (bound p).le⟩, observations, zero, future⟩
      | closed =>
        intro side
        obtain ⟨err, bound, observations, zero, future⟩ := strict side
        exact ⟨err, fun p => (bound p).le, observations, zero, future⟩
    refine ⟨?_, tr, supplied, contracts, ?_, ?_⟩
    · change listWeight (execution ++ lowFiller F) = T
      rw [list_weight_append, weight, filler.2.2.2.2.2.2.2.1]
      exact total
    · intro before a after split high
      exact high_prefix_unchanged K hK execution (lowFiller F)
        filler.2.2.2.2.2.2.2.2.1 before a after split high
    · intro side
      simp only [f, paddedExecution, externalWord, List.reverse_append, List.map_append,
        List.flatten_append]
  have guardCounts (strict : Bool) : actualCount sourceModel K d false N ^ k ≤
      actualCount targetModel K d strict T := by
    letI := (actual_dictionary_bound targetModel K d strict T (by omega)).1
    have guarded (z : Fin k → V) :
        GuardTrace K d strict .high (f z) (initial .high targetModel) := by
      cases strict with
      | true => exact ((actual_strict_record_supply targetModel o b (f z) K hK
          hqb hbp).1).mp ((packet z).2.2.2.1 .strict)
      | false =>
        apply (uniform_guard_trace_iff_split K d false .high (f z) _).mpr
        intro before a after split
        have old := (uniform_guard_trace_iff_split K (d + gamma) false .high (f z) _).mp
          (packet z).2.1 before a after split
        refine ⟨old.1, ?_⟩
        intro high
        have margin := old.2 high
        simp only [Bool.false_eq_true, if_false] at margin ⊢
        change 0 < gamma at gp
        linarith
    let encode : (Fin k → V) → ActualDictionary targetModel K d strict T := fun z =>
      ⟨f z, guarded z, (packet z).1⟩
    have inj : Function.Injective encode := by
      intro z z' he; exact injection (congrArg Subtype.val he)
    have bound := Nat.card_le_card_of_injective encode inj
    simpa only [Nat.card_fun, Nat.card_fin, V, actualCount, ActualDictionary] using bound
  have contractCounts (contract : Contract) : actualCount sourceModel K d false N ^ k ≤
      contractCount targetModel o b contract T := by
    letI := (contract_count_correspondence targetModel o b contract T K hK hqb hbp).1
    let encode : (Fin k → V) → ContractDictionary targetModel o b contract T := fun z =>
      ⟨f z, (packet z).2.2.2.1 contract, (packet z).1⟩
    have inj : Function.Injective encode := by
      intro z z' he; exact injection (congrArg Subtype.val he)
    have bound := Nat.card_le_card_of_injective encode inj
    simpa only [Nat.card_fun, Nat.card_fin, V, actualCount, contractCount,
      ActualDictionary] using bound
  have historyInj : Function.Injective (fun z : Fin k → V => history targetModel (f z)) := by
    intro z z' he
    exact injection (complete_execution_word_parser.2.2.2.2 targetModel he)
  have sourceInj (side : Side) :
      Function.Injective (fun z : Fin k → V => source side targetModel (f z)) := by
    intro z z' he
    exact injection (Completion.actual_source_address_injection side targetModel (f z) (f z')
      ((packet z).1.trans (packet z').1.symm) he)
  exact ⟨evenF, largeF, smallF, total, injection, packet, guardCounts, contractCounts,
    historyInj, sourceInj⟩

/-- Odd literal weights have no actual complete lists under either guard flag
or any of the original source contracts. -/
theorem odd_actual_counts (T : ℕ) (odd : Odd T) :
    (∀ (model : Model) (K : ℕ) (d : ℝ) (strict : Bool),
      actualCount model K d strict T = 0) ∧
    (∀ (model : Model) (o : Ownership) (b : ℝ) (contract : Contract),
      contractCount model o b contract T = 0) := by
  have impossible (xs : List Return) (weight : listWeight xs = T) : False := by
    obtain ⟨v, hv⟩ := actual_list_weight_even xs
    obtain ⟨u, hu⟩ := odd
    omega
  constructor
  · intro model K d strict
    letI : IsEmpty (ActualDictionary model K d strict T) :=
      ⟨fun xs => impossible xs.val xs.property.2⟩
    exact Nat.card_of_isEmpty
  · intro model o b contract
    letI : IsEmpty (ContractDictionary model o b contract T) :=
      ⟨fun xs => impossible xs.val xs.property.2⟩
    exact Nat.card_of_isEmpty

/-- The standalone same low filler supplies both original starts and all
contracts. Raw counts are positive, so max-one normalization is then redundant. -/
theorem even_actual_positivity (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (T : ℕ) (even : Even T) (large : 78 ≤ T) :
    listWeight (lowFiller T) = T ∧
    (∀ (model : Model) (contract : Contract),
      ActualPairSupply model o b contract (lowFiller T) ∧
      0 < contractCount model o b contract T) ∧
    (∀ (model : Model) (strict : Bool),
      0 < actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict T ∧
      actualLogRate model K ((lam - b) / g ^ 2 / chi ^ K) strict T =
        Real.logb 2 (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict T : ℝ) / (T : ℝ)) := by
  have filler := low_filler_geometry T even large
  have weight := filler.2.2.2.2.2.2.2.1
  have trace := filler.2.2.2.2.2.2.2.2.2 K hK
  refine ⟨weight, ?_, ?_⟩
  · intro model contract
    let e := contractDictionaryEquiv model o b contract T K hK hqb hbp
    let xs : ActualDictionary model K ((lam - b) / g ^ 2 / chi ^ K) (contractStrict o contract) T :=
      ⟨lowFiller T, trace _ _ .high _, weight⟩
    have supply : ActualPairSupply model o b contract (lowFiller T) := (e.symm xs).property.1
    letI := (contract_count_correspondence model o b contract T K hK hqb hbp).1
    letI : Nonempty (ContractDictionary model o b contract T) := ⟨⟨_, supply, weight⟩⟩
    exact ⟨supply, Nat.card_pos⟩
  · intro model strict
    letI := (actual_dictionary_bound model K ((lam - b) / g ^ 2 / chi ^ K) strict T (by omega)).1
    letI : Nonempty (ActualDictionary model K ((lam - b) / g ^ 2 / chi ^ K) strict T) :=
      ⟨⟨lowFiller T, trace _ strict .high _, weight⟩⟩
    have positive : 0 < actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict T := Nat.card_pos
    refine ⟨positive, ?_⟩
    simp only [actualLogRate, max_eq_right (show 1 ≤ actualCount model K
      ((lam - b) / g ^ 2 / chi ^ K) strict T by omega)]

/-- The prescribed floor ratio converges on the entire even-weight filter. -/
theorem full_even_floor_ratio (L : ℕ) (positive : 0 < L) (evenL : Even L) :
    Tendsto (fun v : ℕ => (paddingCopies L (2 * v) : ℝ) / ((2 * v : ℕ) : ℝ))
      atTop (𝓝 (1 / (L : ℝ))) := by
  have den : Tendsto (fun v : ℕ => ((2 * v : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : 0 < (2 : ℝ))
  have bounded : ∀ᶠ v : ℕ in atTop, (paddingWeight L (2 * v) : ℝ) ≤ (78 + L : ℕ) := by
    filter_upwards [eventually_ge_atTop (39 : ℕ)] with v hv
    have h := (even_padding_arithmetic L positive evenL (2 * v) (by omega)
      ⟨v, by omega⟩).2.2.1.le
    exact_mod_cast h
  have negligible : Tendsto (fun v : ℕ =>
      (paddingWeight L (2 * v) : ℝ) / ((2 * v : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (Eventually.of_forall (fun v => by positivity))
      bounded den
  have limit : Tendsto (fun v : ℕ =>
      (1 - (paddingWeight L (2 * v) : ℝ) / ((2 * v : ℕ) : ℝ)) / (L : ℝ))
      atTop (𝓝 (1 / (L : ℝ))) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub negligible).div_const (L : ℝ)
  apply limit.congr'
  filter_upwards [eventually_ge_atTop (39 : ℕ)] with v hv
  have total := (even_padding_arithmetic L positive evenL (2 * v) (by omega)
    ⟨v, by omega⟩).2.2.2
  have totalR := congrArg (fun n : ℕ => (n : ℝ)) total
  push_cast at totalR
  have lp : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
  have tp : ((2 * v : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : 2 * v ≠ 0)
  push_cast
  field_simp
  nlinarith

private theorem even_atTop : Tendsto (fun v : ℕ => 2 * v) atTop atTop := by
  apply tendsto_atTop.mpr
  intro t
  filter_upwards [eventually_ge_atTop t] with v hv
  omega

private theorem fixed_codebook_liminf (model : Model) (K : ℕ) (d : ℝ) (strict : Bool)
    (hK : 1 ≤ K)
    (a L : ℕ) (nonempty : 1 ≤ a) (positive : 0 < L) (evenL : Even L)
    (counts : ∀ T : ℕ, 78 ≤ T → Even T →
      a ^ paddingCopies L T ≤ actualCount model K d strict T) :
    Real.logb 2 (a : ℝ) / (L : ℝ) ≤
      liminf (fun v : ℕ => actualLogRate model K d strict (2 * v)) atTop := by
  let lower (v : ℕ) := Real.logb 2 (a : ℝ) *
    ((paddingCopies L (2 * v) : ℝ) / ((2 * v : ℕ) : ℝ))
  have converges : Tendsto lower atTop (𝓝 (Real.logb 2 (a : ℝ) / (L : ℝ))) := by
    simpa only [mul_one_div] using
      (full_even_floor_ratio L positive evenL).const_mul (Real.logb 2 (a : ℝ))
  have comparison : ∀ᶠ v : ℕ in atTop, lower v ≤ actualLogRate model K d strict (2 * v) := by
    filter_upwards [eventually_ge_atTop (39 : ℕ)] with v hv
    have bound := (counts (2 * v) (by omega) ⟨v, by omega⟩).trans
      (Nat.le_max_right 1 (actualCount model K d strict (2 * v)))
    have ap : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    have log := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (pow_pos ap (paddingCopies L (2 * v)))
      (by exact_mod_cast bound : (a : ℝ) ^ paddingCopies L (2 * v) ≤
        ((max 1 (actualCount model K d strict (2 * v)) : ℕ) : ℝ))
    rw [Real.logb_pow] at log
    dsimp [lower, actualLogRate]
    calc
      _ = ((paddingCopies L (2 * v) : ℝ) * Real.logb 2 (a : ℝ)) /
          ((2 * v : ℕ) : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right log (by positivity)
  obtain ⟨B, upper⟩ := (actual_log_rate_bounds model K d strict hK).2
  have bounded : IsBoundedUnder (· ≤ ·) atTop
      (fun v : ℕ => actualLogRate model K d strict (2 * v)) :=
    isBoundedUnder_of_eventually_le (even_atTop.eventually upper)
  have bound := liminf_le_liminf comparison converges.isBoundedUnder_ge
    bounded.isCoboundedUnder_ge
  rwa [converges.liminf_eq] at bound

/-- One reset fixed before all source weights gives the full-even lower slope
for every nonempty full weak codebook and both actual target starts. -/
theorem original_finite_even_bridge (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    (∀ (T : ℕ), Odd T →
      (∀ (model : Model) (strict : Bool),
        actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict T = 0) ∧
      (∀ (model : Model) (contract : Contract), contractCount model o b contract T = 0)) ∧
    (∀ (T : ℕ), Even T → 78 ≤ T →
      listWeight (lowFiller T) = T ∧
      (∀ (model : Model) (contract : Contract),
        ActualPairSupply model o b contract (lowFiller T) ∧
        0 < contractCount model o b contract T) ∧
      (∀ (model : Model) (strict : Bool),
        0 < actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict T ∧
        actualLogRate model K ((lam - b) / g ^ 2 / chi ^ K) strict T =
          Real.logb 2 (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict T : ℝ) / (T : ℝ))) ∧
    ∃ R : Return, R.r = 1 ∧
    max (max (xSide .high) (ySide .high)) ((lam - b) / g ^ 2 / chi ^ K) <
      hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) ∧
    ∀ (sourceModel : Model) (N : ℕ), 0 < N →
      1 ≤ actualCount sourceModel K ((lam - b) / g ^ 2 / chi ^ K) false N →
    let d := (lam - b) / g ^ 2 / chi ^ K
    let a := actualCount sourceModel K d false N
    let L := N + 20 + 6 * R.m
    Even N ∧ Even L ∧ 0 < L ∧
    (∀ (targetModel : Model) (T : ℕ), 78 ≤ T → Even T →
      (∀ strict : Bool, a ^ paddingCopies L T ≤ actualCount targetModel K d strict T) ∧
      ∀ contract : Contract, a ^ paddingCopies L T ≤ contractCount targetModel o b contract T) ∧
    (∀ (targetModel : Model) (strict : Bool), Real.logb 2 (a : ℝ) / (L : ℝ) ≤
      liminf (fun v : ℕ => actualLogRate targetModel K d strict (2 * v)) atTop) := by
  refine ⟨?_, fun T even large => even_actual_positivity o b K hK hqb hbp T even large, ?_⟩
  · intro T odd
    exact ⟨fun model strict => (odd_actual_counts T odd).1 model K _ strict,
      fun model contract => (odd_actual_counts T odd).2 model o b contract⟩
  obtain ⟨R, hr, hB, complete⟩ := same_reset_all_even_counts o b K hK hqb hbp
  refine ⟨R, hr, hB, ?_⟩
  intro sourceModel N hN ha
  dsimp only
  obtain ⟨evenN, evenL, lp, _, _, _, counts⟩ := complete sourceModel N hN ha
  have powers (targetModel : Model) (T : ℕ) (large : 78 ≤ T) (even : Even T) :=
    And.intro (counts targetModel T large even).2.2.2.2.2.2.1
      (counts targetModel T large even).2.2.2.2.2.2.2.1
  refine ⟨evenN, evenL, lp, powers, ?_⟩
  intro targetModel strict
  exact fixed_codebook_liminf targetModel K _ strict (by omega) _ _ ha lp evenL
    (fun T large even => (powers targetModel T large even).1 strict)

private theorem fixed_overhead_ratio (N : ℕ → ℕ) (unbounded : Tendsto N atTop atTop)
    (C : ℕ) :
    Tendsto (fun j => (N j : ℝ) / ((N j + C : ℕ) : ℝ)) atTop (𝓝 1) := by
  have den : Tendsto (fun j => N j + C) atTop atTop :=
    (tendsto_add_atTop_nat C).comp unbounded
  have small := (tendsto_const_div_atTop_nhds_zero_nat (C : ℝ)).comp den
  have limit := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub small
  simp only [sub_zero] at limit
  apply limit.congr'
  filter_upwards [unbounded.eventually (eventually_ge_atTop (1 : ℕ))] with j hj
  have nz : ((N j + C : ℕ) : ℝ) ≠ 0 := by positivity
  dsimp only [Function.comp_def]
  push_cast
  field_simp
  ring

private theorem full_even_normalized_limits (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    ∀ (model : Model) (strict : Bool),
      Tendsto (fun v : ℕ => actualLogRate model K ((lam - b) / g ^ 2 / chi ^ K) strict (2 * v))
        atTop (𝓝 (eta_b K b)) := by
  let d := (lam - b) / g ^ 2 / chi ^ K
  obtain ⟨R, hr, floor, complete⟩ :=
    (original_finite_even_bridge o b K hK hqb hbp).2.2
  obtain ⟨RE, _, _, approximations⟩ :=
    LowerRateLimit.original_count_codebook_approximation o b K hK hqb hbp
  obtain ⟨N, unbounded, nonempty, rawRate, _, _, _⟩ := approximations .original
  have ratio := fixed_overhead_ratio N unbounded (20 + 6 * R.m)
  have slope : Tendsto (fun j => Real.logb 2 (actualCount .original K d false (N j) : ℝ) /
      ((N j + 20 + 6 * R.m : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) := by
    have product := rawRate.mul ratio
    simp only [mul_one] at product
    apply product.congr'
    exact Eventually.of_forall (fun j => by
      have nz : (N j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (nonempty j).1)
      dsimp only [Pi.mul_apply, d]
      simp only [Nat.add_assoc, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      field_simp)
  intro model strict
  let u := fun v : ℕ => actualLogRate model K d strict (2 * v)
  have bounds := actual_log_rate_bounds model K d strict (by omega)
  have upper : IsBoundedUnder (· ≤ ·) atTop u :=
    isBoundedUnder_of_eventually_le (even_atTop.eventually bounds.2.choose_spec)
  have lower : IsBoundedUnder (· ≥ ·) atTop u :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun v => bounds.1 (2 * v)))
  have codebook (j : ℕ) :
      Real.logb 2 (actualCount .original K d false (N j) : ℝ) /
        ((N j + 20 + 6 * R.m : ℕ) : ℝ) ≤ liminf u atTop := by
    exact (complete .original (N j) (nonempty j).1 (nonempty j).2).2.2.2.2 model strict
  have infBound : eta_b K b ≤ liminf u atTop := le_of_tendsto' slope codebook
  have mappedLower : IsBoundedUnder (· ≥ ·) (map (fun v : ℕ => 2 * v) atTop)
      (actualLogRate model K d strict) :=
    isBoundedUnder_of_eventually_ge (even_atTop.eventually
      (Eventually.of_forall bounds.1))
  have allUpper : IsBoundedUnder (· ≤ ·) atTop (actualLogRate model K d strict) :=
    isBoundedUnder_of_eventually_le bounds.2.choose_spec
  have supBound : limsup u atTop ≤ eta_b K b := by
    have h := even_atTop.limsup_comp_le_limsup mappedLower.isCoboundedUnder_le allUpper
    exact h.trans_eq ((original_actual_count_rate_bridge o b K hK hqb hbp).2.1 model strict)
  exact tendsto_of_le_liminf_of_limsup_le infBound supBound upper lower

/-- Raw logarithms converge on every even weight, for both actual starts and
both guard flags. The error from the linear term is little-o of the literal weight. -/
theorem actual_even_raw_asymptotics (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    ∀ (model : Model) (strict : Bool),
      Tendsto (fun v : ℕ => Real.logb 2
        (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict (2 * v) : ℝ) /
        ((2 * v : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) ∧
      Asymptotics.IsLittleO atTop
        (fun v : ℕ => Real.logb 2
          (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict (2 * v) : ℝ) -
          eta_b K b * ((2 * v : ℕ) : ℝ))
        (fun v : ℕ => ((2 * v : ℕ) : ℝ)) := by
  have normalized := full_even_normalized_limits o b K hK hqb hbp
  intro model strict
  have raw : Tendsto (fun v : ℕ => Real.logb 2
      (actualCount model K ((lam - b) / g ^ 2 / chi ^ K) strict (2 * v) : ℝ) /
      ((2 * v : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) := by
    apply (normalized model strict).congr'
    filter_upwards [eventually_ge_atTop (39 : ℕ)] with v hv
    exact ((even_actual_positivity o b K hK hqb hbp (2 * v) ⟨v, by omega⟩
      (by omega)).2.2 model strict).2
  refine ⟨raw, ?_⟩
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with v hv
    intro hzero
    have nz : ((2 * v : ℕ) : ℝ) ≠ 0 := by positivity
    exact (nz hzero).elim
  · have zero := raw.sub (tendsto_const_nhds (x := eta_b K b))
    simp only [sub_self] at zero
    apply zero.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with v hv
    have nz : ((2 * v : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp

/-- Original source-contract lists indexed by the length of their actual color history. -/
def ObservedContractDictionary (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (Nobs : ℕ) :=
  {xs : List Return // ActualPairSupply model o b contract xs ∧
    (history model xs).length = Nobs}

/-- The actual color histories supplied by the prescribed same-list source pairs. -/
def ActualHistoryImage (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (Nobs : ℕ) : Set (List Color) :=
  Set.range (fun xs : ObservedContractDictionary model o b contract Nobs => history model xs.val)

/-- One literal source side, with its original tail, at a specified departure length. -/
def ActualSourceImage (side : Side) (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (Nobs : ℕ) : Set (ℕ → Label) :=
  Set.range (fun xs : ObservedContractDictionary model o b contract Nobs => source side model xs.val)

/-- Both original literal sources from the very same actual return list. -/
def ActualSourcePairImage (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (Nobs : ℕ) : Set ((ℕ → Label) × (ℕ → Label)) :=
  Set.range (fun xs : ObservedContractDictionary model o b contract Nobs =>
    (source .high model xs.val, source .low model xs.val))

noncomputable def historyImageCount (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (Nobs : ℕ) : ℕ := Nat.card (ActualHistoryImage model o b contract Nobs)

noncomputable def sourceImageCount (side : Side) (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (Nobs : ℕ) : ℕ := Nat.card (ActualSourceImage side model o b contract Nobs)

noncomputable def sourcePairImageCount (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (Nobs : ℕ) : ℕ := Nat.card (ActualSourcePairImage model o b contract Nobs)

private def observed_contract_equiv (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (T : ℕ) :
    ObservedContractDictionary model o b contract (observationOffset model + T) ≃
      ContractDictionary model o b contract T where
  toFun xs := ⟨xs.val, xs.property.1, by
    have len := (paired_source_reconstruction .high model xs.val).2.2.2.2.2.1
    have actual := xs.property.2
    rw [len] at actual
    omega⟩
  invFun xs := ⟨xs.val, xs.property.1, by
    rw [(paired_source_reconstruction .high model xs.val).2.2.2.2.2.1, xs.property.2]⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The original parser identifies actual observation-length images with the
contract list dictionary. Every image keeps the original source, legal address,
exact observed prefix and literal zero-error future. -/
theorem actual_observation_count_correspondence (model : Model) (o : Ownership)
    (b : ℝ) (contract : Contract) (T K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    Finite (ObservedContractDictionary model o b contract (observationOffset model + T)) ∧
    historyImageCount model o b contract (observationOffset model + T) =
      contractCount model o b contract T ∧
    (∀ side : Side, sourceImageCount side model o b contract (observationOffset model + T) =
      contractCount model o b contract T) ∧
    sourcePairImageCount model o b contract (observationOffset model + T) =
      contractCount model o b contract T ∧
    contractCount model o b contract T =
      actualCount model K ((lam - b) / g ^ 2 / chi ^ K) (contractStrict o contract) T ∧
    (∀ xs : ObservedContractDictionary model o b contract (observationOffset model + T),
      listWeight xs.val = T ∧
      ∀ side : Side,
        (observedPrefix side model xs.val).length = observationOffset model + T ∧
        OperationRecord o b contract (source side model xs.val)
          (OperationPairedRecord model o xs.val side) ∧
        OperationFiniteSource (source side model xs.val) ∧
        (∀ p, source side model xs.val (observationOffset model + T + p) =
          address (tailPrefix side) p) ∧
        (∃ err : ℕ → ℝ, ErrorBound b contract err ∧
          (∀ p (hp : p < observationOffset model + T),
            observe o (coordinate (sourcePrefix side model xs.val) p) (err p) =
              (history model xs.val)[p]'(by rw [xs.property.2]; exact hp)) ∧
          (∀ p, observationOffset model + T ≤ p → err p = 0) ∧
          (∀ p, observe o (coordinate (sourcePrefix side model xs.val)
              (observationOffset model + T + p)) (err (observationOffset model + T + p)) =
            observe o (coordinate (tailPrefix side) p) 0))) := by
  classical
  let O := ObservedContractDictionary model o b contract (observationOffset model + T)
  let e := observed_contract_equiv model o b contract T
  letI := (contract_count_correspondence model o b contract T K hK hqb hbp).1
  letI : Finite O := Finite.of_equiv _ e.symm
  have hi : Function.Injective (fun xs : O => history model xs.val) := by
    intro xs ys he
    exact Subtype.ext (complete_execution_word_parser.2.2.2.2 model he)
  have si (side : Side) : Function.Injective (fun xs : O => source side model xs.val) := by
    intro xs ys he
    apply Subtype.ext
    apply Completion.actual_source_address_injection side model xs.val ys.val _ he
    exact (e xs).property.2.trans (e ys).property.2.symm
  have pi : Function.Injective (fun xs : O =>
      (source .high model xs.val, source .low model xs.val)) := by
    intro xs ys he
    exact si .high (congrArg Prod.fst he)
  refine ⟨inferInstance, ?_, ?_, ?_,
    (contract_count_correspondence model o b contract T K hK hqb hbp).2, ?_⟩
  · exact Nat.card_congr ((Equiv.ofInjective _ hi).symm.trans e)
  · intro side
    exact Nat.card_congr ((Equiv.ofInjective _ (si side)).symm.trans e)
  · exact Nat.card_congr ((Equiv.ofInjective _ pi).symm.trans e)
  · intro xs
    have weight : listWeight xs.val = T := (e xs).property.2
    refine ⟨weight, ?_⟩
    intro side
    have reconstruction := paired_source_reconstruction side model xs.val
    have len : (observedPrefix side model xs.val).length = observationOffset model + T := by
      rw [reconstruction.2.2.2.2.1, weight]
    have actual := operation_pair_membership model o b contract xs.val xs.property.1 side
    refine ⟨len, actual.1, actual.2, ?_, ?_⟩
    · simpa only [len] using reconstruction.2.1
    · obtain ⟨err, bound, observations, zero, future⟩ := xs.property.1 side
      refine ⟨err, bound, ?_, ?_, ?_⟩
      · intro p hp
        exact observations p (by rw [xs.property.2]; exact hp)
      · simpa only [xs.property.2] using zero
      · simpa only [len] using future

/-- Each original source contract has the same raw all-even asymptotics.
The closed endpoint flag is retained by the exact contract dictionary equivalence. -/
theorem contract_even_raw_asymptotics (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    ∀ (model : Model) (contract : Contract),
      Tendsto (fun v : ℕ => Real.logb 2 (contractCount model o b contract (2 * v) : ℝ) /
        ((2 * v : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) ∧
      Asymptotics.IsLittleO atTop
        (fun v : ℕ => Real.logb 2 (contractCount model o b contract (2 * v) : ℝ) -
          eta_b K b * ((2 * v : ℕ) : ℝ))
        (fun v : ℕ => ((2 * v : ℕ) : ℝ)) := by
  intro model contract
  have counts (T : ℕ) := (contract_count_correspondence model o b contract T K hK hqb hbp).2
  simpa only [counts] using
    actual_even_raw_asymptotics o b K hK hqb hbp model (contractStrict o contract)

/-- The actual offsets are even. The shifted even indices are cofinal, and
subtracting the half-offset recovers every sufficiently large even observation length. -/
theorem observation_even_reindexing (model : Model) :
    Even (observationOffset model) ∧
    Tendsto (fun v : ℕ => observationOffset model + 2 * v) atTop atTop ∧
    Tendsto (fun v : ℕ => v - observationOffset model / 2) atTop atTop ∧
    (∀ᶠ v : ℕ in atTop,
      observationOffset model + 2 * (v - observationOffset model / 2) = 2 * v) := by
  refine ⟨?_, ?_, tendsto_sub_atTop_nat _, ?_⟩
  · cases model
    · exact ⟨13, rfl⟩
    · exact ⟨26, rfl⟩
  · apply tendsto_atTop.mpr
    intro t
    filter_upwards [eventually_ge_atTop t] with v hv
    omega
  · filter_upwards [eventually_ge_atTop (observationOffset model)] with v hv
    cases model <;> simp only [observationOffset] at * <;> omega

/-- Counts of actual histories, each literal source and the same-list source
pair have the original leading coefficient at every even observation length.
The identities and positivity use the actual departure offsets, not an assigned length. -/
theorem actual_observation_length_asymptotics (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    ∀ (model : Model) (contract : Contract),
      (∀ Nobs : ℕ, Odd Nobs →
        historyImageCount model o b contract Nobs = 0 ∧
        (∀ side : Side, sourceImageCount side model o b contract Nobs = 0) ∧
        sourcePairImageCount model o b contract Nobs = 0) ∧
      (∀ T : ℕ,
        historyImageCount model o b contract (observationOffset model + T) =
          contractCount model o b contract T ∧
        (∀ side : Side, sourceImageCount side model o b contract (observationOffset model + T) =
          contractCount model o b contract T) ∧
        sourcePairImageCount model o b contract (observationOffset model + T) =
          contractCount model o b contract T) ∧
      (∀ T : ℕ, Even T → 78 ≤ T →
        0 < historyImageCount model o b contract (observationOffset model + T) ∧
        (∀ side : Side, 0 < sourceImageCount side model o b contract (observationOffset model + T)) ∧
        0 < sourcePairImageCount model o b contract (observationOffset model + T)) ∧
      Tendsto (fun v : ℕ => Real.logb 2 (historyImageCount model o b contract (2 * v) : ℝ) /
        ((2 * v : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) ∧
      Asymptotics.IsLittleO atTop
        (fun v : ℕ => Real.logb 2 (historyImageCount model o b contract (2 * v) : ℝ) -
          eta_b K b * ((2 * v : ℕ) : ℝ))
        (fun v : ℕ => ((2 * v : ℕ) : ℝ)) ∧
      (∀ side : Side,
        Tendsto (fun v : ℕ => Real.logb 2 (sourceImageCount side model o b contract (2 * v) : ℝ) /
          ((2 * v : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) ∧
        Asymptotics.IsLittleO atTop
          (fun v : ℕ => Real.logb 2 (sourceImageCount side model o b contract (2 * v) : ℝ) -
            eta_b K b * ((2 * v : ℕ) : ℝ))
          (fun v : ℕ => ((2 * v : ℕ) : ℝ))) ∧
      Tendsto (fun v : ℕ => Real.logb 2 (sourcePairImageCount model o b contract (2 * v) : ℝ) /
        ((2 * v : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) ∧
      Asymptotics.IsLittleO atTop
        (fun v : ℕ => Real.logb 2 (sourcePairImageCount model o b contract (2 * v) : ℝ) -
          eta_b K b * ((2 * v : ℕ) : ℝ))
        (fun v : ℕ => ((2 * v : ℕ) : ℝ)) := by
  intro model contract
  have correspondence (T : ℕ) :=
    actual_observation_count_correspondence model o b contract T K hK hqb hbp
  have counts (T : ℕ) :
      historyImageCount model o b contract (observationOffset model + T) =
        contractCount model o b contract T ∧
      (∀ side : Side, sourceImageCount side model o b contract (observationOffset model + T) =
        contractCount model o b contract T) ∧
      sourcePairImageCount model o b contract (observationOffset model + T) =
        contractCount model o b contract T :=
    ⟨(correspondence T).2.1, (correspondence T).2.2.1, (correspondence T).2.2.2.1⟩
  have raw := (contract_even_raw_asymptotics o b K hK hqb hbp model contract).1
  have ratio := fixed_overhead_ratio (fun v : ℕ => 2 * v) even_atTop (observationOffset model)
  have shifted : Tendsto (fun v : ℕ => Real.logb 2 (contractCount model o b contract (2 * v) : ℝ) /
      ((observationOffset model + 2 * v : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) := by
    have product := raw.mul ratio
    simp only [mul_one] at product
    apply product.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with v hv
    have nz : ((2 * v : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_add]
    field_simp
    ring
  have reindex := observation_even_reindexing model
  have observed (a : ℕ → ℕ)
      (equalCounts : ∀ T, a (observationOffset model + T) = contractCount model o b contract T) :
      Tendsto (fun v : ℕ => Real.logb 2 (a (2 * v) : ℝ) / ((2 * v : ℕ) : ℝ))
        atTop (𝓝 (eta_b K b)) ∧
      Asymptotics.IsLittleO atTop
        (fun v : ℕ => Real.logb 2 (a (2 * v) : ℝ) - eta_b K b * ((2 * v : ℕ) : ℝ))
        (fun v : ℕ => ((2 * v : ℕ) : ℝ)) := by
    have offset : Tendsto (fun v : ℕ => Real.logb 2
        (a (observationOffset model + 2 * v) : ℝ) /
        ((observationOffset model + 2 * v : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) := by
      simpa only [equalCounts] using shifted
    have rate : Tendsto (fun v : ℕ => Real.logb 2 (a (2 * v) : ℝ) /
        ((2 * v : ℕ) : ℝ)) atTop (𝓝 (eta_b K b)) := by
      apply (offset.comp reindex.2.2.1).congr'
      filter_upwards [reindex.2.2.2] with v hv
      simp only [Function.comp_def, hv]
    refine ⟨rate, ?_⟩
    apply Asymptotics.isLittleO_of_tendsto'
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with v hv
      intro zero
      have nz : ((2 * v : ℕ) : ℝ) ≠ 0 := by positivity
      exact (nz zero).elim
    · have zero := rate.sub (tendsto_const_nhds (x := eta_b K b))
      simp only [sub_self] at zero
      apply zero.congr'
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with v hv
      have nz : ((2 * v : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
  have histories := observed (historyImageCount model o b contract) (fun T => (counts T).1)
  have sources (side : Side) := observed (sourceImageCount side model o b contract)
    (fun T => (counts T).2.1 side)
  have pairs := observed (sourcePairImageCount model o b contract) (fun T => (counts T).2.2)
  have oddImages (Nobs : ℕ) (odd : Odd Nobs) :
      historyImageCount model o b contract Nobs = 0 ∧
      (∀ side : Side, sourceImageCount side model o b contract Nobs = 0) ∧
      sourcePairImageCount model o b contract Nobs = 0 := by
    let O := ObservedContractDictionary model o b contract Nobs
    letI : IsEmpty O := ⟨fun xs => by
      have len := (paired_source_reconstruction .high model xs.val).2.2.2.2.2.1
      have ev := reindex.1.add (actual_list_weight_even xs.val)
      have actual := xs.property.2
      rw [len] at actual
      rw [actual] at ev
      exact (Nat.not_even_iff_odd.mpr odd) ev⟩
    have emptyRange {α : Type} (f : O → α) : IsEmpty (Set.range f) :=
      ⟨fun y => by obtain ⟨xs, _⟩ := y.property; exact isEmptyElim xs⟩
    refine ⟨?_, ?_, ?_⟩
    · letI : IsEmpty (ActualHistoryImage model o b contract Nobs) :=
        emptyRange (fun xs : O => history model xs.val)
      exact Nat.card_of_isEmpty
    · intro side
      letI : IsEmpty (ActualSourceImage side model o b contract Nobs) :=
        emptyRange (fun xs : O => source side model xs.val)
      exact Nat.card_of_isEmpty
    · letI : IsEmpty (ActualSourcePairImage model o b contract Nobs) :=
        emptyRange (fun xs : O => (source .high model xs.val, source .low model xs.val))
      exact Nat.card_of_isEmpty
  refine ⟨oddImages, counts, ?_, histories.1, histories.2, sources, pairs.1, pairs.2⟩
  intro T even large
  have positive := ((even_actual_positivity o b K hK hqb hbp T even large).2.1 model contract).2
  exact ⟨by rw [(counts T).1]; exact positive,
    fun side => by rw [(counts T).2.1 side]; exact positive,
    by rw [(counts T).2.2]; exact positive⟩

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
