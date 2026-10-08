/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual complete-list counts and auxiliary factors have one weighted growth rate. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open Filter
open scoped Topology

/-- The original complete execution lists, with their actual high initial state. -/
def ActualDictionary (model : Model) (K : ℕ) (d : ℝ) (strict : Bool) (N : ℕ) :=
  {xs : List Return // GuardTrace K d strict .high xs (initial .high model) ∧
    listWeight xs = N}

noncomputable def actualCount (model : Model) (K : ℕ) (d : ℝ)
    (strict : Bool) (N : ℕ) : ℕ := Nat.card (ActualDictionary model K d strict N)

noncomputable def actualLogRate (model : Model) (K : ℕ) (d : ℝ)
    (strict : Bool) (N : ℕ) : ℝ :=
  Real.logb 2 ((max 1 (actualCount model K d strict N) : ℕ) : ℝ) / (N : ℝ)

noncomputable def actualRate (model : Model) (K : ℕ) (d : ℝ) (strict : Bool) : ℝ :=
  limsup (actualLogRate model K d strict) atTop

private theorem strict_guard_weak (K : ℕ) (d : ℝ) (xs : List Return) (D : ℝ)
    (h : GuardTrace K d true .high xs D) : GuardTrace K d false .high xs D := by
  induction xs generalizing D with
  | nil => trivial
  | cons a xs ih => exact ⟨h.1, fun he => (h.2.1 he).le, ih _ h.2.2⟩

/-- The original parser and auxiliary padding give an injection without a
realization or factor-embedding premise. -/
def actualToFactor (model : Model) (K : ℕ) (d : ℝ) (strict : Bool) (N : ℕ)
    (hK : 1 ≤ K) : ActualDictionary model K d strict N →
      FactorDictionary (AuxiliaryLanguage K d) N := fun xs => by
  have weak : GuardTrace K d false .high xs.val (initial .high model) := by
    cases strict with
    | false => exact xs.property.1
    | true => exact strict_guard_weak K d xs.val _ xs.property.1
  have pad := auxiliary_lower_padding K d model xs.val hK weak
  exact ⟨executionWord xs.val, pad.2.2.2.2.1,
    pad.2.2.2.2.2.trans xs.property.2⟩

theorem actual_to_factor_injective (model : Model) (K : ℕ) (d : ℝ)
    (strict : Bool) (N : ℕ) (hK : 1 ≤ K) :
    Function.Injective (actualToFactor model K d strict N hK) := by
  intro xs ys h
  apply Subtype.ext
  exact complete_execution_word_parser.2.2.1 (congrArg Subtype.val h)

/-- Both strict and weak actual dictionaries are finite and have the same
uniform exponential bound, at every weight including zero. -/
theorem actual_dictionary_bound (model : Model) (K : ℕ) (d : ℝ)
    (strict : Bool) (N : ℕ) (hK : 1 ≤ K) :
    Finite (ActualDictionary model K d strict N) ∧
    actualCount model K d strict N ≤ factorCount (AuxiliaryLanguage K d) N ∧
    actualCount model K d strict N ≤ 3 ^ (N + 1) := by
  letI := (factor_dictionary_bound (AuxiliaryLanguage K d) N).1
  have inj := actual_to_factor_injective model K d strict N hK
  letI := Finite.of_injective (actualToFactor model K d strict N hK) inj
  have bound := Nat.card_le_card_of_injective (actualToFactor model K d strict N hK) inj
  exact ⟨inferInstance, bound, bound.trans (factor_dictionary_bound _ N).2⟩

private theorem strict_count_le_weak (model : Model) (K : ℕ) (d : ℝ)
    (N : ℕ) (hK : 1 ≤ K) : actualCount model K d true N ≤ actualCount model K d false N := by
  letI := (actual_dictionary_bound model K d false N hK).1
  let f : ActualDictionary model K d true N → ActualDictionary model K d false N :=
    fun xs => ⟨xs.val, strict_guard_weak K d xs.val _ xs.property.1, xs.property.2⟩
  apply Nat.card_le_card_of_injective f
  intro xs ys h
  exact Subtype.ext (congrArg (fun x : ActualDictionary model K d false N => x.val) h)

private theorem golden_contraction : 0 < g ∧ g < 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h0 := Real.sqrt_nonneg (5 : ℝ)
  dsimp [g, t]
  constructor <;> nlinarith

private theorem guard_seed_mono (K : ℕ) (d : ℝ) (strict : Bool)
    (xs : List Return) (D E : ℝ) (hDE : D ≤ E)
    (h : GuardTrace K d strict .high xs D) : GuardTrace K d strict .high xs E := by
  apply (uniform_guard_trace_iff_split K d strict .high xs E).mpr
  intro before a after he
  have old := (uniform_guard_trace_iff_split K d strict .high xs D).mp h before a after he
  have difference := ResetCodebook.execute_seed_difference before D E
  have nn := mul_nonneg (pow_pos golden_contraction.1 (listWeight before)).le
    (sub_nonneg.mpr hDE)
  have mono : execute .high before D ≤ execute .high before E := by linarith
  refine ⟨old.1, ?_⟩
  intro ha
  cases strict <;> simp only [Bool.false_eq_true, if_false, if_true] at *
  · exact (old.2 ha).trans mono
  · exact (old.2 ha).trans_le mono

/-- Increasing the u-run of the first complete return retains the prescribed
strict actual sources and their original zero-error futures. -/
private theorem first_return_u_lengthen (model : Model) (o : Ownership) (b : ℝ)
    (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (a a' : Return) (rest : List Return) (hm : a.m ≤ a'.m) (hr : a.r = a'.r)
    (supply : ActualPairSupply model o b .strict (a :: rest)) :
    ActualPairSupply model o b .strict (a' :: rest) := by
  have trace := (actual_strict_record_supply model o b (a :: rest) K hK hqb hbp).1.mp supply
  have rp : 0 < rho := pow_pos golden_contraction.1 6
  have r1 : rho < 1 := pow_lt_one₀ golden_contraction.1.le golden_contraction.2 (by decide)
  have cp : 0 < chi := pow_pos golden_contraction.1 20
  have c1 : chi < 1 := pow_lt_one₀ golden_contraction.1.le golden_contraction.2 (by decide)
  have hp : 0 < hSide .high := by dsimp [hSide]; linarith [golden_contraction.2]
  have ap : 0 < aSide .high := mul_pos (sub_pos.mpr r1) hp
  have bounds := (actual_complete_boundary_geometry model []).1 .high 0
  simp only [List.take_nil, execute] at bounds
  have dp := lt_trans ap bounds.1
  have cD := mul_le_mul_of_nonneg_right (show chi ^ a.r ≤ 1 from pow_le_one₀ cp.le c1.le) dp.le
  have gap : 0 ≤ hSide .high - chi ^ a.r * initial .high model := by linarith
  have pm := pow_le_pow_of_le_one rp.le r1.le hm
  have mult := mul_le_mul_of_nonneg_right pm gap
  have mono : returnMap .high a (initial .high model) ≤
      returnMap .high a' (initial .high model) := by
    dsimp [returnMap]; rw [← hr]; linarith
  apply (actual_strict_record_supply model o b (a' :: rest) K hK hqb hbp).1.mpr
  exact ⟨hr ▸ trace.1, fun he => trace.2.1 (hr.trans he),
    guard_seed_mono K _ true rest _ _ mono trace.2.2⟩

/-- The completion list keeps the first-return extra u separate from the
category-specific terminal u. Leading u letters merge only into the reset. -/
def completedList (R : Return) (a : ℕ) (first : Return) (rest : List Return) : List Return :=
  ⟨R.m + a, 1, by have := R.m_pos; omega, by decide⟩ ::
  ⟨first.m + 1, first.r, by omega, first.r_pos⟩ :: rest

/-- Delete the fixed reset, then the first-return extra u, and finally the
terminal u exactly in the final-c category. -/
def recoverFactor (R : Return) (finalC : Bool) : List Return → List CuLetter
  | reset :: extra :: rest =>
    let filled := List.replicate (reset.m - R.m) CuLetter.u ++
      List.replicate extra.r CuLetter.c ++ List.replicate (extra.m - 1) CuLetter.u ++
      executionWord rest
    if finalC then filled.dropLast else filled
  | _ => []

private theorem recover_completed (R : Return) (a : ℕ) (first : Return)
    (rest : List Return) (finalC : Bool) :
    recoverFactor R finalC (completedList R a first rest) =
      if finalC then (List.replicate a CuLetter.u ++ executionWord (first :: rest)).dropLast
      else List.replicate a CuLetter.u ++ executionWord (first :: rest) := by
  simp [recoverFactor, completedList, executionWord, List.append_assoc]

/-- One sufficiently long first-return reset works for both actual starts,
weak-to-strict insertion, and both classes of auxiliary factor completion. -/
theorem same_reset_completion (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    ∃ R : Return, R.r = 1 ∧
      max (max (xSide .high) (ySide .high)) ((lam - b) / g ^ 2 / chi ^ K) <
        hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) ∧
      (∀ (src dst : Model) (xs : List Return),
        GuardTrace K ((lam - b) / g ^ 2 / chi ^ K) false .high xs (initial .high src) →
        ActualPairSupply dst o b .strict (R :: xs)) ∧
      (∀ (model : Model) (w : List CuLetter),
        AuxiliaryFactor K ((lam - b) / g ^ 2 / chi ^ K) w → CuLetter.c ∈ w →
        ∃ (a : ℕ) (first : Return) (rest : List Return),
          (if w.getLast? = some CuLetter.c then w ++ [CuLetter.u] else w) =
            List.replicate a CuLetter.u ++ executionWord (first :: rest) ∧
          ActualPairSupply model o b .strict (completedList R a first rest) ∧
          listWeight (completedList R a first rest) = wordWeight w + (20 + 6 * R.m) +
            (if w.getLast? = some CuLetter.c then 12 else 6)) := by
  classical
  obtain ⟨P, pr, pB, ps, pw, transfer, weight, increase⟩ :=
    actual_reset_first_return o b K hK hqb hbp
  obtain ⟨Q, qr, complete⟩ := auxiliary_factor_upper_completion o b K hK hqb hbp
  let R : Return := ⟨P.m + Q.m, 1, by have := P.m_pos; omega, by decide⟩
  have rp : 0 < rho := pow_pos golden_contraction.1 6
  have r1 : rho < 1 := pow_lt_one₀ golden_contraction.1.le golden_contraction.2 (by decide)
  have cp : 0 < chi := pow_pos golden_contraction.1 20
  have c1 : chi < 1 := pow_lt_one₀ golden_contraction.1.le golden_contraction.2 (by decide)
  have hp : 0 < hSide .high := by dsimp [hSide]; linarith [golden_contraction.2]
  have ah : aSide .high < hSide .high := by
    have h := mul_pos rp hp
    dsimp [aSide]; nlinarith
  have ca : chi * aSide .high ≤ aSide .high :=
    by simpa only [aSide, one_mul] using
      mul_le_mul_of_nonneg_right c1.le (mul_pos (sub_pos.mpr r1) hp).le
  have gap : 0 ≤ hSide .high - chi * aSide .high := by linarith
  have pm := pow_le_pow_of_le_one rp.le r1.le (show P.m ≤ R.m by dsimp [R]; omega)
  have mult := mul_le_mul_of_nonneg_right pm gap
  refine ⟨R, rfl, lt_of_lt_of_le pB (by linarith), ?_, ?_⟩
  · intro src dst xs hw
    exact first_return_u_lengthen dst o b K hK hqb hbp P R xs
      (by dsimp [R]; omega) (by simpa [R] using pr) (transfer src dst xs hw)
  · intro model w hw hc
    obtain ⟨a, first, rest, parse, unique, supply, execution, weights⟩ := complete model w hw hc
    refine ⟨a, first, rest, parse, ?_, ?_⟩
    · exact first_return_u_lengthen model o b K hK hqb hbp
        ⟨Q.m + a, 1, by have := Q.m_pos; omega, by decide⟩
        ⟨R.m + a, 1, by have := R.m_pos; omega, by decide⟩
        (⟨first.m + 1, first.r, by omega, first.r_pos⟩ :: rest)
        (by dsimp [R]; omega) rfl supply
    · dsimp only [completedList, listWeight] at weights ⊢
      by_cases he : w.getLast? = some CuLetter.c
      · simp only [if_pos he] at weights ⊢; omega
      · simp only [if_neg he] at weights ⊢; omega

/-- The two c-containing factor classes are kept distinct by their literal
last letter. The false class ends in u, while the true class ends in c. -/
def FactorClass (K : ℕ) (d : ℝ) (N : ℕ) (finalC : Bool) :=
  {w : FactorDictionary (AuxiliaryLanguage K d) N // CuLetter.c ∈ w.val ∧
    (w.val.getLast? = some CuLetter.c ↔ finalC = true)}

def NoCFactor (K : ℕ) (d : ℝ) (N : ℕ) :=
  {w : FactorDictionary (AuxiliaryLanguage K d) N // CuLetter.c ∉ w.val}

private theorem no_c_geometry (w : List CuLetter) (hc : CuLetter.c ∉ w) :
    w = List.replicate w.length CuLetter.u ∧ wordWeight w = 6 * w.length := by
  have shape : w = List.replicate w.length CuLetter.u := List.eq_replicate_length.mpr (by
    intro l hl
    cases l with
    | c => exact False.elim (hc hl)
    | u => rfl)
  have weight (n : ℕ) : wordWeight (List.replicate n CuLetter.u) = 6 * n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [List.replicate_succ, wordWeight, ih]; omega
  exact ⟨shape, (congrArg wordWeight shape).trans (weight w.length)⟩

/-- At every actual weight, including zero and unsupported weights, there is
at most one factor without c. -/
theorem no_c_factor_card (K : ℕ) (d : ℝ) (N : ℕ) : Nat.card (NoCFactor K d N) ≤ 1 := by
  have unique : ∀ w v : NoCFactor K d N, w = v := by
    intro w v
    apply Subtype.ext
    apply Subtype.ext
    have wg := no_c_geometry w.val.val w.property
    have vg := no_c_geometry v.val.val v.property
    have wl := w.val.property.2
    have vl := v.val.property.2
    have lengths : w.val.val.length = v.val.val.length := by omega
    rw [wg.1, vg.1, lengths]
  have inj : Function.Injective (fun _ : NoCFactor K d N => ()) := fun w v _ => unique w v
  simpa only [Nat.card_eq_fintype_card, Fintype.card_unit] using
    Nat.card_le_card_of_injective (fun _ : NoCFactor K d N => ()) inj

private theorem completion_class_bound (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (R : Return)
    (complete : ∀ (model : Model) (w : List CuLetter),
      AuxiliaryFactor K ((lam - b) / g ^ 2 / chi ^ K) w → CuLetter.c ∈ w →
      ∃ (a : ℕ) (first : Return) (rest : List Return),
        (if w.getLast? = some CuLetter.c then w ++ [CuLetter.u] else w) =
          List.replicate a CuLetter.u ++ executionWord (first :: rest) ∧
        ActualPairSupply model o b .strict (completedList R a first rest) ∧
        listWeight (completedList R a first rest) = wordWeight w + (20 + 6 * R.m) +
          (if w.getLast? = some CuLetter.c then 12 else 6))
    (model : Model) (N : ℕ) (finalC : Bool) :
    Nat.card (FactorClass K ((lam - b) / g ^ 2 / chi ^ K) N finalC) ≤
      actualCount model K ((lam - b) / g ^ 2 / chi ^ K) true
        (N + (20 + 6 * R.m) + (if finalC then 12 else 6)) := by
  classical
  let d := (lam - b) / g ^ 2 / chi ^ K
  have completes (w : FactorClass K d N finalC) :=
    complete model w.val.val w.val.property.1 w.property.1
  choose a first rest parse supply weights using completes
  have final (w : FactorClass K d N finalC) :
      (if w.val.val.getLast? = some CuLetter.c then 12 else 6) =
        (if finalC then 12 else 6 : ℕ) := by
    cases finalC with
    | false =>
      have hn : w.val.val.getLast? ≠ some CuLetter.c := by
        intro h; have := w.property.2.mp h; cases this
      simp only [if_neg hn, Bool.false_eq_true, if_false]
    | true => simp only [if_pos (w.property.2.mpr rfl), if_true]
  let f : FactorClass K d N finalC →
      ActualDictionary model K d true (N + (20 + 6 * R.m) + (if finalC then 12 else 6)) :=
    fun w => ⟨completedList R (a w) (first w) (rest w),
      (actual_strict_record_supply model o b _ K hK hqb hbp).1.mp (supply w),
      by rw [weights w, w.val.property.2, final w]⟩
  have recovery (w : FactorClass K d N finalC) : recoverFactor R finalC (f w).val = w.val.val := by
    change recoverFactor R finalC (completedList R (a w) (first w) (rest w)) = _
    rw [recover_completed]
    cases finalC with
    | false =>
      have hn : w.val.val.getLast? ≠ some CuLetter.c := by
        intro h; have := w.property.2.mp h; cases this
      have pa := parse w
      simp only [if_neg hn] at pa
      simpa only [Bool.false_eq_true, if_false] using pa.symm
    | true =>
      have hc := w.property.2.mpr rfl
      have pa := parse w
      simp only [if_pos hc] at pa
      simp only [if_true]
      rw [← pa]
      simp
  letI := (actual_dictionary_bound model K d true
    (N + (20 + 6 * R.m) + (if finalC then 12 else 6)) (by omega)).1
  apply Nat.card_le_card_of_injective f
  intro w v he
  apply Subtype.ext
  apply Subtype.ext
  rw [← recovery w, ← recovery v]
  exact congrArg (fun xs => recoverFactor R finalC xs.val) he

/-- The same reset gives the actual weak-to-strict count injection and the
literal two-shift auxiliary count bound for either specified actual start. -/
theorem same_reset_count_comparison (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    ∃ R : Return, R.r = 1 ∧
      max (max (xSide .high) (ySide .high)) ((lam - b) / g ^ 2 / chi ^ K) <
        hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) ∧
      (∀ (src dst : Model) (N : ℕ),
        actualCount src K ((lam - b) / g ^ 2 / chi ^ K) false N ≤
          actualCount dst K ((lam - b) / g ^ 2 / chi ^ K) true (N + (20 + 6 * R.m))) ∧
      (∀ (model : Model) (N : ℕ),
        factorCount (AuxiliaryLanguage K ((lam - b) / g ^ 2 / chi ^ K)) N ≤
          actualCount model K ((lam - b) / g ^ 2 / chi ^ K) true (N + (20 + 6 * R.m) + 6) +
          actualCount model K ((lam - b) / g ^ 2 / chi ^ K) true (N + (20 + 6 * R.m) + 12) + 1) := by
  classical
  obtain ⟨R, hr, hB, transfer, complete⟩ := same_reset_completion o b K hK hqb hbp
  let d := (lam - b) / g ^ 2 / chi ^ K
  refine ⟨R, hr, hB, ?_, ?_⟩
  · intro src dst N
    letI := (actual_dictionary_bound dst K d true (N + (20 + 6 * R.m)) (by omega)).1
    let f : ActualDictionary src K d false N → ActualDictionary dst K d true (N + (20 + 6 * R.m)) :=
      fun xs => ⟨R :: xs.val,
        (actual_strict_record_supply dst o b _ K hK hqb hbp).1.mp (transfer src dst xs.val xs.property.1),
        by dsimp [listWeight]; rw [hr, xs.property.2]; omega⟩
    apply Nat.card_le_card_of_injective f
    intro xs ys he
    apply Subtype.ext
    have hv := congrArg (fun z : ActualDictionary dst K d true (N + (20 + 6 * R.m)) => z.val) he
    exact (List.cons.inj hv).2
  · intro model N
    letI := (factor_dictionary_bound (AuxiliaryLanguage K d) N).1
    letI : Finite (FactorClass K d N false) := by unfold FactorClass; infer_instance
    letI : Finite (FactorClass K d N true) := by unfold FactorClass; infer_instance
    letI : Finite (NoCFactor K d N) := by unfold NoCFactor; infer_instance
    let f : FactorDictionary (AuxiliaryLanguage K d) N →
      FactorClass K d N false ⊕ (FactorClass K d N true ⊕ NoCFactor K d N) := fun w =>
        if hc : CuLetter.c ∈ w.val then
          if hl : w.val.getLast? = some CuLetter.c then
            Sum.inr (Sum.inl ⟨w, hc, by simp [hl]⟩)
          else Sum.inl ⟨w, hc, by simp [hl]⟩
        else Sum.inr (Sum.inr ⟨w, hc⟩)
    let recover : FactorClass K d N false ⊕ (FactorClass K d N true ⊕ NoCFactor K d N) →
        FactorDictionary (AuxiliaryLanguage K d) N
      | .inl w => w.val
      | .inr (.inl w) => w.val
      | .inr (.inr w) => w.val
    have inverse : Function.LeftInverse recover f := by intro w; dsimp [f]; split <;> (try split) <;> rfl
    have card := Nat.card_le_card_of_injective f inverse.injective
    rw [Nat.card_sum, Nat.card_sum] at card
    have u := completion_class_bound o b K hK hqb hbp R complete model N false
    have c := completion_class_bound o b K hK hqb hbp R complete model N true
    have nc := no_c_factor_card K d N
    simp only [Bool.false_eq_true, if_false, if_true] at u c
    change Nat.card (FactorDictionary (AuxiliaryLanguage K d) N) ≤ _
    dsimp only [d] at card nc ⊢
    omega

private noncomputable def normalizedLog (a : ℕ → ℕ) (N : ℕ) : ℝ :=
  Real.logb 2 ((max 1 (a N) : ℕ) : ℝ) / (N : ℝ)

private theorem normalized_log_nonneg (a : ℕ → ℕ) (N : ℕ) : 0 ≤ normalizedLog a N :=
  div_nonneg (Real.logb_nonneg (by norm_num)
    (by exact_mod_cast Nat.le_max_left 1 (a N))) (by positivity)

private theorem normalized_log_mono (a b : ℕ → ℕ) (N : ℕ) (h : a N ≤ b N) :
    normalizedLog a N ≤ normalizedLog b N := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (show 0 < max 1 (a N) by omega))
    (by exact_mod_cast max_le_max_left 1 h)

/-- The actual normalized counts are nonnegative and bounded. The upper
bound is inherited through the constructed factor injection. -/
theorem actual_log_rate_bounds (model : Model) (K : ℕ) (d : ℝ) (strict : Bool)
    (hK : 1 ≤ K) : (∀ N, 0 ≤ actualLogRate model K d strict N) ∧
    IsBoundedUnder (· ≤ ·) atTop (actualLogRate model K d strict) := by
  refine ⟨normalized_log_nonneg _, ?_⟩
  apply (WordWeightRegrouping.factor_log_rate_bounds (AuxiliaryLanguage K d)).2.mono_le
  exact Eventually.of_forall (fun N => normalized_log_mono _ _ N
    (actual_dictionary_bound model K d strict N hK).2.1)

private theorem normalized_shift (a : ℕ → ℕ) (C : ℕ)
    (bounded : IsBoundedUnder (· ≤ ·) atTop (normalizedLog a)) :
    IsBoundedUnder (· ≤ ·) atTop
        (fun N : ℕ => Real.logb 2 ((max 1 (a (N + C)) : ℕ) : ℝ) / (N : ℝ)) ∧
    limsup (fun N : ℕ => Real.logb 2 ((max 1 (a (N + C)) : ℕ) : ℝ) / (N : ℝ)) atTop =
      limsup (normalizedLog a) atTop := by
  let u (N : ℕ) := normalizedLog a (N + C)
  let v (N : ℕ) := ((N + C : ℕ) : ℝ) / (N : ℝ)
  have up (N : ℕ) : 0 ≤ u N := normalized_log_nonneg a (N + C)
  have vp (N : ℕ) : 0 ≤ v N := div_nonneg (by positivity) (by positivity)
  have ub : IsBoundedUnder (· ≤ ·) atTop u := by
    change IsBoundedUnder (· ≤ ·) atTop (normalizedLog a ∘ (fun N : ℕ => N + C))
    apply (isBoundedUnder_map_iff).mp
    rw [map_add_atTop_eq_nat]
    exact bounded
  have vl : Tendsto v atTop (𝓝 (1 : ℝ)) := by
    have h : Tendsto (fun N : ℕ => (1 : ℝ) + (C : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
      simpa only [add_zero] using
        tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (C : ℝ))
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have nz : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    dsimp [v]; push_cast; field_simp
  have vb := vl.isBoundedUnder_le
  have prodBound := isBoundedUnder_le_mul_of_nonneg (Frequently.of_forall up) ub
    (Eventually.of_forall vp) vb
  have prodEq : (fun N : ℕ => Real.logb 2 ((max 1 (a (N + C)) : ℕ) : ℝ) / (N : ℝ)) =
      u * v := by
    funext N
    by_cases hn : N = 0
    · simp [hn, u, v, Pi.mul_apply]
    · have nz : (N : ℝ) ≠ 0 := by exact_mod_cast hn
      have sz : ((N + C : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : N + C ≠ 0)
      dsimp [u, v, normalizedLog, Pi.mul_apply]
      field_simp
  have lower := le_limsup_mul (Frequently.of_forall up) ub (Eventually.of_forall vp) vb
  have upper := limsup_mul_le (Frequently.of_forall up) ub (Eventually.of_forall vp) vb
  rw [vl.liminf_eq, mul_one] at lower
  rw [vl.limsup_eq, mul_one] at upper
  have shift : limsup u atTop = limsup (normalizedLog a) atTop := by
    change limsup (normalizedLog a ∘ (fun N : ℕ => N + C)) atTop = _
    rw [limsup_comp, map_add_atTop_eq_nat]
  rw [prodEq]
  exact ⟨prodBound, (le_antisymm upper lower).trans shift⟩

/-- A fixed weight shift leaves the original actual limsup rate unchanged;
its normalized shifted sequence remains bounded, including sparse weights. -/
theorem actual_fixed_shift_rate (model : Model) (K : ℕ) (d : ℝ) (strict : Bool)
    (hK : 1 ≤ K) (C : ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (fun N : ℕ =>
      Real.logb 2 ((max 1 (actualCount model K d strict (N + C)) : ℕ) : ℝ) / (N : ℝ)) ∧
    limsup (fun N : ℕ =>
      Real.logb 2 ((max 1 (actualCount model K d strict (N + C)) : ℕ) : ℝ) / (N : ℝ)) atTop =
      actualRate model K d strict :=
  normalized_shift _ C (actual_log_rate_bounds model K d strict hK).2

private theorem strict_rate_le_weak (model : Model) (K : ℕ) (d : ℝ) (hK : 1 ≤ K) :
    actualRate model K d true ≤ actualRate model K d false := by
  exact limsup_le_limsup
    (Eventually.of_forall (fun N => normalized_log_mono _ _ N
      (strict_count_le_weak model K d N hK)))
    (isBoundedUnder_of_eventually_ge
      (Eventually.of_forall (actual_log_rate_bounds model K d true hK).1)).isCoboundedUnder_le
    (actual_log_rate_bounds model K d false hK).2

/-- Reset insertion in both directions identifies both starts and both strict
flags after the fixed shifts have been proved harmless. -/
theorem actual_rates_equal (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (src dst : Model) :
    actualRate src K ((lam - b) / g ^ 2 / chi ^ K) false =
      actualRate dst K ((lam - b) / g ^ 2 / chi ^ K) true := by
  obtain ⟨R, _, _, counts, _⟩ := same_reset_count_comparison o b K hK hqb hbp
  let d := (lam - b) / g ^ 2 / chi ^ K
  have resetRate (src dst : Model) : actualRate src K d false ≤ actualRate dst K d true := by
    have shifted := actual_fixed_shift_rate dst K d true (by omega) (20 + 6 * R.m)
    have cmp := limsup_le_limsup
      (Eventually.of_forall (fun N => normalized_log_mono (actualCount src K d false)
        (fun n => actualCount dst K d true (n + (20 + 6 * R.m))) N (counts src dst N)))
      (isBoundedUnder_of_eventually_ge
        (Eventually.of_forall (actual_log_rate_bounds src K d false (by omega)).1)).isCoboundedUnder_le
      shifted.1
    exact cmp.trans_eq shifted.2
  apply le_antisymm (resetRate src dst)
  exact (strict_rate_le_weak dst K d (by omega)).trans
    ((resetRate dst src).trans (strict_rate_le_weak src K d (by omega)))

private theorem factor_rate_le_actual (model : Model) (K : ℕ) (d : ℝ) (hK : 1 ≤ K)
    (C : ℕ)
    (counts : ∀ N, factorCount (AuxiliaryLanguage K d) N ≤
      actualCount model K d true (N + C + 6) + actualCount model K d true (N + C + 12) + 1) :
    weightedFactorRate (AuxiliaryLanguage K d) ≤ actualRate model K d true := by
  let a := actualCount model K d true
  let u (N : ℕ) := Real.logb 2 ((max 1 (a (N + (C + 6))) : ℕ) : ℝ) / (N : ℝ)
  let v (N : ℕ) := Real.logb 2 ((max 1 (a (N + (C + 12))) : ℕ) : ℝ) / (N : ℝ)
  let z (N : ℕ) := Real.logb 2 3 / (N : ℝ)
  let m (N : ℕ) := max (u N) (v N)
  have up (N : ℕ) : 0 ≤ u N := normalized_log_nonneg (fun n => a (n + (C + 6))) N
  have vp (N : ℕ) : 0 ≤ v N := normalized_log_nonneg (fun n => a (n + (C + 12))) N
  have mp (N : ℕ) : 0 ≤ m N := (up N).trans (le_max_left _ _)
  have us := actual_fixed_shift_rate model K d true hK (C + 6)
  have vs := actual_fixed_shift_rate model K d true hK (C + 12)
  have uc : IsCoboundedUnder (· ≤ ·) atTop u :=
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall up)).isCoboundedUnder_le
  have vc : IsCoboundedUnder (· ≤ ·) atTop v :=
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall vp)).isCoboundedUnder_le
  have mb : IsBoundedUnder (· ≤ ·) atTop m := us.1.sup vs.1
  have mc : IsCoboundedUnder (· ≤ ·) atTop m :=
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall mp)).isCoboundedUnder_le
  have zl : Tendsto z atTop (𝓝 (0 : ℝ)) := tendsto_const_div_atTop_nhds_zero_nat _
  have sb : IsBoundedUnder (· ≤ ·) atTop (z + m) :=
    isBoundedUnder_le_add zl.isBoundedUnder_le mb
  have estimate : ∀ᶠ N in atTop, WordWeightRegrouping.factorLogRate (AuxiliaryLanguage K d) N ≤
      (z + m) N := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have np : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have original := counts N
    simp only [Nat.add_assoc] at original
    have bound (aBig : ℕ) (hf : factorCount (AuxiliaryLanguage K d) N ≤ 3 * max 1 aBig) :
        WordWeightRegrouping.factorLogRate (AuxiliaryLanguage K d) N ≤
          z N + Real.logb 2 ((max 1 aBig : ℕ) : ℝ) / (N : ℝ) := by
      have maxbound : max 1 (factorCount (AuxiliaryLanguage K d) N) ≤ 3 * max 1 aBig := by omega
      have lp := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by exact_mod_cast (show 0 < max 1 (factorCount (AuxiliaryLanguage K d) N) by omega))
        (by exact_mod_cast maxbound :
          ((max 1 (factorCount (AuxiliaryLanguage K d) N) : ℕ) : ℝ) ≤
            (3 : ℝ) * ((max 1 aBig : ℕ) : ℝ))
      rw [Real.logb_mul (by norm_num : (3 : ℝ) ≠ 0)
        (by exact_mod_cast (show max 1 aBig ≠ 0 by omega))] at lp
      have quotient := div_le_div_of_nonneg_right lp np.le
      simpa only [WordWeightRegrouping.factorLogRate, z, add_div] using quotient
    rcases le_total (a (N + (C + 6))) (a (N + (C + 12))) with h | h
    · have hf : factorCount (AuxiliaryLanguage K d) N ≤ 3 * max 1 (a (N + (C + 12))) := by
        dsimp only [a] at h ⊢; omega
      apply (bound _ hf).trans
      exact add_le_add (le_refl (z N)) (le_max_right (u N) (v N))
    · have hf : factorCount (AuxiliaryLanguage K d) N ≤ 3 * max 1 (a (N + (C + 6))) := by
        dsimp only [a] at h ⊢; omega
      apply (bound _ hf).trans
      exact add_le_add (le_refl (z N)) (le_max_left (u N) (v N))
  have cmp := limsup_le_limsup estimate
    (isBoundedUnder_of_eventually_ge
      (Eventually.of_forall (WordWeightRegrouping.factor_log_rate_bounds (AuxiliaryLanguage K d)).1)).isCoboundedUnder_le sb
  have sum := limsup_add_le zl.isBoundedUnder_ge zl.isBoundedUnder_le mc mb
  have maxEq : limsup m atTop = actualRate model K d true := by
    rw [show m = (fun N => max (u N) (v N)) from rfl, limsup_max uc vc us.1 vs.1]
    rw [us.2, vs.2, max_self]
  rw [zl.limsup_eq, zero_add, maxEq] at sum
  exact cmp.trans sum

/-- The auxiliary rate is the rate of complete actual lists, for both original
starts and both strict flags, with the original max-one sparse-weight convention. -/
theorem actual_auxiliary_rate_bridge (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (model : Model) (strict : Bool) :
    actualRate model K ((lam - b) / g ^ 2 / chi ^ K) strict =
      weightedFactorRate (AuxiliaryLanguage K ((lam - b) / g ^ 2 / chi ^ K)) := by
  obtain ⟨R, _, _, _, upper⟩ := same_reset_count_comparison o b K hK hqb hbp
  let d := (lam - b) / g ^ 2 / chi ^ K
  have lower : actualRate model K d strict ≤ weightedFactorRate (AuxiliaryLanguage K d) := by
    exact limsup_le_limsup
      (Eventually.of_forall (fun N => normalized_log_mono _ _ N
        (actual_dictionary_bound model K d strict N (by omega)).2.1))
      (isBoundedUnder_of_eventually_ge
        (Eventually.of_forall (actual_log_rate_bounds model K d strict (by omega)).1)).isCoboundedUnder_le
      (WordWeightRegrouping.factor_log_rate_bounds (AuxiliaryLanguage K d)).2
  have hi := factor_rate_le_actual model K d (by omega) (20 + 6 * R.m) (upper model)
  apply le_antisymm lower
  cases strict with
  | true => exact hi
  | false => exact hi.trans_eq (actual_rates_equal o b K hK hqb hbp model model).symm

/-- The weak original-start rate of source definition 62.8. -/
noncomputable def eta_b (K : ℕ) (b : ℝ) : ℝ :=
  actualRate .original K ((lam - b) / g ^ 2 / chi ^ K) false

def contractStrict (o : Ownership) : Contract → Bool
  | .closed => !o 0
  | .strict | .recordMargin => true

/-- These are actual simultaneous supplies on the two fixed sources, with
errors zero throughout the original tail futures. -/
def ContractDictionary (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (N : ℕ) :=
  {xs : List Return // ActualPairSupply model o b contract xs ∧ listWeight xs = N}

noncomputable def contractCount (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (N : ℕ) : ℕ := Nat.card (ContractDictionary model o b contract N)

noncomputable def contractRate (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) : ℝ :=
  limsup (fun N : ℕ => Real.logb 2 ((max 1 (contractCount model o b contract N) : ℕ) : ℝ) /
    (N : ℝ)) atTop

private theorem contract_guard_iff (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (xs : List Return) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    ActualPairSupply model o b contract xs ↔
      GuardTrace K ((lam - b) / g ^ 2 / chi ^ K) (contractStrict o contract) .high xs
        (initial .high model) := by
  cases contract with
  | closed => exact actual_closed_record_supply model o b xs K hK hqb hbp
  | strict => exact (actual_strict_record_supply model o b xs K hK hqb hbp).1
  | recordMargin => exact (actual_strict_record_supply model o b xs K hK hqb hbp).2

/-- The dictionary equivalence fixes the actual execution list itself. -/
def contractDictionaryEquiv (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (N K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    ContractDictionary model o b contract N ≃
      ActualDictionary model K ((lam - b) / g ^ 2 / chi ^ K) (contractStrict o contract) N where
  toFun xs := ⟨xs.val, (contract_guard_iff model o b contract xs.val K hK hqb hbp).mp xs.property.1,
    xs.property.2⟩
  invFun xs := ⟨xs.val, (contract_guard_iff model o b contract xs.val K hK hqb hbp).mpr xs.property.1,
    xs.property.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Closed supply uses weak counts exactly when the nearest high endpoint is
owned. Strict and record-margin supply use the strict dictionary. -/
theorem contract_count_correspondence (model : Model) (o : Ownership) (b : ℝ)
    (contract : Contract) (N K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    Finite (ContractDictionary model o b contract N) ∧
    contractCount model o b contract N =
      actualCount model K ((lam - b) / g ^ 2 / chi ^ K) (contractStrict o contract) N := by
  let e := contractDictionaryEquiv model o b contract N K hK hqb hbp
  letI := (actual_dictionary_bound model K ((lam - b) / g ^ 2 / chi ^ K)
    (contractStrict o contract) N (by omega)).1
  exact ⟨Finite.of_equiv _ e.symm, Nat.card_congr e⟩

/-- Every actual original contract and both starts have eta_b, which equals
the same actual auxiliary weighted factor rate. -/
theorem original_actual_count_rate_bridge (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    weightedFactorRate (AuxiliaryLanguage K ((lam - b) / g ^ 2 / chi ^ K)) = eta_b K b ∧
    (∀ (model : Model) (strict : Bool),
      actualRate model K ((lam - b) / g ^ 2 / chi ^ K) strict = eta_b K b) ∧
    (∀ (model : Model) (contract : Contract), contractRate model o b contract = eta_b K b) := by
  have canonical := (actual_auxiliary_rate_bridge o b K hK hqb hbp .original false).symm
  refine ⟨canonical, ?_, ?_⟩
  · intro model strict
    exact (actual_auxiliary_rate_bridge o b K hK hqb hbp model strict).trans canonical
  · intro model contract
    have counts (N : ℕ) := (contract_count_correspondence model o b contract N K hK hqb hbp).2
    simp only [contractRate, counts]
    exact (actual_auxiliary_rate_bridge o b K hK hqb hbp model (contractStrict o contract)).trans canonical

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge
