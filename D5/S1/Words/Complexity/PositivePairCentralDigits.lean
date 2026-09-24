/- GID: D5/S1/Words/Complexity/PositivePairCentralDigits
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairCentralDigits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual positive-pair directions form injective equal-length multi-scale digit words. -/
import D5.S1.Words.Complexity.PositivePairFullFamilySpan
import Mathlib.Data.List.Indexes
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Multi-scale central digits from actual positive pairs

At a fixed degree, this module extracts exactly as many independent members of
the recursive positive-pair family as there are Lyndon words.  It then uses
literal letter replication and actual list concatenation to make bounded
base-`2^r` digits at several scales.
-/
namespace D5.S1.Words.Complexity.PositivePairCentralDigits

open scoped BigOperators
open D5.S1.Words.Complexity.LyndonStandardBracket
open D5.S1.Words.Complexity.PositivePairWordCoefficients
open D5.S1.Words.Complexity.PositivePairFullFamilySpan

variable {A : Type*}

/-- Actual Lyndon words of one fixed length. -/
def ActualLyndonWord (A : Type*) [LinearOrder A] (r : ℕ) :=
  {w : List A // w.length = r ∧ IsLyndon w}

noncomputable instance [LinearOrder A] (r : ℕ) :
    LinearOrder (ActualLyndonWord A r) :=
  LinearOrder.lift' Subtype.val Subtype.val_injective

noncomputable instance [Fintype A] [LinearOrder A] (r : ℕ) :
    Fintype (ActualLyndonWord A r) := by
  let intoVector : ActualLyndonWord A r → List.Vector A r :=
    fun w ↦ ⟨w.1, w.2.1⟩
  exact Fintype.ofInjective intoVector (fun x y h ↦
    Subtype.ext (congrArg (fun z : List.Vector A r ↦ z.1) h))

/-- The actual number of Lyndon words of length `r`. -/
noncomputable def actualLyndonCount [Fintype A] [LinearOrder A] (r : ℕ) : ℕ :=
  Fintype.card (ActualLyndonWord A r)

private theorem exists_actual_independent_directions
    [Fintype A] [LinearOrder A] (r : ℕ) :
    ∃ select : Fin (actualLyndonCount (A := A) r) → PositivePairIndex A r,
      LinearIndependent ℚ (fun i ↦ actualLeadingDifference r (select i)) := by
  classical
  have hRationalLI : LinearIndependent ℚ
      (fun w : ActualLyndonWord A r ↦
        toRationalWordPolynomial (standardBracket w.1)) := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    by_contra hgi
    let t := s.filter (fun j ↦ g j ≠ 0)
    have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
    let m := t.min' ht
    have hm : m ∈ t := Finset.min'_mem t ht
    have hms : m ∈ s := (Finset.mem_filter.mp hm).1
    have hmg : g m ≠ 0 := (Finset.mem_filter.mp hm).2
    have hcoeff := congrArg
      (fun p : RationalWordPolynomial A ↦ p.coeff (FreeMonoid.ofList m.1)) hsum
    simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] at hcoeff
    have hself :
        (toRationalWordPolynomial (standardBracket m.1)).coeff
            (FreeMonoid.ofList m.1) = 1 := by
      simp only [toRationalWordPolynomial, MonoidAlgebra.coeff_mapRingHom]
      norm_num [(standardBracket_hasLeadingWord m.1
        (isLyndon_standardFactorClosed m.1 m.2.2)).2.1]
    have hother : ∀ j ∈ s, j ≠ m →
        g j • (toRationalWordPolynomial (standardBracket j.1)).coeff
          (FreeMonoid.ofList m.1) = 0 := by
      intro j hjs hjm
      by_cases hgj : g j = 0
      · simp [hgj]
      have hjt : j ∈ t := Finset.mem_filter.mpr ⟨hjs, hgj⟩
      have hmj : m < j :=
        lt_of_le_of_ne (Finset.min'_le t j hjt) (Ne.symm hjm)
      change m.1 < j.1 at hmj
      have hcoeff0 :
          (standardBracket j.1).coeff (FreeMonoid.ofList m.1) = 0 := by
        rw [← Finsupp.notMem_support_iff]
        intro hmem
        have hjmle : j.1 ≤ m.1 :=
          (standardBracket_hasLeadingWord j.1
            (isLyndon_standardFactorClosed j.1 j.2.2)).2.2 _ hmem
        exact (not_lt_of_ge hjmle) hmj
      simp [toRationalWordPolynomial, hcoeff0]
    rw [Finset.sum_eq_single m hother (fun hmnot ↦ (hmnot hms).elim),
      hself] at hcoeff
    exact hmg (by simpa using hcoeff)
  let generators : Set (RationalWordPolynomial A) :=
    Set.range (actualLeadingDifference (A := A) r)
  let V := Submodule.span ℚ generators
  let lyndonInV : ActualLyndonWord A r → V := fun w ↦
    ⟨toRationalWordPolynomial (standardBracket w.1),
      by
        change toRationalWordPolynomial (standardBracket w.1) ∈
          fullFamilySpan (A := A) r
        have h := every_standardBracket_mem (A := A) w.1
        have heq : fullFamilySpan (A := A) w.1.length =
            fullFamilySpan (A := A) r := congrArg _ w.2.1
        exact heq ▸ h⟩
  have hL : LinearIndependent ℚ lyndonInV := by
    apply LinearIndependent.of_comp (Submodule.subtype V)
    change LinearIndependent ℚ
      (fun w : ActualLyndonWord A r ↦
        toRationalWordPolynomial (standardBracket w.1))
    exact hRationalLI
  letI : Module.Finite ℚ V := by
    dsimp only [V]
    exact Module.Finite.span_of_finite ℚ (Set.finite_range _)
  have hcount : actualLyndonCount (A := A) r ≤ Module.finrank ℚ V := by
    simpa [actualLyndonCount] using hL.fintype_card_le_finrank
  obtain ⟨basisSet, hbasisSubset, hbasisCard, _, hbasisLI⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℚ generators
  obtain ⟨chosen, hchosenSubset, hchosenCard⟩ :=
    Finset.exists_subset_card_eq
      (s := basisSet) (n := actualLyndonCount (A := A) r)
      (by simpa [hbasisCard, V] using hcount)
  let enumerate : Fin (actualLyndonCount (A := A) r) ≃ chosen :=
    (Finset.equivFinOfCardEq hchosenCard).symm
  have hchosenLI :
      LinearIndependent ℚ ((↑) : chosen → RationalWordPolynomial A) :=
    hbasisLI.mono (by
      intro x hx
      exact hchosenSubset hx)
  choose preimage hpreimage using fun i : Fin (actualLyndonCount (A := A) r) ↦
    hbasisSubset (hchosenSubset (enumerate i).2)
  refine ⟨preimage, ?_⟩
  have henum : LinearIndependent ℚ
      (fun i ↦ ((enumerate i : chosen) : RationalWordPolynomial A)) :=
    hchosenLI.comp (fun i ↦ enumerate i) enumerate.injective
  have heq :
      (fun i ↦ ((enumerate i : chosen) : RationalWordPolynomial A)) =
        (fun i ↦ actualLeadingDifference r (preimage i)) := by
    funext i
    exact (hpreimage i).symm
  rw [heq] at henum
  exact henum

/-- Deterministic classical selection of independent directions from the full
actual indexed positive-pair family. -/
noncomputable def selectedDirection [Fintype A] [LinearOrder A] (r : ℕ) :
    Fin (actualLyndonCount (A := A) r) → PositivePairIndex A r :=
  Classical.choose (exists_actual_independent_directions (A := A) r)

/-- The base used by degree-`r` central digits. -/
def digitBase (r : ℕ) : ℕ := 2 ^ r

private def zeroDigit (r : ℕ) : Fin (digitBase r) :=
  ⟨0, by simp [digitBase]⟩

/-- A complete digit array: one base-`2^r` digit for every selected direction
and every scale below `t`. -/
abbrev DigitArray [Fintype A] [LinearOrder A] (r t : ℕ) :=
  Fin (actualLyndonCount (A := A) r) → Fin t → Fin (digitBase r)

/-- The base-`2^r` natural encoded by one direction's scale digits. -/
noncomputable def digitValue [Fintype A] [LinearOrder A] (r t : ℕ)
    (digits : DigitArray (A := A) r t)
    (direction : Fin (actualLyndonCount (A := A) r)) : ℕ :=
  Nat.ofDigits (digitBase r)
    (List.ofFn fun scale : Fin t ↦ (digits direction scale : ℕ))

private def repeatedWord (count : ℕ) (word : List A) : List A :=
  (List.replicate count word).flatten

/-- One actual digit block: `j` powered copies of `u`, then the remaining
`2^r-1-j` powered copies of `v`. -/
noncomputable def digitBlock [Fintype A] [LinearOrder A] (r : ℕ)
    (direction : Fin (actualLyndonCount (A := A) r)) (scale digit : ℕ) : List A :=
  let pair := positivePairWords r (selectedDirection (A := A) r direction)
  let poweredU := literalPowerWord (2 ^ scale) pair.1
  let poweredV := literalPowerWord (2 ^ scale) pair.2
  repeatedWord digit poweredU ++
    repeatedWord (digitBase r - 1 - digit) poweredV

/-- Deterministic direction-major, scale-minor concatenation of all actual
digit blocks.  For `t=0` both index lists are empty, so the result is `[]`. -/
noncomputable def multiScaleWord [Fintype A] [LinearOrder A] (r t : ℕ)
    (digits : DigitArray (A := A) r t) : List A :=
  (List.ofFn fun direction : Fin (actualLyndonCount (A := A) r) ↦
    (List.ofFn fun scale : Fin t ↦
      digitBlock (A := A) r direction scale (digits direction scale)).flatten).flatten

private noncomputable def directionWord [Fintype A] [LinearOrder A]
    (r t : ℕ) (digits : DigitArray (A := A) r t)
    (direction : Fin (actualLyndonCount (A := A) r)) : List A :=
  (List.ofFn fun scale : Fin t ↦
    digitBlock (A := A) r direction scale (digits direction scale)).flatten

/-- The all-`v` reference is the zero digit array. -/
noncomputable def referenceWord [Fintype A] [LinearOrder A] (r t : ℕ) : List A :=
  multiScaleWord (A := A) r t (fun _ _ ↦ zeroDigit r)

/-- The fixed length coefficient appearing in the common length law. -/
noncomputable def baseLength [Fintype A] [LinearOrder A] (r : ℕ) : ℕ :=
  (digitBase r - 1) *
    ∑ i : Fin (actualLyndonCount (A := A) r),
      (positivePairWords r (selectedDirection (A := A) r i)).1.length

private noncomputable def rationalMagnus (source : List A) :
    RationalWordPolynomial A :=
  toRationalWordPolynomial (magnusPolynomial source)

private def AgreesBelow (r : ℕ) (left right : List A) : Prop :=
  ∀ pattern : List A, pattern.length < r →
    (rationalMagnus left).coeff (FreeMonoid.ofList pattern) =
      (rationalMagnus right).coeff (FreeMonoid.ofList pattern)

private theorem agreesBelow_append_and_degree_add
    (r : ℕ) {u u0 v v0 : List A}
    (hu : AgreesBelow r u u0) (hv : AgreesBelow r v v0) :
    AgreesBelow r (u ++ v) (u0 ++ v0) ∧
      ∀ pattern : List A, pattern.length = r →
        (rationalMagnus (u ++ v)).coeff (FreeMonoid.ofList pattern) -
            (rationalMagnus (u0 ++ v0)).coeff (FreeMonoid.ofList pattern) =
          ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
            (rationalMagnus u0).coeff (FreeMonoid.ofList pattern)) +
          ((rationalMagnus v).coeff (FreeMonoid.ofList pattern) -
            (rationalMagnus v0).coeff (FreeMonoid.ofList pattern)) := by
  classical
  let centralWordSplits (w : FreeMonoid A) :
      Finset (FreeMonoid A × FreeMonoid A) :=
    (Finset.range (FreeMonoid.length w + 1)).image fun i ↦
      (FreeMonoid.ofList ((FreeMonoid.toList w).take i),
        FreeMonoid.ofList ((FreeMonoid.toList w).drop i))
  have mem_centralWordSplits_iff
      (w : FreeMonoid A) (pair : FreeMonoid A × FreeMonoid A) :
      pair ∈ centralWordSplits w ↔ pair.1 * pair.2 = w := by
    change pair ∈ (Finset.range (FreeMonoid.length w + 1)).image
        (fun i ↦
          (FreeMonoid.ofList ((FreeMonoid.toList w).take i),
            FreeMonoid.ofList ((FreeMonoid.toList w).drop i))) ↔ _
    constructor
    · intro hpair
      rcases Finset.mem_image.mp hpair with ⟨i, _, rfl⟩
      apply FreeMonoid.toList.injective
      simp [List.take_append_drop]
    · intro hpair
      apply Finset.mem_image.mpr
      refine ⟨FreeMonoid.length pair.1, ?_, ?_⟩
      · rw [Finset.mem_range, ← hpair, FreeMonoid.length_mul]
        omega
      · apply Prod.ext
        · apply FreeMonoid.toList.injective
          have hlist := congrArg FreeMonoid.toList hpair
          simpa [FreeMonoid.toList_mul, FreeMonoid.length,
            List.take_append_of_le_length] using
            congrArg (List.take (FreeMonoid.length pair.1)) hlist.symm
        · apply FreeMonoid.toList.injective
          have hlist := congrArg FreeMonoid.toList hpair
          simpa [FreeMonoid.toList_mul, FreeMonoid.length,
            List.drop_append_of_le_length] using
            congrArg (List.drop (FreeMonoid.length pair.1)) hlist.symm
  have central_coeff_mul_eq_split_sum
      (p q : RationalWordPolynomial A) (w : FreeMonoid A) :
      (p * q).coeff w =
        ∑ i ∈ Finset.range (FreeMonoid.length w + 1),
          p.coeff (FreeMonoid.ofList ((FreeMonoid.toList w).take i)) *
            q.coeff (FreeMonoid.ofList ((FreeMonoid.toList w).drop i)) := by
    rw [MonoidAlgebra.coeff_mul_antidiag p q w (centralWordSplits w)
      (fun {pair} ↦ mem_centralWordSplits_iff w pair)]
    dsimp only [centralWordSplits]
    rw [Finset.sum_image]
    intro i hi j hj hij
    have hi' : i ≤ FreeMonoid.length w := by
      have : i < FreeMonoid.length w + 1 := by simpa using hi
      omega
    have hj' : j ≤ FreeMonoid.length w := by
      have : j < FreeMonoid.length w + 1 := by simpa using hj
      omega
    have hi'' : i ≤ (FreeMonoid.toList w).length := by
      simpa [FreeMonoid.length] using hi'
    have hj'' : j ≤ (FreeMonoid.toList w).length := by
      simpa [FreeMonoid.length] using hj'
    have hlength := congrArg (fun pair : FreeMonoid A × FreeMonoid A ↦
      FreeMonoid.length pair.1) hij
    simpa [FreeMonoid.length, List.length_take, Nat.min_eq_left hi'',
      Nat.min_eq_left hj''] using hlength
  have magnusAppend (left right : List A) :
      rationalMagnus (left ++ right) =
        rationalMagnus left * rationalMagnus right := by
    simp [rationalMagnus, magnusPolynomial_append]
  have coeffEmpty (source : List A) : (rationalMagnus source).coeff 1 = 1 := by
    have hcount :
        D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          [] source = 1 := by
      induction source with
      | nil => rfl
      | cons a source ih => simpa [
          D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount] using ih
    rw [show (1 : FreeMonoid A) = FreeMonoid.ofList [] by rfl]
    change (Int.castRingHom ℚ)
        ((magnusPolynomial source).coeff (FreeMonoid.ofList [])) = 1
    rw [magnusPolynomial_coeff_scatteredCount]
    norm_num [hcount]
  constructor
  · intro pattern hp
    simp only [magnusAppend, central_coeff_mul_eq_split_sum,
      FreeMonoid.length, FreeMonoid.toList_ofList]
    apply Finset.sum_congr rfl
    intro i hi
    have htake : (pattern.take i).length < r :=
      lt_of_le_of_lt (List.length_take_le' i pattern) hp
    have hdrop : (pattern.drop i).length < r := by
      rw [List.length_drop]
      omega
    rw [hu _ htake, hv _ hdrop]
  · intro pattern hp
    simp only [magnusAppend, central_coeff_mul_eq_split_sum,
      FreeMonoid.length, FreeMonoid.toList_ofList, ← Finset.sum_sub_distrib]
    calc
      ∑ i ∈ Finset.range (pattern.length + 1),
          ((rationalMagnus u).coeff (FreeMonoid.ofList (pattern.take i)) *
              (rationalMagnus v).coeff (FreeMonoid.ofList (pattern.drop i)) -
            (rationalMagnus u0).coeff (FreeMonoid.ofList (pattern.take i)) *
              (rationalMagnus v0).coeff (FreeMonoid.ofList (pattern.drop i))) =
          ∑ i ∈ Finset.range (pattern.length + 1),
            (if i = 0 then
              (rationalMagnus v).coeff (FreeMonoid.ofList pattern) -
                (rationalMagnus v0).coeff (FreeMonoid.ofList pattern)
            else if i = pattern.length then
              (rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
                (rationalMagnus u0).coeff (FreeMonoid.ofList pattern)
            else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hi0 : i = 0
              · subst i
                simp [coeffEmpty]
              · by_cases hilast : i = pattern.length
                · subst i
                  simp [hi0, coeffEmpty]
                · have hiLt : i < r := by
                    have : i < pattern.length + 1 := Finset.mem_range.mp hi
                    omega
                  have htake : (pattern.take i).length < r := by
                    rw [List.length_take, hp, Nat.min_eq_left (Nat.le_of_lt hiLt)]
                    exact hiLt
                  have hdrop : (pattern.drop i).length < r := by
                    rw [List.length_drop, hp]
                    omega
                  rw [hu _ htake, hv _ hdrop, if_neg hi0, if_neg hilast]
                  ring
      _ = ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
            (rationalMagnus u0).coeff (FreeMonoid.ofList pattern)) +
          ((rationalMagnus v).coeff (FreeMonoid.ofList pattern) -
            (rationalMagnus v0).coeff (FreeMonoid.ofList pattern)) := by
            by_cases hempty : pattern = []
            · subst pattern
              simp [coeffEmpty]
            · have hn : pattern.length ≠ 0 := by
                intro hzero
                exact hempty (List.eq_nil_of_length_eq_zero hzero)
              let summand := fun i : ℕ ↦
                if i = 0 then
                  (rationalMagnus v).coeff (FreeMonoid.ofList pattern) -
                    (rationalMagnus v0).coeff (FreeMonoid.ofList pattern)
                else if i = pattern.length then
                  (rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
                    (rationalMagnus u0).coeff (FreeMonoid.ofList pattern)
                else 0
              have hzero : 0 ∈ Finset.range (pattern.length + 1) := by simp
              have hlast : pattern.length ∈
                  (Finset.range (pattern.length + 1)).erase 0 := by
                exact Finset.mem_erase.mpr ⟨hn, by simp⟩
              have hrest :
                  ∑ i ∈ ((Finset.range (pattern.length + 1)).erase 0).erase
                      pattern.length, summand i = 0 := by
                apply Finset.sum_eq_zero
                intro i hi
                have hiLast : i ≠ pattern.length := (Finset.mem_erase.mp hi).1
                have hi0 : i ≠ 0 :=
                  (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
                simp [summand, hi0, hiLast]
              change ∑ i ∈ Finset.range (pattern.length + 1), summand i = _
              rw [← Finset.sum_erase_add _ summand hzero,
                ← Finset.sum_erase_add _ summand hlast, hrest]
              simp [summand, hn]

private theorem repeatedWord_central_data
    (r n : ℕ) {u v : List A} (hu : AgreesBelow r u v) :
    AgreesBelow r (repeatedWord n u) (repeatedWord n v) ∧
      ∀ pattern : List A, pattern.length = r →
        (rationalMagnus (repeatedWord n u)).coeff (FreeMonoid.ofList pattern) -
            (rationalMagnus (repeatedWord n v)).coeff (FreeMonoid.ofList pattern) =
          (n : ℚ) *
            ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
              (rationalMagnus v).coeff (FreeMonoid.ofList pattern)) := by
  classical
  induction n with
  | zero =>
      constructor
      · intro pattern _
        rfl
      · intro pattern _
        simp [repeatedWord]
  | succ n ih =>
      have happ := agreesBelow_append_and_degree_add r hu ih.1
      constructor
      · simpa [repeatedWord, List.replicate_succ] using happ.1
      · intro pattern hp
        have hdegree := happ.2 pattern hp
        rw [ih.2 pattern hp] at hdegree
        change
          (rationalMagnus (u ++ repeatedWord n u)).coeff
                (FreeMonoid.ofList pattern) -
              (rationalMagnus (v ++ repeatedWord n v)).coeff
                (FreeMonoid.ofList pattern) =
            ((n + 1 : ℕ) : ℚ) *
              ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
                (rationalMagnus v).coeff (FreeMonoid.ofList pattern))
        calc
          _ = ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
                (rationalMagnus v).coeff (FreeMonoid.ofList pattern)) +
              (n : ℚ) * ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
                (rationalMagnus v).coeff (FreeMonoid.ofList pattern)) := hdegree
          _ = ((n + 1 : ℕ) : ℚ) *
              ((rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
                (rationalMagnus v).coeff (FreeMonoid.ofList pattern)) := by
                push_cast
                ring

private theorem digitBlock_central_data
    [Fintype A] [LinearOrder A] (r t : ℕ)
    (direction : Fin (actualLyndonCount (A := A) r)) (scale : Fin t)
    (digit : Fin (digitBase r)) :
    AgreesBelow r (digitBlock (A := A) r direction scale digit)
        (digitBlock (A := A) r direction scale 0) ∧
      ∀ pattern : List A, pattern.length = r →
        (rationalMagnus (digitBlock (A := A) r direction scale digit)).coeff
              (FreeMonoid.ofList pattern) -
            (rationalMagnus (digitBlock (A := A) r direction scale 0)).coeff
              (FreeMonoid.ofList pattern) =
          (digit : ℚ) * ((digitBase r : ℕ) ^ (scale : ℕ) : ℚ) *
            (actualLeadingDifference r
              (selectedDirection (A := A) r direction)).coeff
                (FreeMonoid.ofList pattern) := by
  classical
  have poweredPair_central_data (scale' : ℕ) :
      let pair := positivePairWords r (selectedDirection (A := A) r direction)
      let u := literalPowerWord (2 ^ scale') pair.1
      let v := literalPowerWord (2 ^ scale') pair.2
      AgreesBelow r u v ∧
        ∀ pattern : List A, pattern.length = r →
          (rationalMagnus u).coeff (FreeMonoid.ofList pattern) -
              (rationalMagnus v).coeff (FreeMonoid.ofList pattern) =
            ((digitBase r : ℕ) ^ scale' : ℚ) *
              (actualLeadingDifference r
                (selectedDirection (A := A) r direction)).coeff
                  (FreeMonoid.ofList pattern) := by
    dsimp only
    let index := selectedDirection (A := A) r direction
    let pair := positivePairWords r index
    have hpower := literalPowerSubstitution_actual_positivePair
      (A := A) (2 ^ scale') r index
    constructor
    · intro pattern hp
      simp only [rationalMagnus, toRationalWordPolynomial,
        MonoidAlgebra.coeff_mapRingHom, magnusPolynomial_coeff_scatteredCount]
      change
        (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            pattern (literalPowerWord (2 ^ scale') pair.1) : ℚ) =
          (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
            pattern (literalPowerWord (2 ^ scale') pair.2) : ℚ)
      exact_mod_cast hpower.2.2.2.2.1 pattern hp
    · intro pattern hp
      simp only [rationalMagnus, toRationalWordPolynomial,
        MonoidAlgebra.coeff_mapRingHom, magnusPolynomial_coeff_scatteredCount]
      have hdegree := hpower.2.2.2.2.2 pattern hp
      let bounded : CutoffWord A r :=
        ⟨FreeMonoid.ofList pattern, by simpa [FreeMonoid.length, hp]⟩
      have hactual : (actualLeadingDifference r index).coeff bounded.1 =
          (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
              (FreeMonoid.toList bounded.1) (positivePairWords r index).1 : ℚ) -
            (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
              (FreeMonoid.toList bounded.1) (positivePairWords r index).2 : ℚ) := by
        have hcoeffAt : (actualLeadingDifference r index).coeff bounded.1 =
            (cutoffMagnus r (positivePairWords r index).1 -
              cutoffMagnus r (positivePairWords r index).2) bounded := by
          simp [actualLeadingDifference, cutoffRestriction, cutoffLift,
            Finsupp.mapDomain_apply Subtype.val_injective]
        rw [hcoeffAt]
        simpa [cutoffMagnus, cutoffRestriction] using
          (full_positivePair_coefficient_checkpoint r index).2 bounded
      rw [show ((2 ^ scale' : ℕ) : ℚ) ^ r =
          ((digitBase r : ℕ) ^ scale' : ℚ) by
        norm_num [digitBase, ← pow_mul, Nat.mul_comm]] at hdegree
      have hactual' :
          (actualLeadingDifference r index).coeff (FreeMonoid.ofList pattern) =
            (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
                pattern pair.1 : ℚ) -
              (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
                pattern pair.2 : ℚ) := by
        simpa [bounded, pair, FreeMonoid.ofList_toList] using hactual
      rw [hactual']
      exact hdegree
  let pair := positivePairWords r (selectedDirection (A := A) r direction)
  let u := literalPowerWord (2 ^ (scale : ℕ)) pair.1
  let v := literalPowerWord (2 ^ (scale : ℕ)) pair.2
  have hp := poweredPair_central_data (scale : ℕ)
  have hrep := repeatedWord_central_data r (digit : ℕ) hp.1
  have htail : AgreesBelow r
      (repeatedWord (digitBase r - 1 - (digit : ℕ)) v)
      (repeatedWord (digitBase r - 1 - (digit : ℕ)) v) := by
    intro pattern _
    rfl
  have happ := agreesBelow_append_and_degree_add r hrep.1 htail
  have hdigitLe : (digit : ℕ) ≤ digitBase r - 1 := by
    have hdigit : (digit : ℕ) < digitBase r := digit.isLt
    omega
  have hrepeatAdd (m n : ℕ) (word : List A) :
      repeatedWord m word ++ repeatedWord n word = repeatedWord (m + n) word := by
    unfold repeatedWord
    rw [List.replicate_add, List.flatten_append]
  have href : repeatedWord (digit : ℕ) v ++
      repeatedWord (digitBase r - 1 - (digit : ℕ)) v =
        digitBlock (A := A) r direction scale 0 := by
    rw [hrepeatAdd, Nat.add_sub_of_le hdigitLe]
    simp [digitBlock, pair, v, repeatedWord]
  constructor
  · simpa [digitBlock, pair, u, v, href] using happ.1
  · intro pattern hpattern
    have hdegree := happ.2 pattern hpattern
    rw [hrep.2 pattern hpattern] at hdegree
    simpa [digitBlock, pair, u, v, href, hp.2 pattern hpattern,
      mul_assoc] using hdegree

private noncomputable def degreeDifference (pattern : List A)
    (words : List A × List A) : ℚ :=
  (rationalMagnus words.1).coeff (FreeMonoid.ofList pattern) -
    (rationalMagnus words.2).coeff (FreeMonoid.ofList pattern)

private theorem flatten_central_data
    (r : ℕ) (words : List (List A × List A))
    (hbelow : ∀ words' ∈ words, AgreesBelow r words'.1 words'.2) :
    AgreesBelow r (words.map Prod.fst).flatten
        (words.map Prod.snd).flatten ∧
      ∀ pattern : List A, pattern.length = r →
        degreeDifference pattern
            ((words.map Prod.fst).flatten, (words.map Prod.snd).flatten) =
          (words.map (degreeDifference pattern)).sum := by
  classical
  induction words with
  | nil =>
      constructor
      · intro pattern _
        rfl
      · intro pattern _
        simp [degreeDifference]
  | cons head tail ih =>
      have hhead : AgreesBelow r head.1 head.2 := hbelow head (by simp)
      have htail : ∀ words' ∈ tail, AgreesBelow r words'.1 words'.2 := by
        intro words' hwords'
        exact hbelow words' (by simp [hwords'])
      have htailData := ih htail
      have happ := agreesBelow_append_and_degree_add r hhead htailData.1
      constructor
      · simpa using happ.1
      · intro pattern hpattern
        have hdegree := happ.2 pattern hpattern
        change degreeDifference pattern
              (head.1 ++ (tail.map Prod.fst).flatten,
                head.2 ++ (tail.map Prod.snd).flatten) =
            degreeDifference pattern head +
              degreeDifference pattern
                ((tail.map Prod.fst).flatten, (tail.map Prod.snd).flatten) at hdegree
        rw [htailData.2 pattern hpattern] at hdegree
        simpa only [List.map_cons, List.flatten_cons, List.sum_cons] using hdegree

private theorem directionWord_central_data
    [Fintype A] [LinearOrder A] (r t : ℕ)
    (digits : DigitArray (A := A) r t)
    (direction : Fin (actualLyndonCount (A := A) r)) :
    AgreesBelow r (directionWord (A := A) r t digits direction)
        (directionWord (A := A) r t (fun _ _ ↦ zeroDigit r) direction) ∧
      ∀ pattern : List A, pattern.length = r →
        degreeDifference pattern
            (directionWord (A := A) r t digits direction,
              directionWord (A := A) r t (fun _ _ ↦ zeroDigit r) direction) =
          (digitValue (A := A) r t digits direction : ℚ) *
            (actualLeadingDifference r
              (selectedDirection (A := A) r direction)).coeff
                (FreeMonoid.ofList pattern) := by
  classical
  let words : List (List A × List A) :=
    List.ofFn fun scale : Fin t ↦
      (digitBlock (A := A) r direction scale (digits direction scale),
        digitBlock (A := A) r direction scale 0)
  have hbelow : ∀ words' ∈ words,
      AgreesBelow r words'.1 words'.2 := by
    intro words' hwords'
    rcases List.mem_ofFn.mp hwords' with ⟨scale, rfl⟩
    exact (digitBlock_central_data (A := A) r t direction scale
      (digits direction scale)).1
  have hdata := flatten_central_data (A := A) r words hbelow
  have hvalueSum : (digitValue (A := A) r t digits direction : ℚ) =
      ∑ scale : Fin t, (digits direction scale : ℚ) *
        ((digitBase r : ℕ) ^ (scale : ℕ) : ℚ) := by
    have hnat : digitValue (A := A) r t digits direction =
        ∑ scale : Fin t,
          (digits direction scale : ℕ) * digitBase r ^ (scale : ℕ) := by
      simp [digitValue, Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn,
        List.sum_ofFn]
    exact_mod_cast hnat
  constructor
  · simpa [words, directionWord, zeroDigit, Function.comp_def] using hdata.1
  · intro pattern hpattern
    calc
      degreeDifference pattern
          (directionWord (A := A) r t digits direction,
            directionWord (A := A) r t (fun _ _ ↦ zeroDigit r) direction) =
          (words.map (degreeDifference pattern)).sum := by
            simpa [words, directionWord, zeroDigit, Function.comp_def] using
              hdata.2 pattern hpattern
      _ = ∑ scale : Fin t,
            (digits direction scale : ℚ) *
                ((digitBase r : ℕ) ^ (scale : ℕ) : ℚ) *
              (actualLeadingDifference r
                (selectedDirection (A := A) r direction)).coeff
                  (FreeMonoid.ofList pattern) := by
            rw [show words.map (degreeDifference pattern) =
                List.ofFn (fun scale : Fin t ↦
                  degreeDifference pattern
                    (digitBlock (A := A) r direction scale
                        (digits direction scale),
                      digitBlock (A := A) r direction scale 0)) by
              simp [words, Function.comp_def], List.sum_ofFn]
            apply Finset.sum_congr rfl
            intro scale _
            exact digitBlock_central_data (A := A) r t direction scale
              (digits direction scale) |>.2 pattern hpattern
      _ = (digitValue (A := A) r t digits direction : ℚ) *
            (actualLeadingDifference r
              (selectedDirection (A := A) r direction)).coeff
                (FreeMonoid.ofList pattern) := by
            rw [hvalueSum]
            rw [Finset.sum_mul]

private theorem multiScaleWord_central_data
    [Fintype A] [LinearOrder A] (r t : ℕ)
    (digits : DigitArray (A := A) r t) :
    AgreesBelow r (multiScaleWord (A := A) r t digits)
        (referenceWord (A := A) r t) ∧
      ∀ pattern : List A, pattern.length = r →
        degreeDifference pattern
            (multiScaleWord (A := A) r t digits,
              referenceWord (A := A) r t) =
          ∑ direction : Fin (actualLyndonCount (A := A) r),
            (digitValue (A := A) r t digits direction : ℚ) *
              (actualLeadingDifference r
                (selectedDirection (A := A) r direction)).coeff
                  (FreeMonoid.ofList pattern) := by
  classical
  let words : List (List A × List A) :=
    List.ofFn fun direction : Fin (actualLyndonCount (A := A) r) ↦
      (directionWord (A := A) r t digits direction,
        directionWord (A := A) r t (fun _ _ ↦ zeroDigit r) direction)
  have hbelow : ∀ words' ∈ words,
      AgreesBelow r words'.1 words'.2 := by
    intro words' hwords'
    rcases List.mem_ofFn.mp hwords' with ⟨direction, rfl⟩
    exact (directionWord_central_data (A := A) r t digits direction).1
  have hdata := flatten_central_data (A := A) r words hbelow
  constructor
  · simpa [words, multiScaleWord, referenceWord, directionWord,
      Function.comp_def] using hdata.1
  · intro pattern hpattern
    calc
      degreeDifference pattern
          (multiScaleWord (A := A) r t digits,
            referenceWord (A := A) r t) =
          (words.map (degreeDifference pattern)).sum := by
            simpa [words, multiScaleWord, referenceWord, directionWord,
              Function.comp_def] using hdata.2 pattern hpattern
      _ = ∑ direction : Fin (actualLyndonCount (A := A) r),
            (digitValue (A := A) r t digits direction : ℚ) *
              (actualLeadingDifference r
                (selectedDirection (A := A) r direction)).coeff
                  (FreeMonoid.ofList pattern) := by
            rw [show words.map (degreeDifference pattern) =
                List.ofFn (fun direction :
                    Fin (actualLyndonCount (A := A) r) ↦
                  degreeDifference pattern
                    (directionWord (A := A) r t digits direction,
                      directionWord (A := A) r t
                        (fun _ _ ↦ zeroDigit r) direction)) by
              simp [words, Function.comp_def], List.sum_ofFn]
            apply Finset.sum_congr rfl
            intro direction _
            exact directionWord_central_data (A := A) r t digits direction
              |>.2 pattern hpattern

private theorem multiScaleWord_cutoff_injective
    [Fintype A] [LinearOrder A] (r t : ℕ) (hr : 2 ≤ r) :
    Function.Injective (fun digits : DigitArray (A := A) r t ↦
      cutoffMagnus r (multiScaleWord (A := A) r t digits)) := by
  classical
  intro left right hequal
  let vectors := fun direction : Fin (actualLyndonCount (A := A) r) ↦
    actualLeadingDifference r (selectedDirection (A := A) r direction)
  let coefficient := fun direction : Fin (actualLyndonCount (A := A) r) ↦
    (digitValue (A := A) r t left direction : ℚ) -
      (digitValue (A := A) r t right direction : ℚ)
  have hrelation : ∑ direction, coefficient direction • vectors direction = 0 := by
    ext word
    by_cases hle : FreeMonoid.length word ≤ r
    · rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
          MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_zero,
          Finsupp.zero_apply]
        apply Finset.sum_eq_zero
        intro direction _
        have hlower := literalPowerSubstitution_actual_positivePair
          (A := A) 1 r (selectedDirection (A := A) r direction)
          |>.2.2.2.2.1 (FreeMonoid.toList word) (by
            simpa [FreeMonoid.length] using hlt)
        let index := selectedDirection (A := A) r direction
        let bounded : CutoffWord A r := ⟨word, hle⟩
        have hactual : (actualLeadingDifference r index).coeff bounded.1 =
            (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
                (FreeMonoid.toList bounded.1) (positivePairWords r index).1 : ℚ) -
              (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
                (FreeMonoid.toList bounded.1) (positivePairWords r index).2 : ℚ) := by
          have hcoeffAt : (actualLeadingDifference r index).coeff bounded.1 =
              (cutoffMagnus r (positivePairWords r index).1 -
                cutoffMagnus r (positivePairWords r index).2) bounded := by
            simp [actualLeadingDifference, cutoffRestriction, cutoffLift,
              Finsupp.mapDomain_apply Subtype.val_injective]
          rw [hcoeffAt]
          simpa [cutoffMagnus, cutoffRestriction] using
            (full_positivePair_coefficient_checkpoint r index).2 bounded
        have hzero : (vectors direction).coeff word = 0 := by
          rw [hactual]
          apply sub_eq_zero.mpr
          exact_mod_cast (by simpa [literalPowerWord] using hlower)
        simp [hzero]
      · have hlength : (FreeMonoid.toList word).length = r := by
          simpa [FreeMonoid.length] using heq
        have hleft := multiScaleWord_central_data (A := A) r t left
          |>.2 (FreeMonoid.toList word) hlength
        have hright := multiScaleWord_central_data (A := A) r t right
          |>.2 (FreeMonoid.toList word) hlength
        have hcut := congrFun hequal ⟨word, hle⟩
        have hcoeff :
            (rationalMagnus (multiScaleWord (A := A) r t left)).coeff word =
              (rationalMagnus (multiScaleWord (A := A) r t right)).coeff word := by
          simpa [cutoffMagnus, cutoffRestriction, rationalMagnus] using hcut
        simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
          MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_zero,
          Finsupp.zero_apply]
        change ∑ direction, coefficient direction * (vectors direction).coeff word = 0
        calc
          _ = (∑ direction,
                (digitValue (A := A) r t left direction : ℚ) *
                  (vectors direction).coeff word) -
              (∑ direction,
                (digitValue (A := A) r t right direction : ℚ) *
                  (vectors direction).coeff word) := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro direction _
                simp [coefficient]
                ring
          _ = degreeDifference (FreeMonoid.toList word)
                (multiScaleWord (A := A) r t left,
                  referenceWord (A := A) r t) -
              degreeDifference (FreeMonoid.toList word)
                (multiScaleWord (A := A) r t right,
                  referenceWord (A := A) r t) := by
                have hleft' : degreeDifference (FreeMonoid.toList word)
                    (multiScaleWord (A := A) r t left,
                      referenceWord (A := A) r t) =
                    ∑ direction,
                      (digitValue (A := A) r t left direction : ℚ) *
                        (vectors direction).coeff word := by
                  simpa [vectors, FreeMonoid.ofList_toList] using hleft
                have hright' : degreeDifference (FreeMonoid.toList word)
                    (multiScaleWord (A := A) r t right,
                      referenceWord (A := A) r t) =
                    ∑ direction,
                      (digitValue (A := A) r t right direction : ℚ) *
                        (vectors direction).coeff word := by
                  simpa [vectors, FreeMonoid.ofList_toList] using hright
                rw [hleft', hright']
          _ = 0 := by
                simp [degreeDifference, FreeMonoid.ofList_toList, hcoeff]
    · simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
        MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_zero,
        Finsupp.zero_apply]
      apply Finset.sum_eq_zero
      intro direction _
      have houtside : (vectors direction).coeff word = 0 := by
        simp only [vectors, actualLeadingDifference, cutoffLift,
          MonoidAlgebra.coeff_ofCoeff]
        apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨bounded, rfl⟩
        exact hle bounded.2
      simp [houtside]
  have hcoeffZero : ∀ direction, coefficient direction = 0 :=
    Fintype.linearIndependent_iff.mp
      (Classical.choose_spec (exists_actual_independent_directions (A := A) r))
      coefficient hrelation
  have hvalue : ∀ direction,
      digitValue (A := A) r t left direction =
        digitValue (A := A) r t right direction := by
    intro direction
    exact_mod_cast sub_eq_zero.mp (hcoeffZero direction)
  funext direction scale
  have hbase : 1 < digitBase r := by
    exact Nat.one_lt_pow (by omega) (by omega)
  have hlists := Nat.injOn_ofDigits hbase t
    (show (List.ofFn fun scale : Fin t ↦
        (left direction scale : ℕ)) ∈
        {digits | digits.length = t ∧
          ∀ digit ∈ digits, digit < digitBase r} by
      simp)
    (show (List.ofFn fun scale : Fin t ↦
        (right direction scale : ℕ)) ∈
        {digits | digits.length = t ∧
          ∀ digit ∈ digits, digit < digitBase r} by
      simp)
    (hvalue direction)
  have hfunctions :
      (fun scale : Fin t ↦ (left direction scale : ℕ)) =
        (fun scale : Fin t ↦ (right direction scale : ℕ)) :=
    List.ofFn_injective hlists
  exact Fin.ext (congrFun hfunctions scale)

/-- The actual recursive positive-pair family supplies a full multi-scale
central digit system: its selected directions are independent, every digit
word has the same lower cutoff and exact length, and the cutoff images are
injective with the expected finite cardinality. -/
theorem actual_positivePair_multiScale_central_digits
    [Fintype A] [LinearOrder A] (r t : ℕ) (hr : 2 ≤ r) :
    LinearIndependent ℚ
        (fun direction : Fin (actualLyndonCount (A := A) r) ↦
          actualLeadingDifference r
            (selectedDirection (A := A) r direction)) ∧
    (∀ direction : Fin (actualLyndonCount (A := A) r),
      (positivePairWords r
          (selectedDirection (A := A) r direction)).1 ≠ [] ∧
      (positivePairWords r
          (selectedDirection (A := A) r direction)).2 ≠ [] ∧
      (positivePairWords r
          (selectedDirection (A := A) r direction)).1.length =
        (positivePairWords r
          (selectedDirection (A := A) r direction)).2.length) ∧
    (∀ (digits : DigitArray (A := A) r t) (pattern : List A),
      pattern.length < r →
      D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          pattern (multiScaleWord (A := A) r t digits) =
        D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          pattern (referenceWord (A := A) r t)) ∧
    (∀ (digits : DigitArray (A := A) r t) (pattern : List A),
      pattern.length = r →
      (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          pattern (multiScaleWord (A := A) r t digits) : ℚ) -
        (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          pattern (referenceWord (A := A) r t) : ℚ) =
        ∑ direction : Fin (actualLyndonCount (A := A) r),
          (digitValue (A := A) r t digits direction : ℚ) *
            (actualLeadingDifference r
              (selectedDirection (A := A) r direction)).coeff
                (FreeMonoid.ofList pattern)) ∧
    Function.Injective (fun digits : DigitArray (A := A) r t ↦
      cutoffMagnus r (multiScaleWord (A := A) r t digits)) ∧
    Fintype.card (DigitArray (A := A) r t) =
      digitBase r ^ (t * actualLyndonCount (A := A) r) ∧
    ∀ digits : DigitArray (A := A) r t,
      (multiScaleWord (A := A) r t digits).length =
        baseLength (A := A) r * (2 ^ t - 1) := by
  classical
  refine ⟨Classical.choose_spec (exists_actual_independent_directions (A := A) r),
    ?_, ?_, ?_,
    multiScaleWord_cutoff_injective (A := A) r t hr, ?_, ?_⟩
  · intro direction
    exact (full_positivePair_coefficient_checkpoint r
      (selectedDirection (A := A) r direction)).1 hr
  · intro digits pattern hpattern
    have h := (multiScaleWord_central_data (A := A) r t digits).1
      pattern hpattern
    have hq :
        (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          pattern (multiScaleWord (A := A) r t digits) : ℚ) =
        (D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount
          pattern (referenceWord (A := A) r t) : ℚ) := by
      simpa [rationalMagnus, toRationalWordPolynomial,
        magnusPolynomial_coeff_scatteredCount] using h
    exact_mod_cast hq
  · intro digits pattern hpattern
    have h := (multiScaleWord_central_data (A := A) r t digits).2
      pattern hpattern
    simpa [degreeDifference, rationalMagnus, toRationalWordPolynomial,
      magnusPolynomial_coeff_scatteredCount] using h
  · simp [DigitArray, pow_mul]
  · have digitBlock_length
        (direction : Fin (actualLyndonCount (A := A) r)) (scale : Fin t)
        (digit : Fin (digitBase r)) :
        (digitBlock (A := A) r direction scale digit).length =
          (digitBase r - 1) *
            (positivePairWords r
              (selectedDirection (A := A) r direction)).1.length *
                2 ^ (scale : ℕ) := by
      let pair := positivePairWords r (selectedDirection (A := A) r direction)
      have hpair := (full_positivePair_coefficient_checkpoint r
        (selectedDirection (A := A) r direction)).1 hr
      have hdigit : (digit : ℕ) ≤ digitBase r - 1 := by omega
      have hrepeated (n : ℕ) (word : List A) :
          (repeatedWord n word).length = n * word.length := by
        simp [repeatedWord]
      have hpower (m : ℕ) (word : List A) :
          (literalPowerWord m word).length = word.length * m := by
        induction word with
        | nil => simp [literalPowerWord]
        | cons a word ih => simp [literalPowerWord, Nat.add_mul, Nat.add_comm]
      simp only [digitBlock, List.length_append, hrepeated, hpower]
      rw [← hpair.2.2]
      calc
        (digit : ℕ) * (pair.1.length * 2 ^ (scale : ℕ)) +
            (digitBase r - 1 - (digit : ℕ)) *
              (pair.1.length * 2 ^ (scale : ℕ)) =
          ((digit : ℕ) + (digitBase r - 1 - (digit : ℕ))) *
            (pair.1.length * 2 ^ (scale : ℕ)) := (Nat.add_mul _ _ _).symm
        _ = (digitBase r - 1) * pair.1.length * 2 ^ (scale : ℕ) := by
          rw [Nat.add_sub_of_le hdigit, Nat.mul_assoc]
    have multiScaleWord_length (digits : DigitArray (A := A) r t) :
        (multiScaleWord (A := A) r t digits).length =
          baseLength (A := A) r * (2 ^ t - 1) := by
      simp only [multiScaleWord, List.length_flatten, List.map_ofFn,
        List.sum_ofFn, Function.comp_apply, digitBlock_length]
      have hgeom : ∑ scale : Fin t, 2 ^ (scale : ℕ) = 2 ^ t - 1 := by
        rw [Fin.sum_univ_eq_sum_range]
        simpa using Nat.geomSum_eq (m := 2) (by omega) t
      simp_rw [← Finset.mul_sum, hgeom]
      rw [← Finset.sum_mul]
      unfold baseLength
      rw [Finset.mul_sum]
    exact multiScaleWord_length


end D5.S1.Words.Complexity.PositivePairCentralDigits
