/- GID: D5/S1/Words/KimberlingA288476Length
   generality: G
   mirror-B: D5/B/S1/Words/KimberlingA288476Length
   mirror-E: none(waiver:Pure theorem proof; no separate empirical evidence artifact)
   anchors: []
   utility: none
   digest: Native replacement-iterate lengths for Kimberling's OEIS A288476 conjecture. -/
import D5.S1.Words.RankOneMorphismIterationBoundDefs
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Logic.Function.Iterate

/-! The binary scanner is defined independently of the auxiliary ternary coding. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KimberlingA288476Length

open RankOneMorphismIterationBound (subst subst_nil subst_cons subst_append image
  image_zero image_succ image_one image_add)

/-- One original-input pass: false is 0 and true is 1. Emitted output is not rescanned. -/
def sourceScan : List Bool → List Bool
  | [] => []
  | false :: false :: v => [false, true, false, true] ++ sourceScan v
  | true :: v => [false, true, true] ++ sourceScan v
  | false :: v => false :: sourceScan v

/-- The source starts at 00, with the zeroth iterate included. -/
def sourceIter (n : ℕ) : List Bool := sourceScan^[n] [false, false]

/-- The independent integer recurrence, in ascending coefficient order. -/
def recurrence : LinearRecurrence ℤ := ⟨3, ![-2, 4, 1]⟩

/-- The OEIS sequence is defined from its recurrence and three initial values. -/
noncomputable def recurrenceSeq : ℕ → ℤ := recurrence.mkSol ![2, 4, 8]

private inductive Letter where
  | D | E | O

private def code : Letter → List Bool
  | .D => [false, false]
  | .E => [false, true]
  | .O => [true]

private def sigma : Letter → List Letter
  | .D => [.E, .E]
  | .E => [.D, .O, .O]
  | .O => [.E, .O]

private theorem scan_code_prefix (c : Letter) (v : List Bool) :
    sourceScan (code c ++ v) = subst code (sigma c) ++ sourceScan v := by
  cases c <;> simp [code, sigma, sourceScan, subst_cons, subst_nil]

private theorem scan_code_word (u : List Letter) :
    sourceScan (subst code u) = subst code (subst sigma u) := by
  have h := List.foldr_hom sourceScan (l := u) (init := [])
    (g₁ := fun c v => code c ++ v)
    (g₂ := fun c v => subst code (sigma c) ++ v)
    (fun c v => (scan_code_prefix c v).symm)
  simp only [List.foldr_append_eq_append, sourceScan, List.append_nil] at h
  change subst (fun c => subst code (sigma c)) u = sourceScan (subst code u) at h
  simpa only [subst, List.flatMap_assoc] using h.symm

private theorem image_iter (n : ℕ) (c : Letter) :
    image sigma n c = (subst sigma)^[n] [c] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [image_succ, Function.iterate_succ_apply', ih]

private theorem native_iterate_code (n : ℕ) :
    sourceIter n = subst code (image sigma n .D) := by
  have h : Function.Semiconj (subst code) (subst sigma) sourceScan :=
    fun u => (scan_code_word u).symm
  rw [image_iter]
  simpa only [sourceIter, subst_cons, subst_nil, code, List.append_nil] using
    (h.iterate_right n [Letter.D]).symm

private def codedLength (n : ℕ) (c : Letter) : ℤ :=
  (subst code (image sigma n c)).length

private theorem coded_step (n : ℕ) :
    codedLength (n + 1) .D = 2 * codedLength n .E ∧
    codedLength (n + 1) .E = codedLength n .D + 2 * codedLength n .O ∧
    codedLength (n + 1) .O = codedLength n .E + codedLength n .O := by
  simp only [codedLength, image_add sigma n 1, image_one, sigma,
    subst_cons, subst_nil, subst_append, List.append_nil, List.length_append, Nat.cast_add]
  constructor
  · omega
  constructor <;> first | omega | trivial

private theorem coded_recurrence (n : ℕ) :
    codedLength (n + 3) .D = codedLength (n + 2) .D +
      4 * codedLength (n + 1) .D - 2 * codedLength n .D := by
  have h0 := coded_step n
  have h1 := coded_step (n + 1)
  have h2 := coded_step (n + 2)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h0 h1 h2
  omega

private theorem native_solution : recurrence.IsSolution (fun n => ((sourceIter n).length : ℤ)) := by
  intro n
  change ((sourceIter (n + 3)).length : ℤ) =
    ∑ i : Fin 3, (![-2, 4, 1] : Fin 3 → ℤ) i * ((sourceIter (n + i)).length : ℤ)
  simp only [Fin.sum_univ_three]
  norm_num [Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons]
  simp only [native_iterate_code]
  change codedLength (n + 3) .D = -2 * codedLength n .D +
    4 * codedLength (n + 1) .D + codedLength (n + 2) .D
  have h := coded_recurrence n
  linarith

/-- Every native source-iterate length equals the independently specified OEIS recurrence. -/
theorem result (n : ℕ) : ((sourceIter n).length : ℤ) = recurrenceSeq n := by
  apply recurrence.eq_mk_of_is_sol_of_eq_init native_solution (init := ![2, 4, 8]) _ n
  change ∀ k : Fin 3, ((sourceIter k).length : ℤ) = (![2, 4, 8] : Fin 3 → ℤ) k
  intro k
  fin_cases k <;> norm_num [sourceIter, Function.iterate_succ_apply', sourceScan]

end D5.S1.Words.KimberlingA288476Length
