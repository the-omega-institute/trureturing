/- GID: D5/S0/Computability/PresburgerPatternGrowth
   generality: G
   mirror-B: D5/B/S0/Computability/PresburgerPatternGrowth
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Boolean combinations of separated integer atoms have polynomial trace growth. -/

import Mathlib.Data.Finset.NAry
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum

/-!
Finite counting for separated Presburger atoms. The source carrier is arbitrary;
no source finiteness, definability, injectivity, or inhabitance is required.
Boolean products are upper bounds: they do not assert compatible witnesses.

`Growth` records a derivation from
actual separated atoms rather than assuming a trace bound. Its constructors
match the constant/atom/and/or/not steps of a quantifier-free formula. The
result concerns finite traces of these derivations.

-/

set_option autoImplicit false

namespace PresburgerPatternGrowth

universe u v w

variable {X : Type u} {Y : Type v} {I : Type w} [Fintype I]

/-- The distinct Boolean sample patterns witnessed by one common source. -/
noncomputable def traces (f : X → I → Bool) : Finset (I → Bool) := by
  classical
  exact Finset.univ.filter (fun p => ∃ x, f x = p)

theorem mem_traces (f : X → I → Bool) (p : I → Bool) :
    p ∈ traces f ↔ ∃ x, f x = p := by
  classical
  simp [traces]

private noncomputable def trueSet (p : I → Bool) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => p i = true)

private theorem trueSet_injective : Function.Injective (trueSet (I := I)) := by
  classical
  intro p q h
  funext i
  have hi : (p i = true) ↔ (q i = true) := by
    simpa [trueSet] using Finset.ext_iff.mp h i
  cases hp : p i <;> cases hq : q i <;> simp_all

/-- A separated threshold has at most one pattern for each possible number of
true sample coordinates, including the empty sample and tied thresholds. -/
theorem trace_card_threshold (A : X → Int) (B : I → Int) :
    (traces (fun x i => decide (A x ≤ B i))).card ≤ Fintype.card I + 1 := by
  classical
  have hc := Finset.card_le_card_of_injOn
    (fun p : I → Bool => (trueSet p).card)
    (s := traces (fun x i => decide (A x ≤ B i)))
    (t := Finset.range (Fintype.card I + 1))
  rw [Finset.card_range] at hc
  apply hc
  · intro p _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (trueSet p).card_le_univ)
  · intro p hp q hq hcard
    obtain ⟨x, rfl⟩ := (mem_traces _ _).mp hp
    obtain ⟨y, rfl⟩ := (mem_traces _ _).mp hq
    apply trueSet_injective
    rcases le_total (A x) (A y) with hxy | hyx
    · symm
      apply Finset.eq_of_subset_of_card_le _ hcard.le
      intro i hi
      have hy : A y ≤ B i := by simpa [trueSet] using hi
      simpa [trueSet] using le_trans hxy hy
    · apply Finset.eq_of_subset_of_card_le _ hcard.ge
      intro i hi
      have hx : A x ≤ B i := by simpa [trueSet] using hi
      simpa [trueSet] using le_trans hyx hx

theorem trace_card_factor {K : Type*} [Fintype K]
    (f : X → I → Bool) (code : X → K) (decode : K → I → Bool)
    (h : ∀ x, f x = decode (code x)) :
    (traces f).card ≤ Fintype.card K := by
  classical
  calc
    (traces f).card ≤ (Finset.univ.image decode).card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨x, rfl⟩ := (mem_traces _ _).mp hp
      exact Finset.mem_image.mpr ⟨code x, Finset.mem_univ _, (h x).symm⟩
    _ ≤ Fintype.card K := Finset.card_image_le.trans_eq Finset.card_univ

/-- Fixed positive-modulus divisibility is determined by the source residue.
Neither the sample values nor the source image need be bounded. -/
theorem trace_card_dvd (d : Nat) (hd : 0 < d) (A : X → Int) (B : I → Int) :
    (traces (fun x i => decide ((d : Int) ∣ A x + B i))).card ≤ d := by
  classical
  let code : X → Fin d := fun x =>
    ⟨(A x % (d : Int)).toNat,
      (Int.toNat_lt_of_ne_zero (Nat.ne_of_gt hd)).mpr
        (Int.emod_lt_of_pos _ (by exact_mod_cast hd))⟩
  have h := trace_card_factor (fun x i => decide ((d : Int) ∣ A x + B i))
    code (fun r i => decide ((d : Int) ∣ (r.val : Int) + B i)) ?_
  · simpa using h
  · intro x
    funext i
    have hr : ((code x).val : Int) = A x % (d : Int) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast Nat.ne_of_gt hd))
    simp only [hr, Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.emod_emod]

/-- Applying any pointwise unary Boolean operation cannot increase trace count. -/
theorem trace_card_unary (op : Bool → Bool) (f : X → I → Bool) :
    (traces (fun x i => op (f x i))).card ≤ (traces f).card := by
  classical
  calc
    (traces (fun x i => op (f x i))).card ≤
        ((traces f).image (fun p i => op (p i))).card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨x, rfl⟩ := (mem_traces _ _).mp hp
      exact Finset.mem_image.mpr ⟨f x, (mem_traces _ _).mpr ⟨x, rfl⟩, rfl⟩
    _ ≤ (traces f).card := Finset.card_image_le

/-- Negated fixed-modulus divisibility has the same residue upper bound. -/
theorem trace_card_ndvd (d : Nat) (hd : 0 < d) (A : X → Int) (B : I → Int) :
    (traces (fun x i => decide (¬ (d : Int) ∣ A x + B i))).card ≤ d := by
  have h := (trace_card_unary Bool.not
    (fun x i => decide ((d : Int) ∣ A x + B i))).trans (trace_card_dvd d hd A B)
  simpa only [decide_not] using h

/-- Intersection, union, and any other pointwise binary Boolean operation
have a product upper bound, with no independent-realizability assumption. -/
theorem trace_card_binary (op : Bool → Bool → Bool) (f g : X → I → Bool) :
    (traces (fun x i => op (f x i) (g x i))).card ≤
      (traces f).card * (traces g).card := by
  classical
  calc
    (traces (fun x i => op (f x i) (g x i))).card ≤
        (Finset.image₂ (fun p q i => op (p i) (q i)) (traces f) (traces g)).card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨x, rfl⟩ := (mem_traces _ _).mp hp
      exact Finset.mem_image₂.mpr
        ⟨f x, (mem_traces _ _).mpr ⟨x, rfl⟩,
          g x, (mem_traces _ _).mpr ⟨x, rfl⟩, rfl⟩
    _ ≤ (traces f).card * (traces g).card := Finset.card_image₂_le _ _ _

private theorem trace_card_constant (b : Bool) :
    (traces (fun (_ : X) (_ : I) => b)).card ≤ 1 := by
  simpa using trace_card_factor (fun (_ : X) (_ : I) => b)
    (fun _ => ()) (fun (_ : Unit) _ => b) (fun _ => rfl)

/-- An exact semantic derivation from separated atoms. C is the product of
fixed positive moduli; s counts threshold occurrences. Unary and binary
operations are unrestricted Boolean functions, covering QF not/and/or. -/
inductive Growth : (X → Y → Bool) → Nat → Nat → Prop where
  | constant (b : Bool) : Growth (fun _ _ => b) 1 0
  | threshold (A : X → Int) (B : Y → Int) :
      Growth (fun x y => decide (A x ≤ B y)) 1 1
  | dvd (d : Nat) (hd : 0 < d) (A : X → Int) (B : Y → Int) :
      Growth (fun x y => decide ((d : Int) ∣ A x + B y)) d 0
  | ndvd (d : Nat) (hd : 0 < d) (A : X → Int) (B : Y → Int) :
      Growth (fun x y => decide (¬ (d : Int) ∣ A x + B y)) d 0
  | unary {f : X → Y → Bool} {C s : Nat} (op : Bool → Bool)
      (hf : Growth f C s) : Growth (fun x y => op (f x y)) C s
  | binary {f g : X → Y → Bool} {C D s t : Nat} (op : Bool → Bool → Bool)
      (hf : Growth f C s) (hg : Growth g D t) :
      Growth (fun x y => op (f x y) (g x y)) (C * D) (s + t)

/-- Every finite separated-atom derivation supplies a fixed positive polynomial
bound for every finite sample map, permitting repetitions and empty carriers. -/
theorem polynomial_trace_bound {f : X → Y → Bool} {C s : Nat}
    (h : Growth f C s) :
    0 < C ∧ ∀ {I : Type w} [Fintype I] (sample : I → Y),
      (traces (fun x i => f x (sample i))).card ≤ C * (Fintype.card I + 1) ^ s := by
  induction h with
  | constant b =>
      refine ⟨by decide, ?_⟩
      intro I _ sample
      simpa using trace_card_constant (X := X) (I := I) b
  | threshold A B =>
      refine ⟨by decide, ?_⟩
      intro I _ sample
      simpa using trace_card_threshold A (fun i => B (sample i))
  | dvd d hd A B =>
      refine ⟨hd, ?_⟩
      intro I _ sample
      simpa using trace_card_dvd d hd A (fun i => B (sample i))
  | ndvd d hd A B =>
      refine ⟨hd, ?_⟩
      intro I _ sample
      simpa using trace_card_ndvd d hd A (fun i => B (sample i))
  | unary op _ ih =>
      refine ⟨ih.1, ?_⟩
      intro I _ sample
      exact (trace_card_unary op _).trans (ih.2 sample)
  | @binary f g C D s t op _ _ ihf ihg =>
      refine ⟨Nat.mul_pos ihf.1 ihg.1, ?_⟩
      intro I _ sample
      calc
        _ ≤ (traces (fun x i => f x (sample i))).card *
              (traces (fun x i => g x (sample i))).card := trace_card_binary op _ _
        _ ≤ (C * (Fintype.card I + 1) ^ s) *
              (D * (Fintype.card I + 1) ^ t) := Nat.mul_le_mul (ihf.2 sample) (ihg.2 sample)
        _ = (C * D) * (Fintype.card I + 1) ^ (s + t) := by
          rw [pow_add]
          ac_rfl

#print axioms mem_traces
#print axioms trueSet_injective
#print axioms trace_card_factor
#print axioms trace_card_constant
#print axioms trace_card_threshold
#print axioms trace_card_dvd
#print axioms trace_card_unary
#print axioms trace_card_ndvd
#print axioms trace_card_binary
#print axioms polynomial_trace_bound

end PresburgerPatternGrowth
