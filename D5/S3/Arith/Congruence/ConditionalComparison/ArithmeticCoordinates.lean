/- GID: D5/S3/Arith/Congruence/ConditionalComparison/ArithmeticCoordinates
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source excerpts: ordinary odd-cover arithmetic coordinates and pure prefixes. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/{ArithmeticReduction,
Rank8Arithmetic,Rank8Cylinders,ThreePrime/CylinderModel}.lean, general
arithmetic/pure-prefix and coordinate-marginal sections.
Archive, full license, exact excerpt map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proof bodies are retained. Unused six-block,
seven-block and three-support applications are not imported. These excerpts
are upstream reuse, not new mathematical contributions. Utility is none:
symbolic finite arithmetic and prefix geometry, with no numerical certificate.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainTrees
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic

namespace Erdos7.FiniteLaw

theorem piLaw_prob_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (μ : ∀ i, FiniteLaw (α i))
    (j : ι) (A : α j → Prop) [DecidablePred A] :
    (piLaw μ).prob (fun x ↦ A (x j)) = (μ j).prob A := by
  classical
  let E := fun i (y : α i) ↦ if h : i = j then decide (A (h ▸ y)) else true
  have he : (piLaw μ).prob (fun x ↦ A (x j)) =
      (piLaw μ).prob (fun x ↦ ∀ i, E i (x i) = true) := by
    apply prob_congr
    intro x
    constructor
    · intro h i
      by_cases hi : i = j
      · subst i; simpa only [E, dif_pos rfl, decide_eq_true_eq] using h
      · simp [E, hi]
    · intro h
      simpa only [E, dif_pos rfl, decide_eq_true_eq] using h j
  rw [he, piLaw_prob_forall_bool]
  rw [Finset.prod_eq_single j]
  · simp [E]
  · intro i _ hi
    simp [E, hi]
  · intro h
    exact (h (Finset.mem_univ j)).elim

end Erdos7.FiniteLaw

namespace Erdos7

def embeddedWordValue {q a : ℕ} (p : ℕ) (w : Word q a) : ℕ :=
  Nat.ofDigits p (List.ofFn fun i ↦ (w i : ℕ))

theorem embeddedWordValue_prefix_eq {q a p d : ℕ}
    (hp : 1 < p) (hqp : q ≤ p) (hda : d ≤ a)
    (u v : Word q a)
    (hmod : embeddedWordValue p u ≡ embeddedWordValue p v [MOD p ^ d]) :
    HasPrefix u (Fin.take d hda v) hda := by
  let Lu : List ℕ := List.ofFn fun i ↦ (u i : ℕ)
  let Lv : List ℕ := List.ofFn fun i ↦ (v i : ℕ)
  have huDigits : ∀ z ∈ Lu, z < p := by
    intro z hz
    simp only [Lu, List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    exact (u i).isLt.trans_le hqp
  have hvDigits : ∀ z ∈ Lv, z < p := by
    intro z hz
    simp only [Lv, List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    exact (v i).isLt.trans_le hqp
  have hvalues : Nat.ofDigits p (Lu.take d) = Nat.ofDigits p (Lv.take d) := by
    unfold Nat.ModEq embeddedWordValue at hmod
    rw [Nat.ofDigits_mod_pow_eq_ofDigits_take d (by omega) Lu huDigits,
      Nat.ofDigits_mod_pow_eq_ofDigits_take d (by omega) Lv hvDigits] at hmod
    exact hmod
  have htake : Lu.take d = Lv.take d := by
    apply Nat.ofDigits_inj_of_len_eq hp
    · simp [Lu, Lv, hda]
    · intro z hz
      exact huDigits z (List.mem_of_mem_take hz)
    · intro z hz
      exact hvDigits z (List.mem_of_mem_take hz)
    · exact hvalues
  have hfunctions :
      (fun i : Fin d ↦ (u ⟨i, Nat.lt_of_lt_of_le i.isLt hda⟩ : ℕ)) =
      (fun i : Fin d ↦ (v ⟨i, Nat.lt_of_lt_of_le i.isLt hda⟩ : ℕ)) := by
    apply List.ofFn_injective
    change List.ofFn (Fin.take d hda (fun i ↦ (u i : ℕ))) =
      List.ofFn (Fin.take d hda (fun i ↦ (v i : ℕ)))
    rw [Fin.ofFn_take_eq_take_ofFn hda,
      Fin.ofFn_take_eq_take_ofFn hda]
    exact htake
  intro i
  apply Fin.ext
  exact congrFun hfunctions i

structure PrimePowerCover (r L : ℕ) where
  prime : Fin r → ℕ
  height : Fin r → ℕ
  depth : Fin L → (j : Fin r) → Fin (height j + 1)
  residue : Fin L → ℕ
  prime_prime : ∀ j, Nat.Prime (prime j)
  prime_injective : Function.Injective prime
  height_pos : ∀ j, 0 < height j
  depth_injective : Function.Injective depth
  nontrivial : ∀ k, ∃ j, (depth k j : ℕ) ≠ 0
  covers : ∀ z : ℕ, ∃ k : Fin L,
    z ≡ residue k [MOD ∏ j, prime j ^ (depth k j : ℕ)]

namespace PrimePowerCover

variable {r L : ℕ} (A : PrimePowerCover r L)

def crtModulus (j : Fin r) : ℕ := A.prime j ^ A.height j

theorem crtModulus_ne_zero (j : Fin r) : A.crtModulus j ≠ 0 :=
  pow_ne_zero _ (A.prime_prime j).ne_zero

theorem crtModulus_pairwise :
  Set.Pairwise (Finset.univ : Finset (Fin r))
      (fun i j ↦ Nat.Coprime (A.crtModulus i) (A.crtModulus j)) := by
  intro i _ j _ hij
  exact Nat.coprime_pow_primes _ _ (A.prime_prime i) (A.prime_prime j)
    (fun h ↦ hij (A.prime_injective h))

def modulus (k : Fin L) : ℕ :=
  ∏ j, A.prime j ^ (A.depth k j : ℕ)

theorem primePowDepth_dvd_modulus (k : Fin L) (j : Fin r) :
    A.prime j ^ (A.depth k j : ℕ) ∣ A.modulus k := by
  exact Finset.dvd_prod_of_mem (fun i ↦
    A.prime i ^ (A.depth k i : ℕ)) (Finset.mem_univ j)

theorem covers_modulus (z : ℕ) :
    ∃ k : Fin L, z ≡ A.residue k [MOD A.modulus k] := by
  simpa [modulus] using A.covers z

noncomputable def actualCRT (x : Cylinder.Point r A.prime A.height) : ℕ :=
  (Nat.chineseRemainderOfFinset
    (fun j ↦ embeddedWordValue (A.prime j) (x j)) A.crtModulus Finset.univ
    (fun j _ ↦ A.crtModulus_ne_zero j) A.crtModulus_pairwise).val

theorem actualCRT_modEq (x : Cylinder.Point r A.prime A.height) (j : Fin r) :
    A.actualCRT x ≡ embeddedWordValue (A.prime j) (x j)
      [MOD A.prime j ^ A.height j] :=
  (Nat.chineseRemainderOfFinset
    (fun j ↦ embeddedWordValue (A.prime j) (x j)) A.crtModulus Finset.univ
    (fun j _ ↦ A.crtModulus_ne_zero j) A.crtModulus_pairwise).property
      j (Finset.mem_univ j)

def ActualSurvives (k : Fin L) : Prop :=
  ∃ x : Cylinder.Point r A.prime A.height,
    A.actualCRT x ≡ A.residue k [MOD A.modulus k]

abbrev ActualSurvivor := {k : Fin L // A.ActualSurvives k}

noncomputable def actualWitness (k : A.ActualSurvivor) :
    Cylinder.Point r A.prime A.height := Classical.choose k.property

theorem actualWitness_modEq (k : A.ActualSurvivor) :
    A.actualCRT (A.actualWitness k) ≡ A.residue k.val [MOD A.modulus k.val] :=
  Classical.choose_spec k.property

noncomputable def actualCylinder (k : A.ActualSurvivor) : Cylinder r A.prime A.height where
  depth := A.depth k.val
  digits j := Fin.take (A.depth k.val j).val (indexedDepthLe (A.depth k.val j))
    (A.actualWitness k j)

theorem actualCylinder_contains (k : A.ActualSurvivor)
    (x : Cylinder.Point r A.prime A.height)
    (hx : A.actualCRT x ≡ A.residue k.val [MOD A.modulus k.val]) :
    (A.actualCylinder k).Contains x := by
  intro j
  let d := (A.depth k.val j).val
  have hd : d ≤ A.height j := indexedDepthLe (A.depth k.val j)
  have hxy := hx.trans (A.actualWitness_modEq k).symm
  have hsmall := hxy.of_dvd (A.primePowDepth_dvd_modulus k.val j)
  have hp : A.prime j ^ d ∣ A.prime j ^ A.height j := pow_dvd_pow _ hd
  have hblocks := ((A.actualCRT_modEq x j).of_dvd hp).symm.trans
    (hsmall.trans ((A.actualCRT_modEq (A.actualWitness k) j).of_dvd hp))
  exact embeddedWordValue_prefix_eq (A.prime_prime j).one_lt le_rfl hd
    (x j) (A.actualWitness k j) hblocks

theorem actualCylinder_depthInjective : Cylinder.DepthInjective A.actualCylinder := by
  intro k l h
  apply Subtype.ext
  exact A.depth_injective h

theorem actualCylinder_nontrivial (k : A.ActualSurvivor) :
    (A.actualCylinder k).Nontrivial := A.nontrivial k.val

theorem actualCylinder_covers : Cylinder.Covers A.actualCylinder := by
  intro x
  obtain ⟨k, hk⟩ := A.covers_modulus (A.actualCRT x)
  let s : A.ActualSurvivor := ⟨k, x, hk⟩
  exact ⟨s, A.actualCylinder_contains s x hk⟩

end PrimePowerCover

theorem finset_prod_odd_nat {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ)
    (hodd : ∀ i ∈ s, Odd (f i)) : Odd (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hodd a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi ↦ hodd i (Finset.mem_insert_of_mem hi)))

/-- An ordinary finite covering system with the hypotheses of the theorem. -/
structure OddDistinctCoveringSystem (L : ℕ) where
  residue : Fin L → ℕ
  modulus : Fin L → ℕ
  covers : ∀ z : ℕ, ∃ k : Fin L, z ≡ residue k [MOD modulus k]
  modulus_one_lt : ∀ k, 1 < modulus k
  modulus_odd : ∀ k, Odd (modulus k)
  modulus_injective : Function.Injective modulus

namespace OddDistinctCoveringSystem

variable {L : ℕ} (S : OddDistinctCoveringSystem L)

def commonModulus : ℕ := Finset.univ.lcm S.modulus

theorem modulus_ne_zero (k : Fin L) : S.modulus k ≠ 0 := by
  exact Nat.ne_of_gt (lt_trans Nat.zero_lt_one (S.modulus_one_lt k))

theorem commonModulus_ne_zero : S.commonModulus ≠ 0 := by
  rw [commonModulus, Finset.lcm_ne_zero_iff]
  intro k _
  exact S.modulus_ne_zero k

theorem modulus_dvd_commonModulus (k : Fin L) :
    S.modulus k ∣ S.commonModulus := by
  exact Finset.dvd_lcm (Finset.mem_univ k)

theorem commonModulus_odd : Odd S.commonModulus := by
  have hprodOdd : Odd (∏ k : Fin L, S.modulus k) :=
    finset_prod_odd_nat Finset.univ S.modulus
      (fun k _ ↦ S.modulus_odd k)
  apply hprodOdd.of_dvd_nat
  apply Finset.lcm_dvd
  intro k hk
  exact Finset.dvd_prod_of_mem S.modulus hk

def supportSize : ℕ := S.commonModulus.primeFactors.card

def orderedPrime : Fin S.supportSize → ℕ :=
  S.commonModulus.primeFactors.orderEmbOfFin rfl

theorem orderedPrime_mem (j : Fin S.supportSize) :
    S.orderedPrime j ∈ S.commonModulus.primeFactors :=
  Finset.orderEmbOfFin_mem _ _ _

theorem orderedPrime_prime (j : Fin S.supportSize) :
    Nat.Prime (S.orderedPrime j) :=
  Nat.prime_of_mem_primeFactors (S.orderedPrime_mem j)

theorem orderedPrime_strictMono : StrictMono S.orderedPrime :=
  (S.commonModulus.primeFactors.orderEmbOfFin rfl).strictMono

theorem orderedPrime_injective : Function.Injective S.orderedPrime :=
  S.orderedPrime_strictMono.injective

theorem orderedPrime_ne_two (j : Fin S.supportSize) :
    S.orderedPrime j ≠ 2 := by
  exact S.commonModulus_odd.ne_two_of_dvd_nat
    (Nat.dvd_of_mem_primeFactors (S.orderedPrime_mem j))

def primeHeight (j : Fin S.supportSize) : ℕ :=
  S.commonModulus.factorization (S.orderedPrime j)

theorem primeHeight_pos (j : Fin S.supportSize) :
    0 < S.primeHeight j := by
  exact (S.orderedPrime_prime j).factorization_pos_of_dvd
    S.commonModulus_ne_zero
    (Nat.dvd_of_mem_primeFactors (S.orderedPrime_mem j))

def primeDepth (k : Fin L) (j : Fin S.supportSize) :
    Fin (S.primeHeight j + 1) :=
  ⟨S.modulus k |>.factorization (S.orderedPrime j), by
    apply Nat.lt_succ_of_le
    exact ((Nat.factorization_le_iff_dvd (S.modulus_ne_zero k)
      S.commonModulus_ne_zero).2 (S.modulus_dvd_commonModulus k))
      (S.orderedPrime j)⟩

@[simp] theorem primeDepth_val (k : Fin L) (j : Fin S.supportSize) :
    (S.primeDepth k j : ℕ) =
      (S.modulus k).factorization (S.orderedPrime j) := rfl

theorem product_primeDepth_eq_modulus (k : Fin L) :
    (∏ j : Fin S.supportSize,
      S.orderedPrime j ^ (S.primeDepth k j : ℕ)) = S.modulus k := by
  classical
  let P := S.commonModulus.primeFactors
  have henum :
      (∏ j : Fin S.supportSize,
        S.orderedPrime j ^ (S.modulus k).factorization (S.orderedPrime j)) =
      ∏ p ∈ P, p ^ (S.modulus k).factorization p := by
    have hmap := Finset.prod_map
      (Finset.univ : Finset (Fin S.commonModulus.primeFactors.card))
      (S.commonModulus.primeFactors.orderEmbOfFin rfl).toEmbedding
      (fun p ↦ p ^ (S.modulus k).factorization p)
    rw [Finset.map_orderEmbOfFin_univ] at hmap
    convert hmap.symm using 1
    apply Finset.prod_congr rfl
    intro i _
    congr 3
  simp only [primeDepth_val]
  rw [henum]
  have hfilter :
      {p ∈ P | p ∣ S.modulus k} = (S.modulus k).primeFactors := by
    exact Nat.primeFactors_filter_dvd_of_dvd S.commonModulus_ne_zero
      (S.modulus_dvd_commonModulus k)
  calc
    (∏ p ∈ P, p ^ (S.modulus k).factorization p) =
        ∏ p ∈ {p ∈ P | p ∣ S.modulus k},
          p ^ (S.modulus k).factorization p := by
      symm
      apply Finset.prod_subset (Finset.filter_subset _ _)
      intro p hpP hpnot
      have hnotdvd : ¬p ∣ S.modulus k := by
        simpa only [Finset.mem_filter, hpP, true_and] using hpnot
      simp [Nat.factorization_eq_zero_of_not_dvd hnotdvd]
    _ = ∏ p ∈ (S.modulus k).primeFactors,
          p ^ (S.modulus k).factorization p := by rw [hfilter]
    _ = (S.modulus k).factorization.prod (fun p e ↦ p ^ e) := by
      rw [Nat.prod_factorization_eq_prod_primeFactors]
    _ = S.modulus k := Nat.prod_factorization_pow_eq_self (S.modulus_ne_zero k)

theorem primeDepth_injective : Function.Injective S.primeDepth := by
  intro k l hdepth
  apply S.modulus_injective
  apply Nat.factorization_inj (S.modulus_ne_zero k) (S.modulus_ne_zero l)
  ext p
  by_cases hp : Nat.Prime p
  · by_cases hpd : p ∣ S.commonModulus
    · have hmem : p ∈ S.commonModulus.primeFactors :=
        hp.mem_primeFactors hpd S.commonModulus_ne_zero
      have hrange : p ∈ Set.range S.orderedPrime := by
        change p ∈ Set.range
          (S.commonModulus.primeFactors.orderEmbOfFin rfl)
        rw [Finset.range_orderEmbOfFin]
        exact hmem
      obtain ⟨j, rfl⟩ := hrange
      have hv := congrFun hdepth j
      exact congrArg Fin.val hv
    · have hknot : ¬p ∣ S.modulus k := fun h ↦
        hpd (h.trans (S.modulus_dvd_commonModulus k))
      have hlnot : ¬p ∣ S.modulus l := fun h ↦
        hpd (h.trans (S.modulus_dvd_commonModulus l))
      rw [Nat.factorization_eq_zero_of_not_dvd hknot,
        Nat.factorization_eq_zero_of_not_dvd hlnot]
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp,
      Nat.factorization_eq_zero_of_not_prime _ hp]

theorem primeDepth_nontrivial (k : Fin L) :
    ∃ j, (S.primeDepth k j : ℕ) ≠ 0 := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (ne_of_gt (S.modulus_one_lt k))
  have hpcommon : p ∣ S.commonModulus :=
    hpd.trans (S.modulus_dvd_commonModulus k)
  have hmem : p ∈ S.commonModulus.primeFactors :=
    hp.mem_primeFactors hpcommon S.commonModulus_ne_zero
  have hrange : p ∈ Set.range S.orderedPrime := by
    change p ∈ Set.range
      (S.commonModulus.primeFactors.orderEmbOfFin rfl)
    rw [Finset.range_orderEmbOfFin]
    exact hmem
  obtain ⟨j, rfl⟩ := hrange
  exact ⟨j, (hp.factorization_pos_of_dvd (S.modulus_ne_zero k) hpd).ne'⟩

noncomputable def toPrimePowerCover : PrimePowerCover S.supportSize L where
  prime := S.orderedPrime
  height := S.primeHeight
  depth := S.primeDepth
  residue := S.residue
  prime_prime := S.orderedPrime_prime
  prime_injective := S.orderedPrime_injective
  height_pos := S.primeHeight_pos
  depth_injective := S.primeDepth_injective
  nontrivial := S.primeDepth_nontrivial
  covers := by
    intro z
    obtain ⟨k, hk⟩ := S.covers z
    refine ⟨k, ?_⟩
    rw [S.product_primeDepth_eq_modulus]
    exact hk

end OddDistinctCoveringSystem

end Erdos7

namespace Erdos7.CappedGain

section PurePrefixes
variable {κ : Type*} {r : ℕ} {arity height : Fin r → ℕ}
  (C : κ → Cylinder r arity height) (hpos : ∀ j, 0 < arity j)

def purePrefixAt (j : Fin r) (d : Fin (height j + 1))
    (k : κ) (hk : (C k).depth j = d) : Prefix (arity j) d.val :=
  fun i ↦ (C k).digits j ⟨i, by simpa [hk] using i.isLt⟩

def SuppliedPure (j : Fin r) (d : Fin (height j + 1)) (u : Prefix (arity j) d.val) : Prop :=
  d.val ≠ 0 ∧ ∃ k : κ, ∃ hk : (C k).depth j = d,
    (C k).Pure ∧ u = purePrefixAt C j d k hk

theorem suppliedPure_unique (hInj : Cylinder.DepthInjective C)
    (j : Fin r) (d : Fin (height j + 1)) {u v : Prefix (arity j) d.val}
    (hu : SuppliedPure C j d u) (hv : SuppliedPure C j d v) : u = v := by
  obtain ⟨hd, k, hk, hkPure, rfl⟩ := hu
  obtain ⟨_, l, hl, hlPure, rfl⟩ := hv
  have hkl : k = l := Cylinder.eq_of_pure_of_same_positive C hInj
    hkPure hlPure (by simpa [hk] using hd) (hk.trans hl.symm)
  subst l
  congr

noncomputable def forbidden (j : Fin r) : ForbiddenPrefixesOf (arity j) (height j) := by
  classical
  exact fun d ↦ if h : ∃ u, SuppliedPure C j d u then Classical.choose h
    else fun _ ↦ ⟨0, hpos j⟩

theorem forbidden_eq_digits (hInj : Cylinder.DepthInjective C)
    (k : κ) (hkPure : (C k).Pure) (j : Fin r) (hj : ((C k).depth j).val ≠ 0) :
    forbidden C hpos j ((C k).depth j) = (C k).digits j := by
  classical
  have hu : SuppliedPure C j ((C k).depth j) ((C k).digits j) :=
    ⟨hj, k, rfl, hkPure, rfl⟩
  have hex : ∃ u, SuppliedPure C j ((C k).depth j) u := ⟨_, hu⟩
  rw [forbidden, dif_pos hex]
  exact suppliedPure_unique C hInj j _ (Classical.choose_spec hex) hu

end PurePrefixes

end Erdos7.CappedGain
