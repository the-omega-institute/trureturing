/- GID: D5/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/SahasrabudheEvenAdditiveComplexityMorphism
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Universal-input morphisms cannot have constant positive even additive complexity. -/

/-
result:
  proof_shape: content
  escape_witness: none
  admission_basis: open-problem-resolution (#22635; Proved)
Per-declaration classification (definitions carry no theorem proof_shape):
  UniversalInput: definition; consumers: claim, complementary_factor, imageWord_occurs, imageWord_sum_mem, result, same_length_sum; dependencies: WF
  IsMorphicImage: definition; consumers: claim, complementary_factor, imageWord_occurs, imageWord_sum_mem, result, same_length_sum; dependencies: none
  factorSum: definition; consumers: complementary_factor, cyclic_factor_sum, factorSum_add, factorSum_eq_list_sum, imageWord_sum_mem, sumSet; dependencies: none
  sumSet: definition; consumers: additiveComplexity, complementary_factor, imageWord_sum_mem, result, same_length_sum; dependencies: none
  additiveComplexity: definition; consumers: claim, complementary_factor, result, same_length_sum; dependencies: none
  claim: definition; consumers: result; dependencies: WF
  listFactor_getElem: proof_shape: bind-only; consumers: morphic_letter, prefix_occurrence, subfactor_eq; dependencies: WF
  listFactor_add: proof_shape: bind-only; consumers: factorSum_add, morphic_block, suffix_occurrence; dependencies: WF
  listFactor_one: proof_shape: bind-only; consumers: morphic_block; dependencies: WF
  factorSum_eq_list_sum: proof_shape: bind-only; consumers: complementary_factor, cyclic_factor_sum, factorSum_add, imageWord_sum_mem; dependencies: WF
  factorSum_add: proof_shape: bind-only; consumers: complementary_factor, cyclic_factor_sum; dependencies: WF
  morphic_letter: proof_shape: bind-only; consumers: morphic_block; dependencies: WF
  morphic_block: proof_shape: content; consumers: bracket_factor, imageWord_occurs; dependencies: WF
  imageWord_occurs: proof_shape: content; consumers: complementary_factor, imageWord_sum_mem; dependencies: WF
  imageWord_power: proof_shape: bind-only; consumers: imageWord_pow_length, imageWord_pow_sum; dependencies: WP
  imageWord_pow_length: proof_shape: bind-only; consumers: same_length_sum; dependencies: WP, WPL
  imageWord_pow_sum: proof_shape: bind-only; consumers: same_length_sum; dependencies: WP
  imageWord_sum_mem: proof_shape: content; consumers: result, same_length_sum; dependencies: WF
  same_length_sum: proof_shape: content; consumers: complementary_factor; dependencies: WF, WP, WPL
  length_closure_iff: proof_shape: bind-only; consumers: padding_length, result; dependencies: none
  padding_length: proof_shape: bind-only; consumers: result; dependencies: none
  symmetric_ncard_odd: proof_shape: bind-only; consumers: result; dependencies: none
  prefix_occurrence: proof_shape: bind-only; consumers: complementary_factor, cyclic_factor_sum, suffix_occurrence; dependencies: WF
  suffix_occurrence: proof_shape: bind-only; consumers: cyclic_factor_sum; dependencies: WF
  subfactor_eq: proof_shape: bind-only; consumers: complementary_factor, cyclic_factor_sum; dependencies: WF
  cyclic_factor_sum: proof_shape: bind-only; consumers: complementary_factor; dependencies: WF
  bracket_factor: proof_shape: content; consumers: complementary_factor; dependencies: WF
  complementary_factor: proof_shape: content; consumers: result; dependencies: WF, WP, WPL
All private helper escape_witness values are none; the module uses the settling result.
Direct frozen dependencies (declaration statement_id; WF, WP, WPL below):
  WF = D5/S1/Words/Complexity/MorseHedlund.wordFactor:
    sha256:ac48653820670fcfa251876138fb18e7748093ca0d6fa2b0830e368730a3d908
  WP = D5/S1/Words/Powers/WordPower.wordPower:
    sha256:a6e228e7ee6ecdc474ee0b218a6a0c370496359d57e770a78cc40f1991acc416
  WPL = D5/S1/Words/Powers/WordPower.length_wordPower:
    sha256:debf5e4132f97f82101c3032c0cf4922d3f005aae64c4067de34e835705ee5bf

List.ofFn (wordFactor w n i), the type α → List ℤ and List.flatMap
are used directly, preserving the registered expressions without forwarding definitions.
The sole public theorem proves the registered universal-input finite-morphism
obstruction, including empty codewords with unbounded cumulative boundaries.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23244
The utility is none: every theorem is universally quantified; no finite checker,
bounded enumeration, numeric reduction or ordinary certified instance is delivered.
-/

import D5.S1.Words.Complexity.MorseHedlund
import D5.S1.Words.Powers.WordPower
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Finite morphisms of universal words admit a complementary-factor parity obstruction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.SahasrabudheEvenAdditiveComplexityMorphism

open D5.S1.Words.Complexity (wordFactor)

/-- The source's universal input: every finite word occurs at a natural start. -/
def UniversalInput {α : Type*} (w : ℕ → α) : Prop :=
  ∀ u : List α, ∃ i : ℕ, (List.ofFn (wordFactor w u.length i)) = u

/-- A one-sided output of a morphism, with possibly empty codewords, indexed by
the cumulative codeword boundaries.  The unboundedness clause says the output
is infinite. -/
def IsMorphicImage {α : Type*} (w : ℕ → α) (φ : α → List ℤ)
    (y : ℕ → ℤ) : Prop :=
  ∃ b : ℕ → ℕ,
    b 0 = 0 ∧
    Monotone b ∧
    (∀ i : ℕ, b (i + 1) = b i + (φ (w i)).length) ∧
    (∀ N : ℕ, ∃ i : ℕ, N < b i) ∧
    (∀ (i j : ℕ) (h : j < (φ (w i)).length),
      y (b i + j) = (φ (w i)).get ⟨j, h⟩)

/-- The sum of a contiguous length-n factor. -/
def factorSum (y : ℕ → ℤ) (n i : ℕ) : ℤ :=
  ∑ j : Fin n, y (i + j)

/-- The source's set of sums of length-n factors. -/
def sumSet (y : ℕ → ℤ) (n : ℕ) : Set ℤ :=
  {z | ∃ i : ℕ, factorSum y n i = z}

/-- Cardinality of the sum set (finite for a morphic image over a finite source). -/
noncomputable def additiveComplexity (y : ℕ → ℤ) (n : ℕ) : ℕ :=
  (sumSet y n).ncard

/-- Sahasrabudhe's Section 5 question under the registered construction reading:
no universal input followed by one finite morphism can have a positive constant
even additive complexity. -/
def claim : Prop :=
  ∀ (α : Type*) [Fintype α] [Nonempty α] (w : ℕ → α)
    (φ : α → List ℤ) (y : ℕ → ℤ),
    UniversalInput w →
    IsMorphicImage w φ y →
    ¬ (∃ k : ℕ, 0 < k ∧
      ∀ n : ℕ, 0 < n → additiveComplexity y n = 2 * k)



open D5.S1.Words.Powers (wordPower)

variable {α : Type*}


@[simp]
private theorem listFactor_getElem (w : ℕ → α) (n i j : ℕ) (h : j < n) :
    ((List.ofFn (wordFactor w n i)))[j]'(by simpa using h) = w (i + j) := by
  exact List.getElem_ofFn (Eq.mpr (id (congrArg (LT.lt j) List.length_ofFn)) h)

private theorem listFactor_add (w : ℕ → α) (n m i : ℕ) :
    (List.ofFn (wordFactor w (n + m) i)) =
      (List.ofFn (wordFactor w n i)) ++ (List.ofFn (wordFactor w m (i + n))) := by
  change (List.ofFn fun k : Fin (n + m) => w (i + k)) =
    (List.ofFn fun k : Fin n => w (i + k)) ++ (List.ofFn fun k : Fin m => w (i + n + k))
  simpa only [Fin.val_castLE, Fin.val_natAdd, Nat.add_assoc] using
    (List.ofFn_add (f := fun k : Fin (n + m) => w (i + k)))

@[simp]
private theorem listFactor_one (w : ℕ → α) (i : ℕ) :
    (List.ofFn (wordFactor w 1 i)) = [w i] := by
  exact Multiset.coe_eq_singleton.mp rfl

private theorem factorSum_eq_list_sum (y : ℕ → ℤ) (n i : ℕ) :
    factorSum y n i = ((List.ofFn (wordFactor y n i))).sum := by
  simp [factorSum, wordFactor, List.sum_ofFn]

private theorem factorSum_add (y : ℕ → ℤ) (n m i : ℕ) :
    factorSum y (n + m) i = factorSum y n i + factorSum y m (i + n) := by
  simp only [factorSum_eq_list_sum, listFactor_add, List.sum_append]



private theorem morphic_letter (w : ℕ → α) (φ : α → List ℤ)
    (y : ℕ → ℤ) (b : ℕ → ℕ)
    (hy : ∀ (i j : ℕ) (h : j < (φ (w i)).length),
      y (b i + j) = (φ (w i)).get ⟨j, h⟩) (i : ℕ) :
    (List.ofFn (wordFactor y (φ (w i)).length (b i))) = φ (w i) := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    rw [listFactor_getElem y (φ (w i)).length (b i) j h₂]
    exact hy i j h₂

private theorem morphic_block (w : ℕ → α) (φ : α → List ℤ)
    (y : ℕ → ℤ) (b : ℕ → ℕ) (hmono : Monotone b)
    (hstep : ∀ i, b (i + 1) = b i + (φ (w i)).length)
    (hy : ∀ (i j : ℕ) (h : j < (φ (w i)).length),
      y (b i + j) = (φ (w i)).get ⟨j, h⟩) (s t : ℕ) :
    (List.ofFn (wordFactor y (b (s + t) - b s) (b s))) =
      List.flatMap φ ((List.ofFn (wordFactor w t s))) := by
  induction t with
  | zero => simp only [Nat.add_zero, Nat.sub_self]; rfl
  | succ t ih =>
    have hle := hmono (show s ≤ s + t by omega)
    have hend : b (s + (t + 1)) = b (s + t) + (φ (w (s + t))).length := by
      exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (hstep (s.add t))) (b s))
    have hlen : b (s + (t + 1)) - b s = b (s + t) - b s + (φ (w (s + t))).length := by omega
    rw [hlen, listFactor_add, ih]
    have hpos : b s + (b (s + t) - b s) = b (s + t) := by exact Nat.add_sub_of_le hle
    rw [hpos, morphic_letter w φ y b hy]
    rw [listFactor_add w t 1 s, List.flatMap_append, listFactor_one, List.flatMap_singleton]

private theorem imageWord_occurs (w : ℕ → α) (φ : α → List ℤ)
    (y : ℕ → ℤ) (hw : UniversalInput w) (himage : IsMorphicImage w φ y)
    (u : List α) : ∃ i, (List.ofFn (wordFactor y (List.flatMap φ u).length i)) =
      List.flatMap φ u := by
  obtain ⟨b, hb0, hmono, hstep, hunbdd, hy⟩ := himage
  obtain ⟨s, hs⟩ := hw u
  have he := morphic_block w φ y b hmono hstep hy s u.length
  rw [hs] at he
  have hl := congrArg List.length he
  simp only [List.length_ofFn] at hl
  exact ⟨b s, hl ▸ he⟩


private theorem imageWord_power (φ : α → List ℤ) (u : List α) (r : ℕ) :
    List.flatMap φ (wordPower r u) = wordPower r (List.flatMap φ u) := by
  calc
    List.flatMap φ (wordPower r u) =
        ((List.replicate r u).flatMap (id : List α → List α)).flatMap φ := by
      exact congrArg (List.flatMap φ) (List.flatten_eq_flatMap (L := List.replicate r u))
    _ = (List.replicate r u).flatMap (fun U => U.flatMap φ) :=
      List.flatMap_assoc (l := List.replicate r u) (f := id) (g := φ)
    _ = wordPower r (List.flatMap φ u) :=
      List.flatMap_replicate (f := fun U : List α => U.flatMap φ)

private theorem imageWord_pow_length (φ : α → List ℤ) (u : List α) (r : ℕ) :
    (List.flatMap φ (wordPower r u)).length = r * (List.flatMap φ u).length := by
  rw [imageWord_power, D5.S1.Words.Powers.length_wordPower]

private theorem imageWord_pow_sum (φ : α → List ℤ) (u : List α) (r : ℕ) :
    (List.flatMap φ (wordPower r u)).sum = (r : ℤ) * (List.flatMap φ u).sum := by
  rw [imageWord_power]
  simp only [D5.S1.Words.Powers.wordPower, List.sum_flatten, List.map_replicate,
    List.sum_replicate, nsmul_eq_mul]

private theorem imageWord_sum_mem (w : ℕ → α) (φ : α → List ℤ)
    (y : ℕ → ℤ) (hw : UniversalInput w) (himage : IsMorphicImage w φ y)
    (u : List α) : (List.flatMap φ u).sum ∈ sumSet y (List.flatMap φ u).length := by
  obtain ⟨i, hi⟩ := imageWord_occurs w φ y hw himage u
  exact ⟨i, by rw [factorSum_eq_list_sum, hi]⟩

private theorem same_length_sum (w : ℕ → α) (φ : α → List ℤ)
    (y : ℕ → ℤ) (hw : UniversalInput w) (himage : IsMorphicImage w φ y)
    (B : ℕ) (hB : 0 < B)
    (hcomplex : ∀ n, 0 < n → additiveComplexity y n = B)
    (u v : List α) (hlen : (List.flatMap φ u).length = (List.flatMap φ v).length) :
    (List.flatMap φ u).sum = (List.flatMap φ v).sum := by
  classical
  by_cases hzero : (List.flatMap φ u).length = 0
  · have hu : List.flatMap φ u = [] := List.length_eq_zero_iff.mp hzero
    have hv : List.flatMap φ v = [] := List.length_eq_zero_iff.mp (hlen ▸ hzero)
    simp [hu, hv]
  by_contra hne
  let f : Fin (B + 1) → ℤ := fun j =>
    (j.val : ℤ) * (List.flatMap φ u).sum + ((B - j.val : ℕ) : ℤ) * (List.flatMap φ v).sum
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hi : i.val ≤ B := by exact Fin.is_le i
    have hj : j.val ≤ B := by exact Fin.is_le j
    have he : ((i.val : ℤ) - (j.val : ℤ)) *
        ((List.flatMap φ u).sum - (List.flatMap φ v).sum) = 0 := by
      dsimp [f] at hij
      rw [Nat.cast_sub hi, Nat.cast_sub hj] at hij
      nlinarith [hij]
    have hdiff : (List.flatMap φ u).sum - (List.flatMap φ v).sum ≠ 0 := sub_ne_zero.mpr hne
    have heq : (i.val : ℤ) = (j.val : ℤ) := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hdiff)
    exact_mod_cast heq
  have hn : 0 < B * (List.flatMap φ u).length := Nat.mul_pos hB (Nat.pos_of_ne_zero hzero)
  have hfin : (sumSet y (B * (List.flatMap φ u).length)).Finite :=
    Set.finite_of_ncard_pos (by rw [← additiveComplexity, hcomplex _ hn]; exact hB)
  have hsub : Set.range f ⊆ sumSet y (B * (List.flatMap φ u).length) := by
    rintro z ⟨j, rfl⟩
    let U := wordPower j.val u ++ wordPower (B - j.val) v
    have hU := imageWord_sum_mem w φ y hw himage U
    have hj : j.val ≤ B := by exact Fin.is_le j
    have hlenU : (List.flatMap φ U).length = B * (List.flatMap φ u).length := by
      dsimp [U]
      simp only [List.flatMap_append, List.length_append, imageWord_pow_length, ← hlen]
      rw [← Nat.add_mul, Nat.add_sub_of_le hj]
    have hsumU : (List.flatMap φ U).sum = f j := by
      simp [U, f, imageWord_pow_sum]
    rwa [hlenU, hsumU] at hU
  have hcard := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_range_of_injective hf, Nat.card_fin] at hcard
  change B + 1 ≤ additiveComplexity y (B * (List.flatMap φ u).length) at hcard
  rw [hcomplex _ hn] at hcard
  omega

/-- The lengths of complete images form exactly the semigroup generated by codeword lengths. -/
private theorem length_closure_iff (φ : α → List ℤ) (n : ℕ) :
    n ∈ AddSubmonoid.closure (Set.range fun a => (φ a).length) ↔
      ∃ u : List α, (List.flatMap φ u).length = n := by
  change α → List ℤ at φ
  rw [← FreeAddMonoid.mrange_lift (fun a => (φ a).length)]
  change (∃ u : FreeAddMonoid α, FreeAddMonoid.lift (fun a => (φ a).length) u = n) ↔ _
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨FreeAddMonoid.toList u, ?_⟩
    rw [List.length_flatMap]
    exact (FreeAddMonoid.lift_apply (fun a => (φ a).length) u).symm.trans hu
  · rintro ⟨u, hu⟩
    refine ⟨FreeAddMonoid.ofList u, ?_⟩
    rw [FreeAddMonoid.lift_ofList]
    change (List.flatMap φ u).length = n at hu
    rw [List.length_flatMap] at hu
    exact hu

private theorem padding_length (φ : α → List ℤ) :
    ∃ C : ℕ, ∀ n ≥ C, Nat.setGcd (Set.range fun a => (φ a).length) ∣ n →
      ∃ u : List α, (List.flatMap φ u).length = n := by
  obtain ⟨C, hC⟩ := Nat.exists_mem_closure_of_ge (Set.range fun a => (φ a).length)
  exact ⟨C, fun n hn hd => (length_closure_iff φ n).mp (hC n hn hd)⟩

private theorem symmetric_ncard_odd (S : Set ℤ) (hfin : S.Finite) (c : ℤ)
    (hc : c ∈ S) (hsym : ∀ z ∈ S, 2 * c - z ∈ S) : Odd S.ncard := by
  classical
  letI : Fintype S := hfin.fintype
  let f : Function.End S := fun z => ⟨2 * c - z.val, hsym z.val z.property⟩
  have hpow : f ^ (2 ^ 1) = 1 := by
    funext z
    apply Subtype.ext
    change 2 * c - (2 * c - z.val) = z.val
    omega
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hpow
  have hfixed : f.fixedPoints = ({⟨c, hc⟩} : Set S) := by
    ext z
    change f z = z ↔ z = ⟨c, hc⟩
    constructor
    · intro he
      apply Subtype.ext
      have he' := congrArg Subtype.val he
      change 2 * c - z.val = z.val at he'
      change z.val = c
      omega
    · intro he
      subst z
      apply Subtype.ext
      change 2 * c - c = c
      omega
  have hcardfixed : Fintype.card f.fixedPoints = 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hfixed, Set.ncard_singleton]
  rw [hcardfixed] at h
  have hcard : Fintype.card S = S.ncard := by
    exact Set.fintypeCard_eq_ncard S
  rw [hcard] at h
  exact Nat.odd_iff.mpr (by simpa only [Nat.ModEq, Nat.one_mod] using h)

private theorem prefix_occurrence (y : ℕ → ℤ) (u v : List ℤ) (i : ℕ)
    (h : (List.ofFn (wordFactor y (u ++ v).length i)) = u ++ v) :
    (List.ofFn (wordFactor y u.length i)) = u := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    have hj : j < (u ++ v).length := by simp; omega
    rw [listFactor_getElem y u.length i j h₂]
    have he := congrArg (fun l : List ℤ => l[j]?) h
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hj),
      List.getElem?_eq_getElem hj, listFactor_getElem y _ i j hj,
      List.getElem_append_left h₂] at he
    exact Option.some.inj he

private theorem suffix_occurrence (y : ℕ → ℤ) (u v : List ℤ) (i : ℕ)
    (h : (List.ofFn (wordFactor y (u ++ v).length i)) = u ++ v) :
    (List.ofFn (wordFactor y v.length (i + u.length))) = v := by
  have he : (List.ofFn (wordFactor y u.length i)) ++ (List.ofFn (wordFactor y v.length (i + u.length))) =
      u ++ v := by
    have he := congrArg (fun n : ℕ => List.ofFn (wordFactor y n i))
      (show (u ++ v).length = u.length + v.length from List.length_append)
    exact (listFactor_add y u.length v.length i).symm.trans (he.symm.trans h)
  rw [prefix_occurrence y u v i h] at he
  exact List.append_cancel_left he

private theorem subfactor_eq (y : ℕ → ℤ) (m i j p n : ℕ)
    (h : (List.ofFn (wordFactor y m i)) = (List.ofFn (wordFactor y m j))) (hpn : p + n ≤ m) :
    (List.ofFn (wordFactor y n (i + p))) = (List.ofFn (wordFactor y n (j + p))) := by
  apply List.ext_getElem
  · simp
  · intro k hk₁ hk₂
    have hk : k < n := by simpa using hk₁
    have hpm : p + k < m := by omega
    rw [listFactor_getElem y n (i + p) k hk, listFactor_getElem y n (j + p) k hk]
    have he := congrArg (fun l : List ℤ => l[p + k]?) h
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hpm),
      List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using hpm),
      listFactor_getElem y m i (p + k) hpm, listFactor_getElem y m j (p + k) hpm] at he
    simpa only [Nat.add_assoc] using Option.some.inj he

private theorem cyclic_factor_sum (y : ℕ → ℤ) (T : List ℤ) (q p : ℕ)
    (hp : p ≤ T.length) (hTT : (List.ofFn (wordFactor y (T ++ T).length q)) = T ++ T) :
    factorSum y T.length (q + p) = T.sum := by
  have hT₁ := prefix_occurrence y T T q hTT
  have hT₂ := suffix_occurrence y T T q hTT
  have he := subfactor_eq y T.length q (q + T.length) 0 p
    (hT₁.trans hT₂.symm) (by omega)
  simp only [Nat.add_zero] at he
  have hpref : factorSum y p q = factorSum y p (q + T.length) := by
    simpa only [factorSum_eq_list_sum] using congrArg List.sum he
  have hsum : factorSum y T.length q = T.sum := by
    rw [factorSum_eq_list_sum, hT₁]
  have h₁ := factorSum_add y p T.length q
  have h₂ := factorSum_add y T.length p q
  rw [Nat.add_comm p T.length] at h₁
  omega

private theorem bracket_factor [Fintype α] (w : ℕ → α) (φ : α → List ℤ)
    (y : ℕ → ℤ) (b : ℕ → ℕ) (hb0 : b 0 = 0) (hmono : Monotone b)
    (hstep : ∀ i, b (i + 1) = b i + (φ (w i)).length)
    (hunbdd : ∀ N, ∃ i, N < b i)
    (hy : ∀ (i j : ℕ) (h : j < (φ (w i)).length),
      y (b i + j) = (φ (w i)).get ⟨j, h⟩)
    (n i : ℕ) :
    ∃ (u : List α) (s p : ℕ),
      s + p = i ∧
      p + n ≤ (List.flatMap φ u).length ∧
      (List.flatMap φ u).length ≤ n + 2 * (∑ a, (φ a).length) ∧
      (List.ofFn (wordFactor y (List.flatMap φ u).length s)) = List.flatMap φ u := by
  classical
  let M := ∑ a, (φ a).length
  have hM : ∀ a, (φ a).length ≤ M := by
    intro a
    change (φ a).length ≤ ∑ a, (φ a).length
    exact Finset.single_le_sum (f := fun a => (φ a).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  let r := Nat.find (hunbdd i)
  have hr : i < b r := Nat.find_spec (hunbdd i)
  have hr0 : 0 < r := by
    by_contra h
    have : r = 0 := Nat.eq_zero_of_not_pos h
    rw [this, hb0] at hr
    omega
  let s := r - 1
  have hs : s + 1 = r := by exact Nat.sub_add_cancel hr0
  have hbs : b s ≤ i := by
    have := Nat.find_min (hunbdd i) (show s < r by dsimp [s]; omega)
    omega
  have hstart : i < b s + (φ (w s)).length := by
    rw [← hstep, hs]
    exact hr
  let t := Nat.find (hunbdd (i + n))
  have ht : i + n < b t := Nat.find_spec (hunbdd (i + n))
  have ht0 : 0 < t := by
    by_contra h
    have : t = 0 := Nat.eq_zero_of_not_pos h
    rw [this, hb0] at ht
    omega
  have hbt : b (t - 1) ≤ i + n := by
    have := Nat.find_min (hunbdd (i + n)) (show t - 1 < t by omega)
    omega
  have htstep := hstep (t - 1)
  rw [Nat.sub_add_cancel ht0] at htstep
  have hst : s ≤ t := by
    by_contra h
    have := hmono (show t ≤ s by omega)
    omega
  let u := (List.ofFn (wordFactor w (t - s) s))
  have hblock := morphic_block w φ y b hmono hstep hy s (t - s)
  rw [Nat.add_sub_of_le hst] at hblock
  have hlen : (List.flatMap φ u).length = b t - b s := by
    have he := congrArg List.length hblock
    simpa only [List.length_ofFn] using he.symm
  refine ⟨u, b s, i - b s, by omega, ?_, ?_, ?_⟩
  · rw [hlen]; omega
  · have hMs := hM (w s)
    have hMt := hM (w (t - 1))
    rw [hlen]
    change b t - b s ≤ n + 2 * M
    omega
  · exact (congrArg (fun n : ℕ => List.ofFn (wordFactor y n (b s))) hlen).trans hblock

private theorem complementary_factor [Fintype α]
    (w : ℕ → α) (φ : α → List ℤ) (y : ℕ → ℤ)
    (hw : UniversalInput w) (himage : IsMorphicImage w φ y)
    (B : ℕ) (hB : 0 < B)
    (hcomplex : ∀ n, 0 < n → additiveComplexity y n = B)
    (n : ℕ) (W : List α) (hW : (List.flatMap φ W).length = n)
    (hpad : ∀ u : List α, (List.flatMap φ u).length ≤ n + 2 * (∑ a, (φ a).length) →
      ∃ V : List α, (List.flatMap φ (u ++ V)).length = 2 * n) :
    ∀ z ∈ sumSet y n, 2 * (List.flatMap φ W).sum - z ∈ sumSet y n := by
  intro z hz
  obtain ⟨i, hi⟩ := hz
  obtain ⟨b, hb0, hmono, hstep, hunbdd, hy⟩ := himage
  obtain ⟨u, s, p, hsp, hpn, hbound, hu⟩ :=
    bracket_factor w φ y b hb0 hmono hstep hunbdd hy n i
  obtain ⟨V, hV⟩ := hpad u hbound
  let T := List.flatMap φ (u ++ V)
  have hTL : T.length = 2 * n := hV
  have htwice : T.sum = 2 * (List.flatMap φ W).sum := by
    have he := same_length_sum w φ y hw ⟨b, hb0, hmono, hstep, hunbdd, hy⟩ B hB hcomplex
      (u ++ V) (W ++ W) (by
        calc
          (List.flatMap φ (u ++ V)).length = 2 * n := hV
          _ = (List.flatMap φ (W ++ W)).length := by
            simp only [List.flatMap_append, List.length_append, hW]; omega)
    simpa [T, List.flatMap_append, two_mul] using he
  obtain ⟨q, hq⟩ := imageWord_occurs w φ y hw
    ⟨b, hb0, hmono, hstep, hunbdd, hy⟩ ((u ++ V) ++ (u ++ V))
  have hTT : (List.ofFn (wordFactor y (T ++ T).length q)) = T ++ T := by
    have he : List.flatMap φ ((u ++ V) ++ (u ++ V)) = T ++ T := List.flatMap_append
    exact Eq.mp (congrArg (fun l : List ℤ => List.ofFn (wordFactor y l.length q) = l) he) hq
  have hT := prefix_occurrence y T T q hTT
  have huq : (List.ofFn (wordFactor y (List.flatMap φ u).length q)) = List.flatMap φ u := by
    exact prefix_occurrence y (List.flatMap φ u) (List.flatMap φ V) q
      (by
        have he : T = List.flatMap φ u ++ List.flatMap φ V := List.flatMap_append
        exact Eq.mp (congrArg (fun l : List ℤ => List.ofFn (wordFactor y l.length q) = l) he) hT)
  have hv := subfactor_eq y (List.flatMap φ u).length s q p n (hu.trans huq.symm) hpn
  rw [hsp] at hv
  have hval : factorSum y n (q + p) = z := by
    rw [factorSum_eq_list_sum, ← hv, ← factorSum_eq_list_sum, hi]
  have hle : p ≤ T.length := by
    have : (List.flatMap φ u).length ≤ T.length := by
      simp only [T, List.flatMap_append, List.length_append]; omega
    omega
  have htotal := cyclic_factor_sum y T q p hle hTT
  rw [hTL, htwice, show 2 * n = n + n by omega, factorSum_add] at htotal
  exact ⟨q + p + n, by omega⟩

theorem result : claim := by
  intro α _ _ w φ y hw himage
  rintro ⟨k, hk, hcomplex⟩
  classical
  let S := Set.range fun a => (φ a).length
  let d := Nat.setGcd S
  let M := ∑ a, (φ a).length
  have hd : 0 < d := by
    by_contra h
    have hzero : Nat.setGcd S = 0 := by exact Nat.eq_zero_of_not_pos h
    have hall := Nat.setGcd_eq_zero_iff.mp hzero
    have hl : ∀ a, (φ a).length = 0 := fun a => Set.mem_singleton_iff.mp (hall ⟨a, rfl⟩)
    obtain ⟨b, hb0, hmono, hstep, hunbdd, hy⟩ := himage
    have hb : ∀ i, b i = 0 := by
      intro i
      induction i with
      | zero => exact hb0
      | succ i ih => simpa [hl, ih] using hstep i
    obtain ⟨i, hi⟩ := hunbdd 0
    rw [hb] at hi
    omega
  obtain ⟨C, hC⟩ := padding_length φ
  let n := d * (C + 2 * M + 1)
  have hn : 0 < n := Nat.mul_pos hd (by omega)
  have hnlarge : C + 2 * M ≤ n := by
    exact (show C + 2 * M ≤ C + 2 * M + 1 by omega).trans
      (Nat.le_mul_of_pos_left _ hd)
  have hdn : d ∣ n := ⟨C + 2 * M + 1, rfl⟩
  obtain ⟨W, hW⟩ := hC n (by omega) hdn
  have hpad : ∀ u : List α, (List.flatMap φ u).length ≤ n + 2 * M →
      ∃ V : List α, (List.flatMap φ (u ++ V)).length = 2 * n := by
    intro u hu
    let m := (List.flatMap φ u).length
    have hdm : d ∣ m :=
      Nat.setGcd_dvd_of_mem_closure ((length_closure_iff φ m).mpr ⟨u, rfl⟩)
    have hdt : d ∣ 2 * n - m := Nat.dvd_sub (dvd_mul_of_dvd_right hdn 2) hdm
    have hle : m ≤ 2 * n := by dsimp [m]; omega
    obtain ⟨V, hV⟩ := hC (2 * n - m) (by omega) hdt
    exact ⟨V, by simp only [List.flatMap_append, List.length_append, hV]; dsimp [m] at *; omega⟩
  have hsym := complementary_factor w φ y hw himage (2 * k) (by omega) hcomplex n W hW hpad
  have hcenter : (List.flatMap φ W).sum ∈ sumSet y n := by
    simpa only [hW] using imageWord_sum_mem w φ y hw himage W
  have hfinite : (sumSet y n).Finite :=
    Set.finite_of_ncard_pos (by change 0 < additiveComplexity y n; rw [hcomplex n hn]; omega)
  have hodd := symmetric_ncard_odd (sumSet y n) hfinite (List.flatMap φ W).sum hcenter hsym
  change Odd (additiveComplexity y n) at hodd
  rw [hcomplex n hn] at hodd
  obtain ⟨r, hr⟩ := hodd
  omega

end D5.S1.Words.Complexity.SahasrabudheEvenAdditiveComplexityMorphism
