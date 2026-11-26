/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/TailPauliQuotientMaps
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral Pauli actions induce two complementary quotient maps. -/

import D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TailPauliPairing
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Integral transport for the two Barnes–Wall tail quotients

In KRR, arXiv:2411.13646v2, (A.1.1), fix the first tensor bit. For an
even number of tail slots, the first-bit-1 scaled subset rows give the basis
of `B`, with coefficients proportional to `2^ceil((n - |u|)/2)` in the
subset indicator basis. The first-bit-0 rows give the basis of `A`, scaled
by an extra factor of two at even tail words. This is the convention in the local
manuscript's “Rank-uniform level matching for the literal KRR involutions.”
https://arxiv.org/html/2411.13646v2#A1

The coordinate input is the tail specialization of (A.2.4)–(A.2.6).
The remaining ambient step is to identify the tensor-lattice tail summands
with these two integral coordinate spaces and verify those generator rows
under the identification.
-/

open scoped BigOperators Matrix
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TailPauliQuotientMaps

open LatticeTwistedGroundRealization.SignQuotient (F₂)
open TailPauliPairing (Word flip parity parity_flip activity deviationMatrix)

variable {ι : Type} [Fintype ι] [LinearOrder ι]

/-- Integer coefficients in the scaled subset basis of the chosen tail block. -/
abbrev Coeff (ι : Type) := Word ι → ℤ

/-- Read the coordinates of parity `p` modulo two, with zero elsewhere. -/
def reduce (p : F₂) : Coeff ι →ₗ[ℤ] (Word ι → F₂) :=
  (show Coeff ι →+ (Word ι → F₂) from
    { toFun := fun a u => if parity u = p then (a u : F₂) else 0
      map_zero' := by
        funext u
        by_cases hu : parity u = p <;> simp [hu]
      map_add' := by
        intro a b
        funext u
        by_cases hu : parity u = p <;> simp [hu, Int.cast_add] }).toIntLinearMap

@[simp] theorem reduce_apply (p : F₂) (a : Coeff ι) (u : Word ι) :
    reduce p a u = if parity u = p then (a u : F₂) else 0 := rfl

/-- In the basis of `B` this is `A` for `p = 0`. In the basis of `A`
this is `2B` for `p = 1`. -/
def parityLattice (p : F₂) : Submodule ℤ (Coeff ι) :=
  (reduce p).ker

theorem mem_parityLattice (p : F₂) (a : Coeff ι) :
    a ∈ parityLattice p ↔ ∀ u, parity u = p → (2 : ℤ) ∣ a u := by
  change reduce p a = 0 ↔ _
  constructor
  · intro ha u hu
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a u) 2).mp
      (by simpa [hu] using congrFun ha u)
  · intro ha
    funext u
    by_cases hu : parity u = p
    · simpa [hu] using (ZMod.intCast_zmod_eq_zero_iff_dvd (a u) 2).mpr (ha u hu)
    · simp [hu]

/-- Change to the containing lattice's basis. For `p = 0` this embeds
`A` into `B`. For `p = 1` it gives the `A`-coordinates of twice a
vector of `B`. -/
def embed (p : F₂) (a : Coeff ι) : Coeff ι :=
  fun u => (if parity u = p then 2 else 1) * a u

theorem mem_parityLattice_iff_exists_embed (p : F₂) (b : Coeff ι) :
    b ∈ parityLattice p ↔ ∃ a, embed p a = b := by
  rw [mem_parityLattice]
  constructor
  · intro hb
    have hw (u : Word ι) : ∃ a : ℤ, (if parity u = p then 2 else 1) * a = b u := by
      by_cases hu : parity u = p
      · obtain ⟨a, ha⟩ := hb u hu
        exact ⟨a, by simpa [hu] using ha.symm⟩
      · exact ⟨b u, by simp [hu]⟩
    choose a ha using hw
    exact ⟨a, funext ha⟩
  · rintro ⟨a, rfl⟩ u hu
    exact ⟨a u, by simp [embed, hu]⟩

theorem toggle : ∀ p q : F₂, p + 1 = q ↔ p ≠ q := by
  decide +kernel

private theorem eq_one_iff (p : F₂) : p = 1 ↔ p ≠ 0 := by
  have h := toggle 0 p
  rw [zero_add] at h
  exact eq_comm.trans (h.trans ne_comm)

private theorem embed_twice (b : Coeff ι) :
    embed 0 (embed 1 b) = (2 : ℤ) • b := by
  funext u
  by_cases hu : parity u = 0 <;> simp [embed, eq_one_iff, hu, zsmul_eq_mul]

/-- A quotient in the integral basis of its numerator lattice. -/
abbrev ParityQuotient (ι : Type) [Fintype ι] (p : F₂) :=
  Coeff ι ⧸ parityLattice p

/-- The quotient coordinates use the same rows as the sparse phase matrix. -/
def quotientCoords (p : F₂) : ParityQuotient ι p →ₗ[ℤ] (Word ι → F₂) :=
  (parityLattice p).liftQ (reduce p) le_rfl

theorem quotientCoords_injective (p : F₂) :
    Function.Injective (quotientCoords (ι := ι) p) := by
  intro x y h
  obtain ⟨a, rfl⟩ := (parityLattice p).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (parityLattice p).mkQ_surjective y
  change reduce p a = reduce p b at h
  apply sub_eq_zero.mp
  rw [← map_sub]
  have hm : a - b ∈ parityLattice p := by
    change reduce p (a - b) = 0
    rw [map_sub, h, sub_self]
  have hk : a - b ∈ (parityLattice p).mkQ.ker := by
    rwa [Submodule.ker_mkQ]
  exact LinearMap.mem_ker.mp hk

theorem quotientCoords_range (p : F₂) (a : Word ι → F₂) :
    (∃ x, quotientCoords p x = a) ↔ ∀ u, parity u ≠ p → a u = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ u hu
    obtain ⟨b, rfl⟩ := (parityLattice p).mkQ_surjective x
    change reduce p b u = 0
    simp [hu]
  · intro ha
    refine ⟨(parityLattice p).mkQ (fun u => ((a u).val : ℤ)), ?_⟩
    change reduce p (fun u => ((a u).val : ℤ)) = a
    funext u
    by_cases hu : parity u = p
    · simp [hu, ZMod.natCast_zmod_val]
    · simp [hu, ha u hu]

private abbrev End (ι : Type) := Coeff ι →ₗ[ℤ] Coeff ι

/-- Deviation from the identity in row-action convention. -/
def dev (g : End ι) : End ι := g - LinearMap.id

/-- In basis `p`, the deviation lands in the even-coefficient sublattice
at parity `p`, and its opposite-parity reduction is the sparse row action. -/
structure Transports (p : F₂) (g : End ι) (M : Matrix (Word ι) (Word ι) F₂) : Prop where
  lands : ∀ b, reduce p (dev g b) = 0
  sparse : ∀ b, reduce (p + 1) (dev g b) = reduce p b ᵥ* M

/-- The quotient map of the deviation. At `p = 0` it is `B/A → A/2B`.
At `p = 1` it is `A/2B → B/A`. The input to either quotient is in the
basis of its numerator. -/
def quotientMap {p : F₂} {g : End ι} {M : Matrix (Word ι) (Word ι) F₂}
    (hg : Transports p g M) : ParityQuotient ι p →ₗ[ℤ] ParityQuotient ι (p + 1) :=
  (parityLattice p).mapQ (parityLattice (p + 1)) (dev g) (by
    intro b hb
    change reduce p b = 0 at hb
    change reduce (p + 1) (dev g b) = 0
    rw [hg.sparse, hb, Matrix.zero_vecMul])

theorem quotientMap_coords
    {p : F₂} {g : End ι} {M : Matrix (Word ι) (Word ι) F₂}
    (hg : Transports p g M) (x : ParityQuotient ι p) :
    quotientCoords (p + 1) (quotientMap hg x) = quotientCoords p x ᵥ* M := by
  obtain ⟨b, rfl⟩ := (parityLattice p).mkQ_surjective x
  exact hg.sparse b

/-- Integer generator deviation from KRR (A.2.5) and (A.2.6). In the
`B` basis (`p = 0`), the coefficient from the source `flip v r` is
two when that source is odd and one when it is even. In the `A` basis
(`p = 1`) the roles are reversed. The flag is false for X, true for Z. -/
def slotDev (p : F₂) (r : ι) (isZ : Bool) : End ι :=
  (show Coeff ι →+ Coeff ι from
    { toFun := fun b v => (if v r = isZ then -2 * b v else 0) +
        (if flip v r r = isZ then (if parity v = p then 2 else 1) * b (flip v r) else 0)
      map_zero' := by
        funext v
        by_cases hd : v r = isZ <;> by_cases hf : flip v r r = isZ <;> simp [hd, hf]
      map_add' := by
        intro a b
        funext v
        by_cases hd : v r = isZ <;> by_cases hf : flip v r r = isZ <;>
          simp [hd, hf, mul_add] <;> abel }).toIntLinearMap

theorem slotDev_apply (p : F₂) (r : ι) (isZ : Bool) (b : Coeff ι) (v : Word ι) :
    slotDev p r isZ b v = (if v r = isZ then -2 * b v else 0) +
      (if flip v r r = isZ then (if parity v = p then 2 else 1) * b (flip v r) else 0) :=
  rfl

/-- The generator itself is the identity plus its integer deviation. -/
def slot (p : F₂) (r : ι) (isZ : Bool) : End ι :=
  LinearMap.id + slotDev p r isZ

@[simp] theorem dev_slot (p : F₂) (r : ι) (isZ : Bool) :
    dev (slot p r isZ) = slotDev p r isZ := by
  unfold dev slot
  abel

def select (r : ι) (isZ side : Bool) (s : ι) : F₂ :=
  if s = r ∧ isZ = side then 1 else 0

theorem flip_flip (u : Word ι) (r : ι) : flip (flip u r) r = u := by
  funext s
  by_cases hs : s = r <;> simp [TailPauliPairing.flip, hs]

private theorem slotSparse_entry (r : ι) (isZ : Bool) (u v : Word ι) :
    deviationMatrix (select r isZ false) (select r isZ true) u v =
      if v = flip u r ∧ u r = isZ then 1 else 0 := by
  classical
  unfold deviationMatrix
  rw [Finset.sum_eq_single r]
  · by_cases hv : v = flip u r <;> cases hu : u r <;> cases isZ <;>
      simp [activity, select, hv, hu]
  · intro s _ hs
    simp [activity, select, hs]
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

private theorem vecMul_slotSparse (r : ι) (isZ : Bool) (a : Word ι → F₂) (v : Word ι) :
    (a ᵥ* deviationMatrix (select r isZ false) (select r isZ true)) v =
      if flip v r r = isZ then a (flip v r) else 0 := by
  classical
  rw [Matrix.vecMul_apply_eq_sum, Finset.sum_eq_single (flip v r)]
  · by_cases hv : flip v r r = isZ <;> simp [slotSparse_entry, flip_flip, hv]
  · intro u _ hu
    have hn : v ≠ flip u r := by
      intro h
      apply hu
      rw [h, flip_flip]
    simp [slotSparse_entry, hn]
  · intro hv
    exact (hv (Finset.mem_univ _)).elim

/-- A single X or Z has the same mod-two sparse row in the two quotient maps.
The integer diagonal is killed in both bases. -/
theorem slot_transports (p : F₂) (r : ι) (isZ : Bool) :
    Transports p (slot p r isZ) (deviationMatrix (select r isZ false) (select r isZ true)) := by
  have htwo : (2 : F₂) = 0 := by decide
  constructor
  · intro b
    funext v
    by_cases hv : parity v = p
    · by_cases hd : v r = isZ <;> by_cases hs : flip v r r = isZ <;>
        simp [hv, hd, hs, slotDev_apply, Int.cast_add, Int.cast_mul, Int.cast_neg, htwo]
    · simp [hv]
  · intro b
    funext v
    rw [vecMul_slotSparse, dev_slot, reduce_apply]
    have hf : parity (flip v r) = p ↔ parity v = p + 1 := by
      rw [parity_flip, toggle]
      exact ne_comm.trans ((toggle p (parity v)).symm.trans eq_comm)
    by_cases hv : parity v = p + 1
    · have hn : parity v ≠ p := Ne.symm ((toggle p (parity v)).mp hv.symm)
      by_cases hd : v r = isZ <;> by_cases hs : flip v r r = isZ <;>
        simp [hv, hf, hn, hd, hs, slotDev_apply, Int.cast_add, Int.cast_mul, Int.cast_neg, htwo]
    · simp [hv, hf]

/-- The deviations of a product induce the sum of the two sparse actions.
The cross term factors through the intermediate even-coefficient lattice. -/
theorem Transports.comp {p : F₂} {g h : End ι} {M N : Matrix (Word ι) (Word ι) F₂}
    (hg : Transports p g M) (hh : Transports p h N) :
    Transports p (h.comp g) (M + N) := by
  have hdev (b : Coeff ι) : dev (h.comp g) b = dev g b + dev h b + dev h (dev g b) := by
    simp only [dev, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub]
    abel
  constructor
  · intro b
    simp only [hdev, map_add, hg.lands, hh.lands, add_zero]
  · intro b
    simp only [hdev, map_add, hg.sparse, hh.sparse, hg.lands, Matrix.zero_vecMul, add_zero,
      Matrix.vecMul_add]

/-- The product law on the quotient maps themselves. -/
theorem quotientMap_comp {p : F₂} {g h : End ι} {M N : Matrix (Word ι) (Word ι) F₂}
    (hg : Transports p g M) (hh : Transports p h N) :
    quotientMap (hg.comp hh) = quotientMap hg + quotientMap hh := by
  apply LinearMap.ext
  intro x
  apply quotientCoords_injective (p + 1)
  simp [quotientMap_coords, Matrix.vecMul_add]

/-- Central inversion contributes zero to both reductions. -/
theorem Transports.neg {p : F₂} {g : End ι} {M : Matrix (Word ι) (Word ι) F₂}
    (hg : Transports p g M) : Transports p (-g) M := by
  have hdev (b : Coeff ι) : dev (-g) b = dev g b - (g b + g b) := by
    simp only [dev, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply]
    abel
  have hdouble (q : F₂) (b : Coeff ι) : reduce q (b + b) = 0 := by
    funext v
    by_cases hv : parity v = q <;> simp [hv, Int.cast_add, CharTwo.add_self_eq_zero]
  exact ⟨fun b => by rw [hdev, map_sub, hdouble, sub_zero, hg.lands],
    fun b => by rw [hdev, map_sub, hdouble, sub_zero, hg.sparse]⟩

private theorem deviation_add (x z y w : ι → F₂) :
    deviationMatrix (x + y) (z + w) = deviationMatrix x z + deviationMatrix y w := by
  classical
  ext u v
  simp only [deviationMatrix, Matrix.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hv : v = flip u r <;> cases hu : u r <;> simp [activity, hv, hu]

/-- A list of pairs (slot, isZ), read in row-action order. -/
def wordAction (p : F₂) : List (ι × Bool) → End ι
  | [] => LinearMap.id
  | (r, isZ) :: tail => (wordAction p tail).comp (slot p r isZ)

/-- The exponents of X or Z at each slot, counted modulo two. -/
def selections (side : Bool) : List (ι × Bool) → (ι → F₂)
  | [] => 0
  | (r, isZ) :: tail => select r isZ side + selections side tail

def signedWord (negative : Bool) (p : F₂) (word : List (ι × Bool)) : End ι :=
  if negative then -wordAction p word else wordAction p word

theorem word_transports (p : F₂) (word : List (ι × Bool)) :
    Transports p (wordAction p word)
      (deviationMatrix (selections false word) (selections true word)) := by
  induction word with
  | nil =>
    have hz : deviationMatrix (0 : ι → F₂) 0 = 0 := by
      classical
      ext u v
      simp [deviationMatrix, activity]
    constructor <;> intro b <;> simp [wordAction, selections, hz, dev]
  | cons factor tail ih =>
    obtain ⟨r, isZ⟩ := factor
    simp only [selections, deviation_add]
    exact (slot_transports p r isZ).comp ih

theorem signedWord_transports (negative : Bool) (p : F₂) (word : List (ι × Bool)) :
    Transports p (signedWord negative p word)
      (deviationMatrix (selections false word) (selections true word)) := by
  cases negative
  · exact word_transports p word
  · exact (word_transports p word).neg

/-- The class of `(h - 1)b` in `A/2B`. -/
noncomputable def mapBToA (negative : Bool) (word : List (ι × Bool)) :
    ParityQuotient ι 0 →ₗ[ℤ] ParityQuotient ι 1 :=
  quotientMap (signedWord_transports negative 0 word)

/-- The class of `(h - 1)a/2` in `B/A`. -/
noncomputable def mapAToB (negative : Bool) (word : List (ι × Bool)) :
    ParityQuotient ι 1 →ₗ[ℤ] ParityQuotient ι 0 := by
  have h : (1 : F₂) + 1 = 0 := by decide
  exact h ▸ quotientMap (signedWord_transports negative 1 word)

private theorem slot_embed (r : ι) (isZ : Bool) (a : Coeff ι) :
    slot 0 r isZ (embed 0 a) = embed 0 (slot 1 r isZ a) := by
  funext v
  have hf : parity (flip v r) = 0 ↔ parity v ≠ 0 := by
    rw [parity_flip, toggle]
  change embed 0 a v + slotDev 0 r isZ (embed 0 a) v =
    (if parity v = 0 then 2 else 1) * (a v + slotDev 1 r isZ a v)
  by_cases hp : parity v = 0 <;> by_cases hd : v r = isZ <;>
    by_cases hs : flip v r r = isZ <;>
    simp [slotDev_apply, embed, hp, hf, eq_one_iff, hd, hs] <;> ring

private theorem word_embed (word : List (ι × Bool)) (a : Coeff ι) :
    wordAction 0 word (embed 0 a) = embed 0 (wordAction 1 word a) := by
  induction word generalizing a with
  | nil => rfl
  | cons factor tail ih =>
    obtain ⟨r, isZ⟩ := factor
    change wordAction 0 tail (slot 0 r isZ (embed 0 a)) =
      embed 0 (wordAction 1 tail (slot 1 r isZ a))
    rw [slot_embed, ih]

/-- Both transport equations in the coordinates of `B`. The variable `a`
uses the scaled basis of `A`, so its `B` coordinate vector is
`embed 0 a`. The vector `c` is exactly half of the second deviation. -/
theorem signedWord_transport_in_B (negative : Bool) (word : List (ι × Bool)) (b a : Coeff ι) :
    let g := signedWord negative 0 word
    let M := deviationMatrix (selections false word) (selections true word)
    (dev g b ∈ parityLattice 0 ∧ reduce 1 (dev g b) = reduce 0 b ᵥ* M) ∧
      ∃ c : Coeff ι, dev g (embed 0 a) = (2 : ℤ) • c ∧ reduce 0 c = reduce 1 a ᵥ* M := by
  dsimp only
  let g := signedWord negative 0 word
  let h := signedWord negative 1 word
  have hg := signedWord_transports negative 0 word
  have hh := signedWord_transports negative 1 word
  refine ⟨⟨hg.lands b, by simpa only [zero_add] using hg.sparse b⟩, ?_⟩
  have hm : dev h a ∈ parityLattice 1 := hh.lands a
  obtain ⟨c, hc⟩ := (mem_parityLattice_iff_exists_embed 1 (dev h a)).mp hm
  have he (x : Coeff ι) : g (embed 0 x) = embed 0 (h x) := by
    cases negative with
    | false => exact word_embed word x
    | true =>
      change -(wordAction 0 word (embed 0 x)) = embed 0 (-(wordAction 1 word x))
      rw [word_embed]
      funext v
      simp [embed, mul_neg]
  have hdev : dev g (embed 0 a) = embed 0 (dev h a) := by
    funext v
    change g (embed 0 a) v - embed 0 a v = embed 0 (dev h a) v
    rw [he]
    simp [embed, dev, LinearMap.id_apply, mul_sub]
  refine ⟨c, by rw [hdev, ← hc, embed_twice], ?_⟩
  have hr : reduce 0 (embed 1 c) = reduce 0 c := by
    funext v
    by_cases hv : parity v = 0 <;> simp [hv, embed, eq_one_iff]
  have hs := hh.sparse a
  rw [show (1 : F₂) + 1 = 0 by decide] at hs
  change reduce 0 (dev h a) = _ at hs
  rwa [← hc, hr] at hs

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.TailPauliQuotientMaps
