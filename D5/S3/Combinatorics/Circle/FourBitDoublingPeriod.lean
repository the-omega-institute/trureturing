/- GID: D5/S3/Combinatorics/Circle/FourBitDoublingPeriod
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourBitDoublingPeriod
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Dynamics.PeriodicPts.Defs,
     mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Primitive gap blocks determine actual four-bit doubling periods. -/
import D5.S3.Combinatorics.Circle.NarrowDoublingOrbit
import D5.S3.Combinatorics.Circle.ZeroSumSubsets

/-!
# Four-gap periods of doubling

Binary support translation detects returns without cancellation of the seed.
Inverse occupied-prefix rotations compare increasing four-point sets and force
one, two or four entries in the primitive directed gap block. Its sum is the
actual Function.minimalPeriod, and its multiples are exactly all natural returns.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourBitDoublingPeriod

open D5.S1.Words.AssociatedMersenne.CircularWords
open D5.S3.Combinatorics.Circle.ZeroSumSubsets (mask)
open scoped BigOperators

private def raw (a b c : ℕ) : Finset ℕ := {0, a, a + b, a + b + c}

private def pack {r : ℕ} (T : Finset ℕ) : Finset (Fin r) :=
  Finset.univ.filter (fun i => i.val ∈ T)

private def turn {r : ℕ} (h : ℕ) (i : Fin r) : Fin r := cycAdd i h

private def rot {r : ℕ} (h : ℕ) (A : Finset (Fin r)) : Finset (Fin r) :=
  A.image (turn h)

private theorem turn_injective {r : ℕ} (h : ℕ) :
    Function.Injective (@turn r h) := by
  intro i j he
  let t : Fin r := ⟨h % r, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
  have hc (k : Fin r) : turn h k = cycAdd t k.val := by
    apply Fin.ext
    simp only [turn, cycAdd_val]
    change (k.val + h) % r = (h % r + k.val) % r
    rw [Nat.mod_add_mod, Nat.add_comm]
  apply (cycAdd_bijective t).1
  change cycAdd t i.val = cycAdd t j.val
  rw [← hc i, ← hc j]
  exact he

private theorem rot_comp {r : ℕ} (A : Finset (Fin r)) (h k : ℕ) :
    rot k (rot h A) = rot (h + k) A := by
  simp only [rot, Finset.image_image, Function.comp_def]
  congr 1
  funext i
  exact cycAdd_assoc i h k

private theorem rot_full {r : ℕ} (A : Finset (Fin r)) : rot r A = A := by
  have ht (i : Fin r) : turn r i = i := by
    apply Fin.ext
    simp only [turn, cycAdd_val, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  have hfun : (turn r : Fin r → Fin r) = id := funext ht
  unfold rot
  rw [hfun, Finset.image_id]

private theorem inverse_stabilizer {r : ℕ} (A : Finset (Fin r))
    {t : ℕ} (ht : t ≤ r) : rot t A = A ↔ rot (r - t) A = A := by
  have hleft : t + (r - t) = r := by omega
  have hright : r - t + t = r := by omega
  constructor
  · intro he
    calc
      rot (r - t) A = rot (r - t) (rot t A) := congrArg (rot (r - t)) he.symm
      _ = A := by rw [rot_comp, hleft, rot_full]
  · intro he
    calc
      rot t A = rot t (rot (r - t) A) := congrArg (rot t) he.symm
      _ = A := by rw [rot_comp, hright, rot_full]

private theorem pack_values {r : ℕ} (T : Finset ℕ)
    (hT : ∀ n ∈ T, n < r) : (pack (r := r) T).image Fin.val = T := by
  ext n
  constructor
  · rintro hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    simpa only [pack, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro hn
    exact Finset.mem_image.mpr ⟨⟨n, hT n hn⟩, by simp [pack, hn], rfl⟩

private theorem values_injective {r : ℕ} :
    Function.Injective (fun A : Finset (Fin r) => A.image Fin.val) :=
  Finset.image_injective Fin.val_injective

private theorem rot_values {r : ℕ} (T : Finset ℕ)
    (hT : ∀ n ∈ T, n < r) (h : ℕ) :
    (rot h (pack (r := r) T)).image Fin.val = T.image (fun n => (n + h) % r) := by
  calc
    (rot h (pack (r := r) T)).image Fin.val =
        ((pack (r := r) T).image Fin.val).image (fun n => (n + h) % r) := by
      simp only [rot, Finset.image_image, Function.comp_def, turn, cycAdd_val]
    _ = _ := by rw [pack_values T hT]

private theorem mask_values {r : ℕ} (A : Finset (Fin r)) :
    mask A = ∑ n ∈ A.image Fin.val, 2 ^ n := by
  rw [Finset.sum_image]
  · rfl
  · intro i _ j _ he
    exact Fin.ext he

private theorem mask_injective {r : ℕ} : Function.Injective (@mask r) := by
  intro A B he
  apply values_injective
  apply Finset.geomSum_injective (by decide : 2 ≤ (2 : ℕ))
  simpa only [mask_values] using he

private theorem mask_lt_mersenne {r : ℕ} (A : Finset (Fin r))
    (hproper : ∃ i : Fin r, i ∉ A) : mask A < 2 ^ r - 1 := by
  obtain ⟨i, hi⟩ := hproper
  have hb : mask (insert i A) < 2 ^ r := by
    rw [mask_values]
    apply Nat.geomSum_lt (by decide : 2 ≤ (2 : ℕ))
    intro n hn
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hn
    exact j.isLt
  have hs : mask (insert i A) = 2 ^ i.val + mask A := by
    exact Finset.sum_insert hi
  have hp : 0 < (2 : ℕ) ^ i.val := pow_pos (by decide) _
  omega

private theorem rot_proper {r : ℕ} (A : Finset (Fin r)) (h : ℕ)
    (hproper : ∃ i : Fin r, i ∉ A) : ∃ i : Fin r, i ∉ rot h A := by
  obtain ⟨i, hi⟩ := hproper
  refine ⟨turn h i, ?_⟩
  intro hm
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hm
  have hji : j = i := turn_injective h he
  exact hi (hji ▸ hj)

private theorem two_pow_length (r : ℕ) :
    (2 : ZMod (2 ^ r - 1)) ^ r = 1 := by
  have hp : 0 < (2 : ℕ) ^ r := pow_pos (by decide) _
  have hn : (2 ^ r - 1) + 1 = (2 : ℕ) ^ r := by omega
  have hc := congrArg (fun n : ℕ => (n : ZMod (2 ^ r - 1))) hn
  simpa only [Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add,
    Nat.cast_pow, Nat.cast_ofNat] using hc.symm

private theorem rot_mask_cast {r : ℕ} (A : Finset (Fin r)) (h : ℕ) :
    (mask (rot h A) : ZMod (2 ^ r - 1)) =
      (2 : ZMod (2 ^ r - 1)) ^ h * (mask A : ZMod (2 ^ r - 1)) := by
  have hpow (i : Fin r) :
      (2 : ZMod (2 ^ r - 1)) ^ (turn h i).val =
        (2 : ZMod (2 ^ r - 1)) ^ h * 2 ^ i.val := by
    calc
      (2 : ZMod (2 ^ r - 1)) ^ (turn h i).val = 2 ^ (i.val + h) := by
        apply pow_eq_pow_of_modEq _ (two_pow_length r)
        change ((i.val + h) % r) % r = (i.val + h) % r
        exact Nat.mod_mod _ _
      _ = _ := by rw [pow_add, mul_comm]
  simp only [mask, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat, rot]
  rw [Finset.sum_image]
  · simp_rw [hpow]
    rw [Finset.mul_sum]
  · intro i _ j _ he
    exact turn_injective h he

private theorem periodic_iff_support {r : ℕ}
    (A : Finset (Fin r)) (hproper : ∃ i : Fin r, i ∉ A) (h : ℕ) :
    Function.IsPeriodicPt (fun z : ZMod (2 ^ r - 1) => 2 * z) h
      (mask A : ZMod (2 ^ r - 1)) ↔ rot h A = A := by
  have hb := mask_lt_mersenne A hproper
  have hbr := mask_lt_mersenne (rot h A) (rot_proper A h hproper)
  change (fun z : ZMod (2 ^ r - 1) => 2 * z)^[h] (mask A : ZMod (2 ^ r - 1)) =
    (mask A : ZMod (2 ^ r - 1)) ↔ _
  rw [mul_left_iterate_apply, ← rot_mask_cast A h,
    ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hbr, Nat.mod_eq_of_lt hb]
  exact mask_injective.eq_iff

private theorem residue_iff_periodic {M Q : ℕ} (hQ : Q < M) (h : ℕ) :
    NarrowDoublingOrbit.residue M Q h = Q ↔
      Function.IsPeriodicPt (fun z : ZMod M => 2 * z) h (Q : ZMod M) := by
  change (2 ^ h * Q) % M = Q ↔
    (fun z : ZMod M => 2 * z)^[h] (Q : ZMod M) = (Q : ZMod M)
  rw [mul_left_iterate_apply]
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.mod_eq_of_lt hQ] using
    (ZMod.natCast_eq_natCast_iff' (2 ^ h * Q) Q M).symm

/- Increasing positive prefix lists determine their three displayed gaps. -/
private theorem raw_eq_iff {a b c e f g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : 0 < e) (hf : 0 < f) (hg : 0 < g) :
    raw a b c = raw e f g ↔ a = e ∧ b = f ∧ c = g := by
  constructor
  · intro h
    have h₁ : a ∈ raw e f g := h ▸ (by simp [raw] : a ∈ raw a b c)
    have h₂ : e ∈ raw a b c := h.symm ▸ (by simp [raw] : e ∈ raw e f g)
    simp only [raw, Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
    have hae : a = e := by omega
    have h₃ : a + b ∈ raw e f g := h ▸ (by simp [raw] : a + b ∈ raw a b c)
    have h₄ : e + f ∈ raw a b c := h.symm ▸ (by simp [raw] : e + f ∈ raw e f g)
    simp only [raw, Finset.mem_insert, Finset.mem_singleton] at h₃ h₄
    have hbf : b = f := by omega
    have h₅ : a + b + c ∈ raw e f g :=
      h ▸ (by simp [raw] : a + b + c ∈ raw a b c)
    have h₆ : e + f + g ∈ raw a b c :=
      h.symm ▸ (by simp [raw] : e + f + g ∈ raw e f g)
    simp only [raw, Finset.mem_insert, Finset.mem_singleton] at h₅ h₆
    exact ⟨hae, hbf, by omega⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/- These are rotations by negative occupied prefixes, with all modular
branches proved from positivity. They preserve the directed order. -/
private theorem raw_rotate_one {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (raw a b c).image (fun n => (n + (a + b + c + d - a)) % (a + b + c + d)) =
      raw b c d := by
  let r := a + b + c + d
  have e₀ : (0 + (r - a)) % r = b + c + d := by
    rw [show 0 + (r - a) = b + c + d by dsimp [r]; omega]
    exact Nat.mod_eq_of_lt (by dsimp [r]; omega)
  have e₁ : (a + (r - a)) % r = 0 := by
    rw [show a + (r - a) = r by dsimp [r]; omega, Nat.mod_self]
  have e₂ : (a + b + (r - a)) % r = b := by
    rw [show a + b + (r - a) = b + r by dsimp [r]; omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by dsimp [r]; omega)
  have e₃ : (a + b + c + (r - a)) % r = b + c := by
    rw [show a + b + c + (r - a) = (b + c) + r by dsimp [r]; omega,
      Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by dsimp [r]; omega)
  change (raw a b c).image (fun n => (n + (r - a)) % r) = raw b c d
  simp only [raw, Finset.image_insert, Finset.image_singleton, e₀, e₁, e₂, e₃]
  ext n
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem raw_rotate_two {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (raw a b c).image (fun n => (n + (a + b + c + d - (a + b))) % (a + b + c + d)) =
      raw c d a := by
  let r := a + b + c + d
  have e₀ : (0 + (r - (a + b))) % r = c + d := by
    rw [show 0 + (r - (a + b)) = c + d by dsimp [r]; omega]
    exact Nat.mod_eq_of_lt (by dsimp [r]; omega)
  have e₁ : (a + (r - (a + b))) % r = c + d + a := by
    rw [show a + (r - (a + b)) = c + d + a by dsimp [r]; omega]
    exact Nat.mod_eq_of_lt (by dsimp [r]; omega)
  have e₂ : (a + b + (r - (a + b))) % r = 0 := by
    rw [show a + b + (r - (a + b)) = r by dsimp [r]; omega, Nat.mod_self]
  have e₃ : (a + b + c + (r - (a + b))) % r = c := by
    rw [show a + b + c + (r - (a + b)) = c + r by dsimp [r]; omega,
      Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by dsimp [r]; omega)
  change (raw a b c).image (fun n => (n + (r - (a + b))) % r) = raw c d a
  simp only [raw, Finset.image_insert, Finset.image_singleton, e₀, e₁, e₂, e₃]
  ext n
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem raw_rotate_three {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (raw a b c).image (fun n => (n + (a + b + c + d - (a + b + c))) % (a + b + c + d)) =
      raw d a b := by
  let r := a + b + c + d
  have e₀ : (0 + (r - (a + b + c))) % r = d := by
    rw [show 0 + (r - (a + b + c)) = d by dsimp [r]; omega]
    exact Nat.mod_eq_of_lt (by dsimp [r]; omega)
  have e₁ : (a + (r - (a + b + c))) % r = d + a := by
    rw [show a + (r - (a + b + c)) = d + a by dsimp [r]; omega]
    exact Nat.mod_eq_of_lt (by dsimp [r]; omega)
  have e₂ : (a + b + (r - (a + b + c))) % r = d + a + b := by
    rw [show a + b + (r - (a + b + c)) = d + a + b by dsimp [r]; omega]
    exact Nat.mod_eq_of_lt (by dsimp [r]; omega)
  have e₃ : (a + b + c + (r - (a + b + c))) % r = 0 := by
    rw [show a + b + c + (r - (a + b + c)) = r by dsimp [r]; omega, Nat.mod_self]
  change (raw a b c).image (fun n => (n + (r - (a + b + c))) % r) = raw d a b
  simp only [raw, Finset.image_insert, Finset.image_singleton, e₀, e₁, e₂, e₃]
  ext n
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem prefix_stabilizers {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    let A := pack (r := a + b + c + d) (raw a b c)
    (rot a A = A ↔ a = b ∧ b = c ∧ c = d) ∧
    (rot (a + b) A = A ↔ a = c ∧ b = d) ∧
    (rot (a + b + c) A = A ↔ a = b ∧ b = c ∧ c = d) := by
  let r := a + b + c + d
  let A := pack (r := r) (raw a b c)
  have hT : ∀ n ∈ raw a b c, n < r := by
    intro n hn
    simp only [raw, Finset.mem_insert, Finset.mem_singleton] at hn
    dsimp [r]
    omega
  have key (t : ℕ) (ht : t ≤ r) : rot t A = A ↔
      (raw a b c).image (fun n => (n + (r - t)) % r) = raw a b c := by
    calc
      rot t A = A ↔ rot (r - t) A = A := inverse_stabilizer A ht
      _ ↔ (rot (r - t) A).image Fin.val = A.image Fin.val :=
        (values_injective.eq_iff).symm
      _ ↔ _ := by
        rw [rot_values (raw a b c) hT, pack_values (raw a b c) hT]
  change (rot a A = A ↔ _) ∧ (rot (a + b) A = A ↔ _) ∧
    (rot (a + b + c) A = A ↔ _)
  constructor
  · rw [key a (by dsimp [r]; omega), raw_rotate_one ha hb hc hd,
      raw_eq_iff hb hc hd ha hb hc]
    omega
  · constructor
    · rw [key (a + b) (by dsimp [r]; omega), raw_rotate_two ha hb hc hd,
        raw_eq_iff hc hd ha ha hb hc]
      omega
    · rw [key (a + b + c) (by dsimp [r]; omega), raw_rotate_three ha hb hc hd,
        raw_eq_iff hd ha hb ha hb hc]
      omega

private theorem bounded_stabilizer {a b c d h : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hh : h < a + b + c + d)
    (hs : rot h (pack (r := a + b + c + d) (raw a b c)) =
      pack (r := a + b + c + d) (raw a b c)) :
    h = 0 ∨
    (h = a ∧ a = b ∧ b = c ∧ c = d) ∨
    (h = a + b ∧ a = c ∧ b = d) ∨
    (h = a + b + c ∧ a = b ∧ b = c ∧ c = d) := by
  let r := a + b + c + d
  let A := pack (r := r) (raw a b c)
  let z : Fin r := ⟨0, by dsimp [r]; omega⟩
  have hz : z ∈ A := by simp [A, pack, z, raw]
  change rot h A = A at hs
  have hm : turn h z ∈ A := hs ▸ Finset.mem_image_of_mem (turn h) hz
  have hhr : h < r := hh
  have hv : h ∈ raw a b c := by
    have hv' : (turn h z).val ∈ raw a b c := by
      simpa only [A, pack, Finset.mem_filter, Finset.mem_univ, true_and] using hm
    simpa only [turn, cycAdd_val, z, zero_add, Nat.mod_eq_of_lt hhr] using hv'
  obtain ⟨h₁, h₂, h₃⟩ := prefix_stabilizers ha hb hc hd
  simp only [raw, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h0 | h1 | h2 | h3
  · exact Or.inl h0
  · exact Or.inr (Or.inl ⟨h1, h₁.mp (by simpa only [h1] using hs)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h2, h₂.mp (by simpa only [h2] using hs)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h3, h₃.mp (by simpa only [h3] using hs)⟩))

/-- The exact actual least dynamical period and all natural return exponents
of a four-bit seed, including nonunit seeds and all four gaps at least two.
The period is the sum of a primitive block of the directed gap word. -/
theorem four_gap_actual_period (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) :
    let r := a + b + c + d
    let M := 2 ^ r - 1
    let Q := 1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)
    let p := if a = b ∧ b = c ∧ c = d then a
      else if a = c ∧ b = d then a + b else r
    NarrowDoublingOrbit.period M Q = p ∧
      ∀ h : ℕ, (NarrowDoublingOrbit.residue M Q h = Q ↔ p ∣ h) := by
  classical
  let r := a + b + c + d
  let M := 2 ^ r - 1
  let Q := 1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)
  let p := if a = b ∧ b = c ∧ c = d then a
    else if a = c ∧ b = d then a + b else r
  let A := pack (r := r) (raw a b c)
  have hap : 0 < a := by omega
  have hbp : 0 < b := by omega
  have hcp : 0 < c := by omega
  have hdp : 0 < d := by omega
  have hT : ∀ n ∈ raw a b c, n < r := by
    intro n hn
    simp only [raw, Finset.mem_insert, Finset.mem_singleton] at hn
    dsimp [r]
    omega
  have hproper : ∃ i : Fin r, i ∉ A := by
    refine ⟨⟨1, by dsimp [r]; omega⟩, ?_⟩
    simp only [A, pack, Finset.mem_filter, Finset.mem_univ, true_and,
      raw, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hmask : mask A = Q := by
    rw [mask_values, pack_values (raw a b c) hT]
    have e0 : (0 : ℕ) ∉ ({a, a + b, a + b + c} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have e1 : a ∉ ({a + b, a + b + c} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have e2 : a + b ∉ ({a + b + c} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      omega
    change (∑ n ∈ raw a b c, 2 ^ n) = Q
    rw [raw, Finset.sum_insert e0, Finset.sum_insert e1,
      Finset.sum_insert e2, Finset.sum_singleton]
    simp only [pow_zero, Q]
    omega
  have hQ : Q < M := by
    rw [← hmask]
    exact mask_lt_mersenne A hproper
  have bridge (h : ℕ) :
      Function.IsPeriodicPt (fun z : ZMod M => 2 * z) h (Q : ZMod M) ↔ rot h A = A := by
    simpa only [hmask] using periodic_iff_support A hproper h
  obtain ⟨h₁, h₂, _⟩ := prefix_stabilizers hap hbp hcp hdp
  have hp : 0 < p := by
    have hr : 0 < r := by dsimp [r]; omega
    dsimp [p]
    split_ifs <;> omega
  have hper : Function.IsPeriodicPt (fun z : ZMod M => 2 * z) p (Q : ZMod M) := by
    apply (bridge p).mpr
    dsimp [p]
    split_ifs with he halt
    · exact h₁.mpr he
    · exact h₂.mpr halt
    · exact rot_full A
  have hnpos : 0 < NarrowDoublingOrbit.period M Q := hper.minimalPeriod_pos hp
  have hnle : NarrowDoublingOrbit.period M Q ≤ p := hper.minimalPeriod_le hp
  have hnret : rot (NarrowDoublingOrbit.period M Q) A = A := by
    apply (bridge _).mp
    exact Function.isPeriodicPt_minimalPeriod _ _
  have hnsmall (hlt : NarrowDoublingOrbit.period M Q < r) :=
    bounded_stabilizer hap hbp hcp hdp hlt hnret
  have heq : NarrowDoublingOrbit.period M Q = p := by
    by_cases he : a = b ∧ b = c ∧ c = d
    · have hpa : p = a := by simp only [p, ite_eq_left he]
      have hlt : NarrowDoublingOrbit.period M Q < r := by dsimp [r]; omega
      have hclass := hnsmall hlt
      omega
    · by_cases halt : a = c ∧ b = d
      · have hpab : p = a + b := by simp only [p, ite_eq_right he, ite_eq_left halt]
        have hlt : NarrowDoublingOrbit.period M Q < r := by dsimp [r]; omega
        have hclass := hnsmall hlt
        omega
      · have hpr : p = r := by simp only [p, ite_eq_right he, ite_eq_right halt]
        by_contra hne
        have hlt : NarrowDoublingOrbit.period M Q < r := by omega
        have hclass := hnsmall hlt
        omega
  change NarrowDoublingOrbit.period M Q = p ∧ _
  refine ⟨heq, ?_⟩
  intro h
  rw [residue_iff_periodic hQ h, Function.isPeriodicPt_iff_minimalPeriod_dvd]
  change NarrowDoublingOrbit.period M Q ∣ h ↔ p ∣ h
  rw [heq]

#print axioms four_gap_actual_period
#check @four_gap_actual_period

end D5.S3.Combinatorics.Circle.FourBitDoublingPeriod
