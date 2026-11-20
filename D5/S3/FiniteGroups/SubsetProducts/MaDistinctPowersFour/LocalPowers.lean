/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LocalPowers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Power separation within generator classes of size two, three or four. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.SourceClaim
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderThree
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.ModularBlock

namespace D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour

/-- The order-four classification, at the universe needed by the registered claim. -/
def OrderFourObstruction : Prop :=
  ∀ {α : Type} (B : Fin 4 → Fin 4 → α), MaLatin.Latin B →
    MaLatin.Rainbow B ∨ MaLatin.EqualColumns B ∨ MaLatin.Motif B

section Group

variable {G : Type*} [Group G] [Finite G]

private theorem prime_gt {n p : ℕ} (h : noSmallOrders n G)
    (x : G) (hp : p.Prime) (hd : p ∣ orderOf x) : n + 1 < p := by
  by_contra! hle
  exact h (x ^ (orderOf x / p)) p hp.two_le hle
    (orderOf_pow_orderOf_div (orderOf_pos x).ne' hd)

private theorem coprime_of_bound {n k : ℕ} (h : noSmallOrders n G)
    (x : G) (hk : 0 < k) (hle : k ≤ n + 1) : k.Coprime (orderOf x) := by
  by_contra hh
  obtain ⟨p, hp, hpk, hpx⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
  exact (not_lt_of_ge ((Nat.le_of_dvd hk hpk).trans hle)) (prime_gt h x hp hpx)

theorem zpowers_pow_of_bound {n k : ℕ} (h : noSmallOrders n G)
    (x : G) (hk : 0 < k) (hle : k ≤ n) :
    Subgroup.zpowers (x ^ k) = Subgroup.zpowers x := by
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers x k)
  · exact Subgroup.zpowers_le.mpr (mem_zpowers_pow_iff.mpr
      (coprime_of_bound h x hk (by omega)))

/-- Any generator of the trivial subgroup is the identity, so a class with
two distinct generators has order greater than one. -/
private theorem order_gt_one_of_distinct_generators {x y : G}
    (hne : x ≠ y) (h : Subgroup.zpowers x = Subgroup.zpowers y) : 1 < orderOf x := by
  have hpos := orderOf_pos x
  by_contra! hle
  have hx : x = 1 := orderOf_eq_one_iff.mp (by omega)
  have hy : y = 1 :=
    Subgroup.zpowers_eq_bot.mp (h.symm.trans (Subgroup.zpowers_eq_bot.mpr hx))
  exact hne (hx.trans hy.symm)

/-- If both assignments of the endpoint pair collide, the order divides
the positive product of the sum and difference of the exponents. -/
private theorem endpoint_pair {n r s : ℕ} (h : noSmallOrders n G) (hr : 0 < r)
    (hrs : r < s) (hsum : r + s = n + 1) {x y : G}
    (hne : x ≠ y) (hz : Subgroup.zpowers x = Subgroup.zpowers y) :
    x ^ r ≠ y ^ s ∨ y ^ r ≠ x ^ s := by
  by_contra! hf
  have hpow : x ^ (r * r) = x ^ (s * s) := by
    rw [pow_mul, pow_mul, hf.1, ← hf.2]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm s r]
  have hle : r * r ≤ s * s := Nat.mul_le_mul (by omega) (by omega)
  have hd : orderOf x ∣ s * s - r * r :=
    (Nat.modEq_iff_dvd' hle).mp (pow_eq_pow_iff_modEq.mp hpow)
  have hm := order_gt_one_of_distinct_generators hne hz
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (by omega : orderOf x ≠ 1)
  have hlarge := prime_gt h x hp hpx
  have hfactor : s * s - r * r = (s - r) * (s + r) := by
    rw [Nat.sub_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm r s]
    omega
  rw [hfactor] at hd
  rcases hp.dvd_mul.mp (hpx.trans hd) with hdiff | hsum'
  · have := Nat.le_of_dvd (by omega : 0 < s - r) hdiff
    omega
  · have := Nat.le_of_dvd (by omega : 0 < s + r) hsum'
    omega

private theorem exists_coprime_pow {x g : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers g) :
    ∃ v : ℕ, g ^ v = x ∧ v.Coprime (orderOf g) := by
  have hx : x ∈ Subgroup.zpowers g := h ▸ Subgroup.mem_zpowers x
  obtain ⟨v, hv⟩ := mem_powers_iff_mem_zpowers.mpr hx
  change g ^ v = x at hv
  refine ⟨v, hv, mem_zpowers_pow_iff.mp ?_⟩
  rw [hv, h]
  exact Subgroup.mem_zpowers g

/-- Coordinates of distinct generators in the full cyclic group of order `orderOf g`. -/
private theorem cyclic_coordinates {ι : Type*} (g : G) (x : ι → G)
    (hinj : Function.Injective x)
    (hz : ∀ i, Subgroup.zpowers (x i) = Subgroup.zpowers g) :
    ∃ u : ι → (ZMod (orderOf g))ˣ, Function.Injective u ∧
      ∀ (i j : ι) (a b : ℕ), x i ^ a = x j ^ b ↔
        (a : ZMod (orderOf g)) * (u i : ZMod (orderOf g)) =
          (b : ZMod (orderOf g)) * (u j : ZMod (orderOf g)) := by
  choose v hv hcop using fun i => exists_coprime_pow (hz i)
  let u (i : ι) := ZMod.unitOfCoprime (v i) (hcop i)
  refine ⟨u, ?_, ?_⟩
  · intro i j hh
    apply hinj
    rw [← hv i, ← hv j, pow_eq_pow_iff_modEq]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [u, ZMod.coe_unitOfCoprime] using congrArg Units.val hh
  · intro i j a b
    rw [← hv i, ← hv j, ← pow_mul, ← pow_mul, pow_eq_pow_iff_modEq,
      ← ZMod.natCast_eq_natCast_iff]
    simp only [u, ZMod.coe_unitOfCoprime, Nat.cast_mul, mul_comm]

/-- Three consecutive in-range exponents give an injective sequence in full-modulus
coordinates by the order-three Latin-array theorem. -/
private theorem threeBlock (m n r : ℕ)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ m → n + 1 < p)
    (hm : 1 < m) (hr : 0 < r) (hrn : r + 2 ≤ n)
    (u : Fin 3 → (ZMod m)ˣ) (hu : Function.Injective u) :
    ∃ π : Equiv.Perm (Fin 3), Function.Injective
      (fun i : Fin 3 => ((r + i.val : ℕ) : ZMod m) * (u (π i) : ZMod m)) := by
  have hcop (i : Fin 3) : Nat.Coprime (r + i.val) m := by
    have hi := i.isLt
    by_contra h
    obtain ⟨p, hp, hpi, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hle := Nat.le_of_dvd (by omega : 0 < r + i.val) hpi
    have := hprime p hp hpm
    omega
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hlarge := hprime p hp hd
  have hpm := Nat.le_of_dvd (by omega : 0 < m) hd
  let b (i : Fin 3) := ZMod.unitOfCoprime (r + i.val) (hcop i)
  have hb : Function.Injective b := by
    intro i j hij
    have h := congrArg Units.val hij
    simp only [b, ZMod.coe_unitOfCoprime, ZMod.natCast_eq_natCast_iff'] at h
    have hi := i.isLt
    have hj := j.isLt
    rw [Nat.mod_eq_of_lt (by omega : r + i.val < m),
      Nat.mod_eq_of_lt (by omega : r + j.val < m)] at h
    exact Fin.ext (by omega)
  obtain ⟨π, hπ⟩ := MaLatin.orderThree _ (MaLatin.productLatin b u hb hu)
  refine ⟨π, fun i j h => hπ (Units.val_injective ?_)⟩
  simpa only [Units.val_mul, b, ZMod.coe_unitOfCoprime] using h

/-- A class of two is arranged using the assigned endpoint exponents. -/
theorem arrange_pair {n r s : ℕ} (h : noSmallOrders n G) (hr : 0 < r)
    (hrs : r < s) (hsum : r + s = n + 1) (k : Fin 2 → ℕ)
    (hk₀ : k 0 = r) (hk₁ : k 1 = s) (x : Fin 2 → G)
    (hinj : Function.Injective x) (hz : ∀ i j, Subgroup.zpowers (x i) = Subgroup.zpowers (x j)) :
    ∃ π : Equiv.Perm (Fin 2), Function.Injective (fun i : Fin 2 => x (π i) ^ k i) := by
  have hne : x 0 ≠ x 1 := fun he => (by decide : (0 : Fin 2) ≠ 1) (hinj he)
  rcases endpoint_pair h hr hrs hsum hne (hz 0 1) with hgood | hgood
  · refine ⟨Equiv.refl _, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm hgood]
  · refine ⟨Equiv.swap 0 1, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Equiv.swap_apply_left, Equiv.swap_apply_right, Ne.symm hgood]

/-- The hypotheses on the actual generators produce the full-modulus three-block assignment. -/
theorem arrange_triple {n r : ℕ} (h : noSmallOrders n G)
    (hr : 0 < r) (hrn : r + 2 ≤ n) (x : Fin 3 → G) (hinj : Function.Injective x)
    (hz : ∀ i j, Subgroup.zpowers (x i) = Subgroup.zpowers (x j)) :
    ∃ π : Equiv.Perm (Fin 3), Function.Injective (fun i : Fin 3 => x (π i) ^ (r + i.val)) := by
  have hne : x 0 ≠ x 1 := fun he => (by decide : (0 : Fin 3) ≠ 1) (hinj he)
  let g := x 0
  obtain ⟨u, hu, he⟩ := cyclic_coordinates g x hinj (fun i => hz i 0)
  obtain ⟨π, hπ⟩ :=
    threeBlock (orderOf g) n r (fun _ hp hd => prime_gt h g hp hd)
      (order_gt_one_of_distinct_generators hne (hz 0 1)) hr hrn u hu
  exact ⟨π, fun i j hp => hπ ((he (π i) (π j) _ _).mp hp)⟩

end Group

/-- The conditional four-block assignment for actual generators in an arbitrary finite group. -/
theorem arrange_four {G : Type} [Group G] [Finite G] (classify : OrderFourObstruction)
    {n r : ℕ} (h : noSmallOrders n G)
    (hr : 0 < r) (hrn : r + 3 ≤ n) (x : Fin 4 → G) (hinj : Function.Injective x)
    (hz : ∀ i j, Subgroup.zpowers (x i) = Subgroup.zpowers (x j)) :
    ∃ π : Equiv.Perm (Fin 4), Function.Injective (fun i : Fin 4 => x (π i) ^ (r + i.val)) := by
  have hne : x 0 ≠ x 1 := fun he => (by decide : (0 : Fin 4) ≠ 1) (hinj he)
  let g := x 0
  obtain ⟨u, hu, he⟩ := cyclic_coordinates g x hinj (fun i => hz i 0)
  obtain ⟨π, hπ⟩ :=
    MaLatin.fourBlock_of_orderFour (orderOf g) classify n r
      (order_gt_one_of_distinct_generators hne (hz 0 1))
      (fun _ hp hd => prime_gt h g hp hd) hr hrn u hu
  exact ⟨π, fun i j hp => hπ ((he (π i) (π j) _ _).mp hp)⟩

end D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour
