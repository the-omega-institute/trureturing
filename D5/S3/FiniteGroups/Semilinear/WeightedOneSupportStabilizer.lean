/- GID: D5/S3/FiniteGroups/Semilinear/WeightedOneSupportStabilizer
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/Semilinear/WeightedOneSupportStabilizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/Semilinear/WeightedOneSupportStabilizer.splittingClaim; result=D5/S3/FiniteGroups/Semilinear/WeightedOneSupportStabilizer.result; claim=D5/S3/FiniteGroups/Semilinear/WeightedOneSupportStabilizer.splittingClaim
   digest: A native weighted stabilizer and its nonsplit Galois projection. -/

import D5.S3.FiniteGroups.Semilinear.WeightedOrbits
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! The scalar kernel of the Galois projection is different from the normal
order-seven factor in the internal semidirect product. All groups below are
subgroups of the existing weighted action on the full five-coordinate space. -/

set_option autoImplicit false

noncomputable section

open scoped Classical

namespace WeightedSemilinear.OneSupport63

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {K : Type} [Field K] [Fintype K] [Algebra (ZMod 5) K]

abbrev Ambient (K : Type) [Field K] [Fintype K] [Algebra (ZMod 5) K] :=
  WeightedSemilinear.Group (ZMod 5) K

def weights (i : Fin 5) : ℕ := 5 ^ (i.val + 1) - 5 + 1

/-- The primitive field element, converted using its proved nonvanishing. -/
def primitiveUnit (ζ : K) (hζ : IsPrimitiveRoot ζ 15624) : Kˣ :=
  Units.mk0 ζ (hζ.ne_zero (by decide))

def coefficients (z : Kˣ) (i : Fin 5) : K := if i = 1 then (z : K) ^ 7 else 0

local instance : MulAction (Ambient K) (Fin 5 → K) := weightedAction weights

def stabilizer (z : Kˣ) : Subgroup (Ambient K) :=
  MulAction.stabilizer (Ambient K) (coefficients z)

abbrev frob (K : Type) [Field K] [Fintype K] [Algebra (ZMod 5) K] :=
  FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 5) K

def alpha (z : Kˣ) : Ambient K := SemidirectProduct.inl (z ^ 744)
def tau (z : Kˣ) : Ambient K := ⟨z ^ 8, frob K ^ 2⟩
def beta (z : Kˣ) : Ambient K := alpha z ^ 3

private theorem frob_apply (n : ℕ) (x : K) : (frob K ^ n) x = x ^ (5 ^ n) := by
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  simp [ZMod.card]

private theorem frob_units (n : ℕ) (x : Kˣ) :
    unitsAut (ZMod 5) K (frob K ^ n) x = x ^ (5 ^ n) := by
  apply Units.ext
  exact frob_apply n (x : K)

private theorem finrank_eq (hK : Fintype.card K = 15625) :
    Module.finrank (ZMod 5) K = 6 := by
  apply Nat.pow_right_injective (by decide : 1 < 5)
  simpa [hK] using FiniteField.pow_finrank_eq_card 5 K

private theorem frob_order (hK : Fintype.card K = 15625) : orderOf (frob K) = 6 := by
  rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, finrank_eq hK]

private theorem frob_six (hK : Fintype.card K = 15625) : frob K ^ 6 = 1 := by
  rw [← frob_order hK]
  exact pow_orderOf_eq_one _

private theorem mem_stabilizer_iff (z : Kˣ) (g : Ambient K) :
    g ∈ stabilizer z ↔ (g.left : K) ^ 21 * (z : K) ^ 7 = g.right ((z : K) ^ 7) := by
  change act weights g (coefficients z) = coefficients z ↔ _
  constructor
  · intro h
    have hi := congrFun h (1 : Fin 5)
    have he : weights 1 = 21 := by decide
    simp only [act, coefficients, ite_true, he] at hi
    calc
      (g.left : K) ^ 21 * (z : K) ^ 7 =
          (g.left : K) ^ 21 * (((g.left⁻¹ : Kˣ) : K) ^ 21 *
            g.right ((z : K) ^ 7)) := by rw [hi]
      _ = g.right ((z : K) ^ 7) := by
        rw [← mul_assoc, ← mul_pow, ← Units.val_mul]
        simp
  · intro h
    funext i
    by_cases hi : i = 1
    · subst i
      change ((g.left⁻¹ : Kˣ) : K) ^ 21 * g.right ((z : K) ^ 7) = (z : K) ^ 7
      rw [← h, ← mul_assoc, ← mul_pow, ← Units.val_mul]
      simp
    · simp [act, coefficients, hi]

private theorem alpha_pow (z : Kˣ) (n : ℕ) :
    alpha z ^ n = SemidirectProduct.inl (z ^ (744 * n)) := by
  rw [alpha, ← map_pow, pow_mul]

private theorem alpha_mem (z : Kˣ) (hz : IsPrimitiveRoot z 15624) :
    alpha z ∈ stabilizer z := by
  rw [mem_stabilizer_iff]
  change ((z ^ 744 : Kˣ) : K) ^ 21 * (z : K) ^ 7 = (z : K) ^ 7
  have h : (z ^ 744) ^ 21 = 1 := by
    rw [← pow_mul]
    exact hz.pow_eq_one
  rw [← Units.val_pow_eq_pow_val, h]
  simp

private theorem tau_mem (z : Kˣ) : tau z ∈ stabilizer z := by
  rw [mem_stabilizer_iff]
  change ((z ^ 8 : Kˣ) : K) ^ 21 * (z : K) ^ 7 = (frob K ^ 2) ((z : K) ^ 7)
  rw [frob_apply]
  simp only [Units.val_pow_eq_pow_val, ← pow_mul, ← pow_add]
  rfl

private theorem beta_mem (z : Kˣ) (hz : IsPrimitiveRoot z 15624) :
    beta z ∈ stabilizer z := (stabilizer z).pow_mem (alpha_mem z hz) 3

private theorem alpha_order (z : Kˣ) (hz : IsPrimitiveRoot z 15624) :
    orderOf (alpha z) = 21 := by
  rw [alpha, orderOf_injective _ SemidirectProduct.inl_injective,
    orderOf_pow, ← hz.eq_orderOf]
  norm_num

private theorem beta_order (z : Kˣ) (hz : IsPrimitiveRoot z 15624) :
    orderOf (beta z) = 7 := by
  rw [beta, orderOf_pow, alpha_order z hz]
  norm_num

private theorem tau_cube (hK : Fintype.card K = 15625)
    (z : Kˣ) : tau z ^ 3 = alpha z ^ 7 := by
  apply SemidirectProduct.ext
  · rw [alpha_pow, pow_succ, pow_two]
    change (z ^ 8 * unitsAut (ZMod 5) K (frob K ^ 2) (z ^ 8)) *
      unitsAut (ZMod 5) K (frob K ^ 2 * frob K ^ 2) (z ^ 8) = z ^ (744 * 7)
    rw [← pow_add, frob_units, frob_units]
    simp only [← pow_mul, ← pow_add]
    rfl
  · change (SemidirectProduct.rightHom (tau z ^ 3)) = _
    rw [map_pow]
    change (frob K ^ 2) ^ 3 = (alpha z ^ 7).right
    rw [← pow_mul, alpha_pow, SemidirectProduct.right_inl]
    exact frob_six hK

private theorem tau_order (hK : Fintype.card K = 15625)
    (z : Kˣ) (hz : IsPrimitiveRoot z 15624) : orderOf (tau z) = 9 := by
  have hc : orderOf (tau z ^ 3) = 3 := by
    rw [tau_cube hK, orderOf_pow, alpha_order z hz]
    norm_num
  have hp : tau z ^ 9 = 1 := by
    rw [show 9 = 3 * 3 from rfl, pow_mul, tau_cube hK,
      ← pow_mul, show 7 * 3 = 21 from rfl, ← alpha_order z hz]
    exact pow_orderOf_eq_one _
  have hd := orderOf_dvd_of_pow_eq_one hp
  have he : orderOf (tau z) / Nat.gcd (orderOf (tau z)) 3 = 3 := by
    simpa only [orderOf_pow] using hc
  have hpos : 0 < orderOf (tau z) := orderOf_pos _
  have hle : orderOf (tau z) ≤ 9 := Nat.le_of_dvd (by decide) hd
  interval_cases h : orderOf (tau z) <;> norm_num at *

private theorem aut_power (hK : Fintype.card K = 15625) (s : Gal(K/ZMod 5)) :
    ∃ k : Fin 6, frob K ^ k.val = s := by
  obtain ⟨k, hk⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 5) K).surjective s
  exact ⟨⟨k.val, by simpa only [finrank_eq hK] using k.isLt⟩, hk⟩

private theorem fixed_equation (z : Kˣ) {g : Ambient K}
    (hg : g ∈ stabilizer z) {k : ℕ} (hk : g.right = frob K ^ k) :
    g.left ^ 21 * z ^ 7 = z ^ (7 * 5 ^ k) := by
  apply Units.ext
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, hk, frob_apply, ← pow_mul]
    using (mem_stabilizer_iff z g).mp hg

private theorem scalar_card_pow (hK : Fintype.card K = 15625) (c : Kˣ) :
    c ^ 15624 = 1 := by
  have hc : Fintype.card Kˣ = 15624 := by rw [Fintype.card_units, hK]
  rw [← hc]
  exact pow_card_eq_one

private theorem projection_mem (hK : Fintype.card K = 15625)
    (z : Kˣ) (hz : IsPrimitiveRoot z 15624) (g : stabilizer z) :
    g.val.right ∈ Subgroup.zpowers (frob K ^ 2) := by
  obtain ⟨k, hk⟩ := aut_power hK g.val.right
  have he := fixed_equation z g.property hk.symm
  have hp := congrArg (fun x : Kˣ => x ^ 744) he
  have hc := scalar_card_pow hK g.val.left
  rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at hp
  rw [show 7 * 5 ^ k.val * 744 = 5208 * 5 ^ k.val by ring] at hp
  change g.val.left ^ 15624 * z ^ 5208 = z ^ (5208 * 5 ^ k.val) at hp
  rw [hc, one_mul] at hp
  have hm := (pow_eq_pow_iff_modEq.mp hp)
  rw [← hz.eq_orderOf] at hm
  fin_cases k
  · rw [← hk]
    exact Subgroup.one_mem _
  · norm_num [Nat.ModEq] at hm
  · rw [← hk]
    exact Subgroup.mem_zpowers _
  · norm_num [Nat.ModEq] at hm
  · rw [← hk]
    exact Subgroup.mem_zpowers_iff.mpr ⟨2, by simp [← pow_mul]⟩
  · norm_num [Nat.ModEq] at hm

def projection (z : Kˣ) : stabilizer z →* Gal(K/ZMod 5) :=
  SemidirectProduct.rightHom.comp (stabilizer z).subtype

def galoisSubgroup (K : Type) [Field K] [Fintype K] [Algebra (ZMod 5) K] :
    Subgroup Gal(K/ZMod 5) := Subgroup.zpowers (frob K ^ 2)

private theorem projection_range (hK : Fintype.card K = 15625)
    (z : Kˣ) (hz : IsPrimitiveRoot z 15624) :
    (projection z).range = galoisSubgroup K := by
  apply le_antisymm
  · rintro s ⟨g, rfl⟩
    exact projection_mem hK z hz g
  · apply Subgroup.zpowers_le.mpr
    exact ⟨⟨tau z, tau_mem z⟩, rfl⟩

private theorem galois_card (hK : Fintype.card K = 15625) :
    Nat.card (galoisSubgroup K) = 3 := by
  rw [galoisSubgroup, Nat.card_zpowers, orderOf_pow, frob_order hK]
  norm_num

private theorem kernel_scalar (z : Kˣ) (g : (projection z).ker) :
    g.val.val.left ^ 21 = 1 := by
  have hg : g.val.val.right = 1 := g.property
  have he := (mem_stabilizer_iff z g.val.val).mp g.val.property
  rw [hg, AlgEquiv.one_apply] at he
  apply Units.ext
  apply mul_right_cancel₀ (pow_ne_zero 7 z.ne_zero)
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, one_mul] using he

private theorem kernel_card_le (z : Kˣ) : Nat.card (projection z).ker ≤ 21 := by
  let f : (projection z).ker → rootsOfUnity 21 K :=
    fun g => ⟨g.val.val.left, (mem_rootsOfUnity 21 _).mpr (kernel_scalar z g)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact congrArg Subtype.val hab
    · exact a.property.trans b.property.symm
  exact (Nat.card_le_card_of_injective f hf).trans (card_rootsOfUnity K 21)

private theorem stabilizer_card_le (hK : Fintype.card K = 15625)
    (z : Kˣ) (hz : IsPrimitiveRoot z 15624) : Nat.card (stabilizer z) ≤ 63 := by
  rw [← Subgroup.card_ker_mul_card_range (projection z), projection_range hK z hz,
    galois_card hK]
  exact Nat.mul_le_mul_right 3 (kernel_card_le z)

def alphaIn (z : Kˣ) (hz : IsPrimitiveRoot z 15624) : stabilizer z :=
  ⟨alpha z, alpha_mem z hz⟩

private theorem kernel_generated (z : Kˣ) (hz : IsPrimitiveRoot z 15624) :
    (projection z).ker = Subgroup.zpowers (alphaIn z hz) := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · apply Subgroup.zpowers_le.mpr
    change (alpha z).right = 1
    rfl
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe (alphaIn z hz)]
    change Nat.card (projection z).ker ≤ orderOf (alpha z)
    rw [alpha_order z hz]
    exact kernel_card_le z

def betaIn (z : Kˣ) (hz : IsPrimitiveRoot z 15624) : stabilizer z :=
  ⟨beta z, beta_mem z hz⟩

def tauIn (z : Kˣ) : stabilizer z := ⟨tau z, tau_mem z⟩

def betaSubgroup (z : Kˣ) (hz : IsPrimitiveRoot z 15624) : Subgroup (stabilizer z) :=
  Subgroup.zpowers (betaIn z hz)

def tauSubgroup (z : Kˣ) : Subgroup (stabilizer z) := Subgroup.zpowers (tauIn z)

private theorem beta_card (z : Kˣ) (hz : IsPrimitiveRoot z 15624) :
    Nat.card (betaSubgroup z hz) = 7 := by
  rw [betaSubgroup, Nat.card_zpowers, ← Subgroup.orderOf_coe (betaIn z hz)]
  exact beta_order z hz

private theorem tau_card (hK : Fintype.card K = 15625)
    (z : Kˣ) (hz : IsPrimitiveRoot z 15624) : Nat.card (tauSubgroup z) = 9 := by
  rw [tauSubgroup, Nat.card_zpowers, ← Subgroup.orderOf_coe (tauIn z)]
  exact tau_order hK z hz

private theorem factors_disjoint (hK : Fintype.card K = 15625)
    (z : Kˣ) (hz : IsPrimitiveRoot z 15624) :
    Disjoint (betaSubgroup z hz) (tauSubgroup z) := by
  apply Subgroup.disjoint_of_coprime_natCard
  rw [beta_card z hz, tau_card hK z hz]
  decide

private theorem stabilizer_card (hK : Fintype.card K = 15625)
    (z : Kˣ) (hz : IsPrimitiveRoot z 15624) : Nat.card (stabilizer z) = 63 := by
  apply Nat.le_antisymm (stabilizer_card_le hK z hz)
  have hi := Subgroup.mul_injective_of_disjoint (factors_disjoint hK z hz)
  have hc := Nat.card_le_card_of_injective _ hi
  rw [Nat.card_prod, beta_card z hz, tau_card hK z hz] at hc
  exact hc

private theorem factors_complement (hK : Fintype.card K = 15625)
    (z : Kˣ) (hz : IsPrimitiveRoot z 15624) :
    (betaSubgroup z hz).IsComplement' (tauSubgroup z) := by
  apply Subgroup.isComplement'_of_card_mul_and_disjoint
  · rw [beta_card z hz, tau_card hK z hz, stabilizer_card hK z hz]
  · exact factors_disjoint hK z hz

private theorem conj_inl (g : Ambient K) (c : Kˣ) :
    g * SemidirectProduct.inl c * g⁻¹ =
      SemidirectProduct.inl (unitsAut (ZMod 5) K g.right c) := by
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
      SemidirectProduct.mul_right, SemidirectProduct.right_inl,
      SemidirectProduct.left_inl, mul_one]
    have hi : unitsAut (ZMod 5) K g.right
        (unitsAut (ZMod 5) K g.right⁻¹ g.left⁻¹) = g.left⁻¹ := by
      change (unitsAut (ZMod 5) K g.right * unitsAut (ZMod 5) K g.right⁻¹)
        g.left⁻¹ = g.left⁻¹
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hi]
    simp [mul_comm, mul_left_comm]
  · simp

private theorem conj_beta (z : Kˣ) (g : Ambient K) {k : ℕ}
    (hk : g.right = frob K ^ k) :
    g * beta z * g⁻¹ = beta z ^ (5 ^ k) := by
  rw [beta, alpha_pow, conj_inl, hk, frob_units, ← map_pow]

private theorem beta_normal (hK : Fintype.card K = 15625)
    (z : Kˣ) (hz : IsPrimitiveRoot z 15624) : (betaSubgroup z hz).Normal := by
  constructor
  intro n hn g
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  obtain ⟨k, hk⟩ := aut_power hK g.val.right
  have hb : g * betaIn z hz * g⁻¹ = betaIn z hz ^ (5 ^ k.val) := by
    apply Subtype.ext
    exact conj_beta z g.val hk.symm
  have he : g * (betaIn z hz) ^ j * g⁻¹ = (g * betaIn z hz * g⁻¹) ^ j := by
    exact map_zpow (MulAut.conj g) (betaIn z hz) j
  rw [he, hb]
  exact (betaSubgroup z hz).zpow_mem ((betaSubgroup z hz).pow_mem
    (Subgroup.mem_zpowers _) _) _

def internalAction (hK : Fintype.card K = 15625) (z : Kˣ)
    (hz : IsPrimitiveRoot z 15624) : tauSubgroup z →* MulAut (betaSubgroup z hz) := by
  letI := beta_normal hK z hz
  exact (betaSubgroup z hz).normalizerMonoidHom.comp
    (Subgroup.inclusion ((betaSubgroup z hz).normalizer_eq_top ▸ le_top))

/-- The equivalence multiplies the actual internal beta and tau factors. -/
def internalEquiv (hK : Fintype.card K = 15625) (z : Kˣ)
    (hz : IsPrimitiveRoot z 15624) :
    (betaSubgroup z hz) ⋊[internalAction hK z hz] (tauSubgroup z) ≃* stabilizer z := by
  letI := beta_normal hK z hz
  exact SemidirectProduct.mulEquivSubgroup (factors_complement hK z hz)

private theorem action_four (hK : Fintype.card K = 15625)
    (z : Kˣ) (hz : IsPrimitiveRoot z 15624) :
    internalAction hK z hz ⟨tauIn z, Subgroup.mem_zpowers _⟩
      ⟨betaIn z hz, Subgroup.mem_zpowers _⟩ =
        (⟨betaIn z hz, Subgroup.mem_zpowers _⟩ : betaSubgroup z hz) ^ 4 := by
  apply Subtype.ext
  apply Subtype.ext
  change tau z * beta z * (tau z)⁻¹ = beta z ^ 4
  rw [conj_beta z (tau z) rfl]
  have ho := beta_order z hz
  rw [pow_eq_pow_iff_modEq, ho]
  decide

private theorem lift_cube (hK : Fintype.card K = 15625)
    (z : Kˣ) (hz : IsPrimitiveRoot z 15624) (g : stabilizer z)
    (hg : projection z g = frob K ^ 2) :
    g.val ^ 3 = SemidirectProduct.inl (z ^ 5208) := by
  change g.val.right = frob K ^ 2 at hg
  have he := fixed_equation z g.property hg
  have hc : g.val.left ^ 21 = z ^ 168 := by
    apply mul_right_cancel (b := z ^ 7)
    rw [he, ← pow_add]
    rfl
  apply SemidirectProduct.ext
  · rw [pow_succ, pow_two]
    change (g.val.left * unitsAut (ZMod 5) K g.val.right g.val.left) *
      unitsAut (ZMod 5) K (g.val.right * g.val.right) g.val.left = z ^ 5208
    rw [hg, ← pow_add, frob_units, frob_units]
    rw [← pow_succ', ← pow_add]
    change g.val.left ^ (21 * 31) = z ^ 5208
    rw [pow_mul, hc, ← pow_mul]
  · change SemidirectProduct.rightHom (g.val ^ 3) = 1
    rw [map_pow]
    change g.val.right ^ 3 = 1
    rw [hg, ← pow_mul]
    exact frob_six hK

/-- The genuine restriction of the right projection to its proved Galois image. -/
def galoisProjection (hK : Fintype.card K = 15625) (z : Kˣ)
    (hz : IsPrimitiveRoot z 15624) : stabilizer z →* galoisSubgroup K :=
  (projection z).codRestrict (galoisSubgroup K) (projection_mem hK z hz)

private theorem no_section (hK : Fintype.card K = 15625)
    (z : Kˣ) (hz : IsPrimitiveRoot z 15624) :
    ¬ ∃ s : galoisSubgroup K →* stabilizer z,
      (galoisProjection hK z hz).comp s = MonoidHom.id _ := by
  rintro ⟨s, hs⟩
  let a : galoisSubgroup K := ⟨frob K ^ 2, Subgroup.mem_zpowers _⟩
  have ha : a ^ 3 = 1 := by
    apply Subtype.ext
    change (frob K ^ 2) ^ 3 = 1
    rw [← pow_mul]
    exact frob_six hK
  have hg : projection z (s a) = frob K ^ 2 :=
    congrArg Subtype.val (DFunLike.congr_fun hs a)
  have hc := lift_cube hK z hz (s a) hg
  have hp : s a ^ 3 = 1 := by rw [← map_pow, ha, map_one]
  have hv : ((s a).val) ^ 3 = 1 := congrArg Subtype.val hp
  have he : z ^ 5208 = 1 := by
    have := congrArg SemidirectProduct.left (hc.symm.trans hv)
    exact this
  have hd := hz.dvd_of_pow_eq_one 5208 he
  norm_num at hd

/-- Internal cyclic factors, actual orders and the action-four decomposition of the stabilizer. -/
theorem stabilizer_structure (hK : Fintype.card K = 15625)
    (ζ : K) (hζ : IsPrimitiveRoot ζ 15624) :
    let z := primitiveUnit ζ hζ
    let hz : IsPrimitiveRoot z 15624 := IsPrimitiveRoot.coe_units_iff.mp hζ
    alpha z ∈ stabilizer z ∧ tau z ∈ stabilizer z ∧ beta z ∈ stabilizer z ∧
    orderOf (alpha z) = 21 ∧ orderOf (tau z) = 9 ∧ orderOf (beta z) = 7 ∧
    tau z ^ 3 = alpha z ^ 7 ∧ alpha z ^ 7 ≠ 1 ∧
    tau z * beta z * (tau z)⁻¹ = beta z ^ 4 ∧
    Nat.card (stabilizer z) = 63 ∧
    IsCyclic (betaSubgroup z hz) ∧ Nat.card (betaSubgroup z hz) = 7 ∧
    IsCyclic (tauSubgroup z) ∧ Nat.card (tauSubgroup z) = 9 ∧
    (betaSubgroup z hz).Normal ∧
    (betaSubgroup z hz).IsComplement' (tauSubgroup z) ∧
    Nonempty ((betaSubgroup z hz) ⋊[internalAction hK z hz] (tauSubgroup z) ≃*
      stabilizer z) ∧
    internalAction hK z hz ⟨tauIn z, Subgroup.mem_zpowers _⟩
      ⟨betaIn z hz, Subgroup.mem_zpowers _⟩ =
        (⟨betaIn z hz, Subgroup.mem_zpowers _⟩ : betaSubgroup z hz) ^ 4 := by
  dsimp only
  let z := primitiveUnit ζ hζ
  have hz : IsPrimitiveRoot z 15624 := IsPrimitiveRoot.coe_units_iff.mp hζ
  have ha : alpha z ^ 7 ≠ 1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [alpha_order z hz] at hd
    norm_num at hd
  have ht : tau z * beta z * (tau z)⁻¹ = beta z ^ 4 := by
    rw [conj_beta z (tau z) rfl, pow_eq_pow_iff_modEq, beta_order z hz]
    decide
  have hbcyc : IsCyclic (betaSubgroup z hz) :=
    (inferInstance : IsCyclic (Subgroup.zpowers (betaIn z hz)))
  have htcyc : IsCyclic (tauSubgroup z) :=
    (inferInstance : IsCyclic (Subgroup.zpowers (tauIn z)))
  exact ⟨alpha_mem z hz, tau_mem z, beta_mem z hz, alpha_order z hz,
    tau_order hK z hz, beta_order z hz, tau_cube hK z, ha, ht,
    stabilizer_card hK z hz, hbcyc, beta_card z hz, htcyc,
    tau_card hK z hz, beta_normal hK z hz, factors_complement hK z hz,
    ⟨internalEquiv hK z hz⟩, action_four hK z hz⟩

/-- The scalar-kernel extension onto the actual order-three Galois image is nonsplit. -/
theorem galois_nonsplitting (hK : Fintype.card K = 15625)
    (ζ : K) (hζ : IsPrimitiveRoot ζ 15624) :
    let z := primitiveUnit ζ hζ
    let hz : IsPrimitiveRoot z 15624 := IsPrimitiveRoot.coe_units_iff.mp hζ
    (projection z).range = galoisSubgroup K ∧ Nat.card (galoisSubgroup K) = 3 ∧
    Nat.card (projection z).ker = 21 ∧
    (projection z).ker = Subgroup.zpowers (alphaIn z hz) ∧
    Function.Surjective (galoisProjection hK z hz) ∧
    (∀ g : stabilizer z, projection z g = frob K ^ 2 →
      g.val ^ 3 = SemidirectProduct.inl (z ^ 5208) ∧ g ^ 3 ≠ 1) ∧
    ¬ ∃ s : galoisSubgroup K →* stabilizer z,
      (galoisProjection hK z hz).comp s = MonoidHom.id _ := by
  dsimp only
  let z := primitiveUnit ζ hζ
  have hz : IsPrimitiveRoot z 15624 := IsPrimitiveRoot.coe_units_iff.mp hζ
  have hk : Nat.card (projection z).ker = 21 := by
    have he := Subgroup.card_ker_mul_card_range (projection z)
    rw [projection_range hK z hz, galois_card hK, stabilizer_card hK z hz] at he
    omega
  have hs : Function.Surjective (galoisProjection hK z hz) := by
    intro a
    have ham : a.val ∈ (projection z).range := by
      rw [projection_range hK z hz]
      exact a.property
    obtain ⟨g, hg⟩ := ham
    exact ⟨g, Subtype.ext hg⟩
  refine ⟨projection_range hK z hz, galois_card hK, hk, kernel_generated z hz,
    hs, ?_, no_section hK z hz⟩
  intro g hg
  refine ⟨lift_cube hK z hz g hg, ?_⟩
  intro he
  have hv : g.val ^ 3 = 1 := congrArg Subtype.val he
  have hc := lift_cube hK z hz g hg
  have hd := hz.dvd_of_pow_eq_one 5208
    (congrArg SemidirectProduct.left (hc.symm.trans hv))
  norm_num at hd

/-- A split ambient semilinear group does not force stabilizer Galois projections to split. -/
def splittingClaim : Prop :=
  ∀ (L : Type) [Field L] [Fintype L] [Algebra (ZMod 5) L]
    (hL : Fintype.card L = 15625) (z : Lˣ) (hz : IsPrimitiveRoot z 15624),
    ∃ s : galoisSubgroup L →* stabilizer z,
      (galoisProjection hL z hz).comp s = MonoidHom.id _

/-- A nonvacuous finite-field counterexample, using native cyclicity to obtain a primitive unit. -/
theorem result : ¬ splittingClaim := by
  intro h
  let L := GaloisField 5 6
  letI : Fintype L := Fintype.ofFinite L
  have hL : Fintype.card L = 15625 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 5 6 (by decide)
  obtain ⟨z, hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Lˣ)
  have hc : Nat.card Lˣ = 15624 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hL]
  have hp : IsPrimitiveRoot z 15624 := IsPrimitiveRoot.iff_orderOf.mpr (hz.trans hc)
  exact no_section hL z hp (h L hL z hp)

#print axioms stabilizer_structure
#print axioms galois_nonsplitting
#print axioms result

end WeightedSemilinear.OneSupport63
