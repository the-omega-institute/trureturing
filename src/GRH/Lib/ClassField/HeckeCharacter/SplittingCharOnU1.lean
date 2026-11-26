import GRH.Lib.ClassField.HeckeCharacter.CharacterConjugates
import GRH.Lib.Weil.Construction.PairDefs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM
field (known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

This file: Local values of base change; weight, powers and algebraicity of the splitting
character. -/

open NumberField Finset Valued Complex OneMemClass


attribute [local simp] RingHom.codRestrict coe_divStar star_singleAdele MulChar.one_apply chiAdelic
variable {E : Type*} [Field E] [CMType E] {w : FinPlace E} {μ : AutChar E} {e ψ}

lemma AutChar.HasWeight.of_weight_eq (h : μ.HasWeight e ψ) {e'} : e = e' → μ.HasWeight e' ψ :=
  (· ▸ h)

/-- Let μ have tame part ψ with ψ trivial at w̄; let x ∈ E_w^×, a local unit if w̄ ≠ w, be
viewed as an idele at w. Then x/x̄ has integral finite part, and μ(x/x̄) = ψ_w(x/x̄ mod w). -/
lemma AutChar.HasWeight.exists_baseChange_finPart_locIdele (h : μ.HasWeight e ψ) (h' :
  ψ (star w) = 1) x (hx : w.IsSplit → v x.1 = 1) : ∃ k, μ.baseChange.finPart (locIdele w x) =
  ψ w (reduceAt w ⟨(divStar (locFullIdele w x)).1.2, k⟩) := by
  have f y u : v ((locFullIdele w y).1.2 u) =
    ite (u = w) (v y.1) 1 := by aesop (add simp locFullIdele)
  suffices _ from ⟨this, (h.2 _ this).trans (by rw [finprod_eq_single _ w ((and_forall_ne (star
    w)).1 ⟨by simp [*, -coe_divStar], ?_⟩)] <;> simp +contextual [reduceAt, locFullIdele, ← map_inv,
      ← one_def])⟩
  simp [mem_Ô, *, ← map_inv]; aesop

/-- Let μ have weight e and tame part ψ, and let w be a finite place with w̄ ≠ w and ψ_{w̄}
trivial. Then the base change y ↦ μ(y/ȳ), at a local unit x placed at w, equals ψ_w(x mod
w). -/
lemma AutChar.HasWeight.baseChange_finPart_locIdele (h : μ.HasWeight e ψ) (hw : w.IsSplit) (h' :
  ψ (star w) = 1) {x} (hx : v x.1 = 1) :
  μ.baseChange.finPart (locIdele w x) = ψ w (IsLocalRing.residue _ ⟨x, hx.le⟩) := by
  simp [↓(h.exists_baseChange_finPart_locIdele ..).2, reduceAt, locFullIdele, ← map_inv, *, symm]

namespace WeilData

variable [WeilData E]

instance upsilonU1_hasWeight : upsilonU1.HasWeight (E := E) 1 1 :=
  ⟨by simp, fun _ h ↦ (υ_unit _ ⟨h, star_mem_Ô h⟩).trans (by simp)⟩

instance hasWeight_upsilonU1_zpow z :
  (upsilonU1 ^ z : AutChar E).HasWeight (fun _ ↦ z) 1 := by simpa using! upsilonU1_hasWeight.zpow z

instance hasWeight_upsilonU1_pow (n : ℕ) : (upsilonU1 ^ n : AutChar E).HasWeight (fun _ ↦ n) 1 :=
  hasWeight_upsilonU1_zpow n

instance _root_.AutChar.HasWeight.mul_upsilonU1_pow [h : μ.HasWeight e ψ] (n : ℕ) : (μ * upsilonU1 ^
  n).HasWeight (n + e ·) ψ := by simpa [add_comm] using! h.mul (hasWeight_upsilonU1_pow n)

/-- The twist `rankTwist μ n` of μ by a power of υ restricted to U(1) has the weight of `μ` raised
by `⌊card n / 2⌋` and the tame part of `μ`. -/
instance _root_.AutChar.HasWeight.hasWeight_rankTwist [h : μ.HasWeight e ψ] {n} [Fintype n] :
    (_root_.rankTwist μ n).HasWeight ((Fintype.card n / 2 : ℕ) + e ·) ψ := h.mul_upsilonU1_pow _

/-- The base change x ↦ υ(x/x̄) of the restriction of the splitting character υ to U(1)(𝔸)
equals the Hecke character υ². -/
@[simp] lemma baseChange_upsilonU1 : upsilonU1.baseChange = υ (E := E) ^ 2 := by
  ext x : 2; simpa [sq, υ_star] using! congrArg υ.1 (by bound : _ = x / star x)

variable {p} [Fact p.Prime] (ι : ℂ →+* ℂ_[p]) (x : (𝔸f E)ˣ)

/-- For Weil data on E and a finite idele x, there are n > 0 and y ∈ E^× such that xⁿ and y have
the same valuation at every finite place and (υ(x)|x|^(−1/2))ⁿ = ∏_v Φ_v(ȳ), over the
embeddings Φ_v of the CM type. -/
lemma exists_chiFin_pow_eq_prod : ∃ n > 0, ∃ y,
  (∀ w, v ((x ^ n).1 w) = v ((principalIdele y).1 w)) ∧ chiFin x ^ n = ∏ v, Φ v (starRingEnd E y) :=
  ⟨_, classNumber_pos E, (exists_valuation_eq_of_mem_sup (pow_classNumber_mem_principal_sup x)).imp
  fun y h ↦ by rw [← map_pow, chiFin_congr, ← mul_one (∏ _, _), ← show chiAdelic
  (y.map toAdele.1) = 1 by simp [upsilon_toAdele, ideleAbs_toAdele]] <;> simp [chiFin,
  upsilon_eq_prod_mul_of_v_eq (x := y.map _) (principalIdele y), ideleAbs, finprod_nonneg, field,
  h, @starRingEnd_apply E, prod_pow, ← prod_mul_distrib, conj_mul', prod_nonneg]
               rw [div_mul_cancel_right₀]; simp [prod_eq_zero_iff]⟩

lemma norm_map_chiFin : ‖ι (chiFin x)‖ = ∏ v, ‖adeleExtension (weightEmbedding ι v)
  x.1‖ := have ⟨_, n, _, h, e⟩ := exists_chiFin_pow_eq_prod x
  (pow_left_inj₀ (by simp) (by positivity) n.ne').1 (by simp [*, ← prod_pow, ← norm_pow,
    ← map_pow, ← Units.val_pow_eq_pow_val, (norm_adeleExtension_eq_iff ..).2 (h _)])
