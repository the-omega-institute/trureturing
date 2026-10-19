/- GID: D5/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/TarnauceanuReciprocalSubgroupOrders
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Tarnauceanu Conjecture 3.1 reciprocal subgroup-order sum is proved. -/

/- Public declarations: `f` is the literal subgroup-order reciprocal sum and `claim` is the
   source conjecture with its quantifiers inlined. `result` is the settling theorem. Each
   helper is used by a later helper or by `result` on its proof path.
   f: proof_shape: definition; escape_witness: none
   claim: proof_shape: definition; escape_witness: none
   result: proof_shape: bind-only; escape_witness: none
   admission_basis: open-problem-resolution (#18701; Proved)
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19077 (result).
   Direct frozen dependencies (statement_id):
   D5.S3.FiniteGroups.CyclicPrimePowerAction.ActionData sha256:c71aad57a46e2043ac3c59fbfdac94c88466997905d9131f6000db21ab421b86
   D5.S3.FiniteGroups.CyclicPrimePowerAction.SplitGroup sha256:d4b08944e010dadced8e5c21927dec386b50829f03bf269f2d45116bd6ce1cc4
   D5.S3.FiniteGroups.CyclicPrimePowerAction.actionData sha256:b2241a6a63f1460c92eb590c6c5dd32922d153fb724fb80e05b22c00ca27dc43
   D5.S3.FiniteGroups.CyclicPrimePowerAction.cyclicSubgroupEquiv sha256:4b2e77bc94c9dd2a62b2a90d9565fadf0e903c1c469783223fad87f122f41204
   D5.S3.FiniteGroups.CyclicPrimePowerAction.subgroupEnumeration sha256:a0f94a3b60675dfbecbb0acf152ddf6be03f6274e497e34ce4e5139fb1f864cb
   D5.S3.FiniteGroups.CyclicPrimePowerAction.cyclic_card sha256:e580e385eb64c74b3b2c9ac7c7138d10b5b976958f9cf2e3281ab777f6fe89b8
   D5.S3.FiniteGroups.CyclicPrimePowerAction.kernel_power_card sha256:93c8d26a6815c5a83855148dddc390b31bada1c29e0fa8a0c4ebb848061695bf
   Claim uses the source convention literally; the owner correspondence is used only inside proofs.
-/

import D5.S3.FiniteGroups.CyclicPrimePowerAction
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Algebra.Order.Field.GeomSum

set_option autoImplicit false

namespace D5.S3.FiniteGroups.TarnauceanuReciprocalSubgroupOrders

/-- `f(G) = ∑_{H ∈ L(G)} 1/|H|`, the sum over all subgroups `H` of `G` (including `1` and `G`). -/
noncomputable def f (G : Type) [Group G] : ℝ :=
  ∑ᶠ H : Subgroup G, (1 : ℝ) / (Nat.card H : ℝ)

/-- Tărnăuceanu, Sci. Stud. Res. Ser. Math. Inform. 34 (2024), Conjecture 3.1 ("There is no constant
c > 1 such that f(G) > c, for all finite non-cyclic groups G."). -/
def claim : Prop :=
  ¬ ∃ c : ℝ, 1 < c ∧ ∀ (G : Type) [Group G] [Finite G], ¬ IsCyclic G → c < f G

end D5.S3.FiniteGroups.TarnauceanuReciprocalSubgroupOrders

namespace D5.S3.FiniteGroups.TarnauceanuReciprocalSubgroupOrders

open D5.S3.FiniteGroups.CyclicPrimePowerAction
open scoped BigOperators
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

variable {p q s : ℕ} [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)]

private theorem over_card (A : ActionData p q s) (B : Subgroup (Cyclic (q ^ s))) :
    Nat.card (B.comap (SemidirectProduct.rightHom : SplitGroup A →* Cyclic (q ^ s))) =
      p * Nat.card B := by
  let e : B.comap (SemidirectProduct.rightHom : SplitGroup A →* Cyclic (q ^ s)) ≃
      Cyclic p × B := {
    toFun x := (x.val.left, ⟨x.val.right, x.property⟩)
    invFun x := ⟨⟨x.1, x.2.val⟩, x.2.property⟩
    left_inv x := by apply Subtype.ext; rfl
    right_inv x := rfl }
  rw [Nat.card_congr e, Nat.card_prod, cyclic_card p]

private theorem complement_card (A : ActionData p q s) (x : Cyclic p) :
    Nat.card ((SemidirectProduct.inr : Cyclic (q ^ s) →* SplitGroup A).range.map
      (MulAut.conj (SemidirectProduct.inl x : SplitGroup A)).toMonoidHom) = q ^ s := by
  rw [Subgroup.card_map_of_injective (MulAut.conj _).injective,
    MonoidHom.range_eq_map, Subgroup.card_map_of_injective SemidirectProduct.inr_injective,
    Subgroup.card_top, cyclic_card (q ^ s)]

private theorem split_not_cyclic (A : ActionData p q s) : ¬ IsCyclic (SplitGroup A) := by
  intro hcyc
  letI := hcyc
  letI := IsCyclic.commGroup (α := SplitGroup A)
  have ha : A.action (generator (q ^ s)) = 1 := by
    apply MulEquiv.ext
    intro x
    have he := mul_comm (SemidirectProduct.inr (generator (q ^ s)) : SplitGroup A)
      (SemidirectProduct.inl x)
    simpa using congrArg SemidirectProduct.left he
  have ho := A.order_generator
  rw [ha, orderOf_one] at ho
  exact (Fact.out : q.Prime).ne_one ho.symm

private theorem reciprocal_geometric_bound (q n : ℕ) (hq : 1 < q) :
    (∑ j : Fin n, (1 : ℝ) / (q : ℝ) ^ j.val) ≤ (q : ℝ) / ((q : ℝ) - 1) := by
  have hqr : (1 : ℝ) < q := Nat.one_lt_cast.mpr hq
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hqm : (q : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hqr)
  have hi : (q : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).2 hqr
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n)
    (x := (q : ℝ)⁻¹) (by positivity) hi
  calc
    _ = ∑ i ∈ Finset.range n, ((q : ℝ)⁻¹) ^ i := by
      simp only [one_div, ← inv_pow]
      rw [Fin.sum_univ_eq_sum_range]
    _ ≤ 1 / (1 - (q : ℝ)⁻¹) := by simpa using h
    _ = _ := by
      field_simp [hq0, hqm]
      <;> ring

private theorem quotient_sum_bound (q s : ℕ) (hq : q.Prime) [NeZero (q ^ s)] :
    (∑ B : Subgroup (Cyclic (q ^ s)), (1 : ℝ) / (Nat.card B : ℝ)) ≤
      (q : ℝ) / ((q : ℝ) - 1) := by
  classical
  let e := cyclicSubgroupEquiv hq (cyclic_card (q ^ s))
  have he (j : Fin (s + 1)) : Nat.card (e.symm j) = q ^ j.val := by
    exact (kernel_power_card)
      (cyclic_card (q ^ s)) j
  calc
    _ = ∑ j : Fin (s + 1), (1 : ℝ) / (q : ℝ) ^ j.val := by
      rw [← e.symm.sum_comp]
      apply Finset.sum_congr rfl
      intro j _
      rw [he, Nat.cast_pow]
    _ ≤ _ := reciprocal_geometric_bound q (s + 1) hq.one_lt

private theorem split_sum_bound (A : ActionData p q s) (hs : 0 < s) (hc : p.Coprime q) :
    f (SplitGroup A) ≤
      (1 / (p : ℝ)) * ((q : ℝ) / ((q : ℝ) - 1)) +
      (q : ℝ) / ((q : ℝ) - 1) + (p : ℝ) / (q : ℝ) ^ s := by
  classical
  letI := Fintype.ofFinite (Subgroup (SplitGroup A))
  let e := subgroupEnumeration A hs hc
  let w : Subgroup (SplitGroup A) → ℝ := fun H => 1 / (Nat.card H : ℝ)
  have he : f (SplitGroup A) = ∑ z : SubgroupLabel p q s, w (e.symm z) := by
    rw [f, finsum_eq_sum_of_fintype, Equiv.sum_comp e.symm w]
  have hover (B : Subgroup (Cyclic (q ^ s))) :
      w (e.symm (.inl B)) = (1 / (p : ℝ)) * (1 / (Nat.card B : ℝ)) := by
    change (1 : ℝ) / (Nat.card (B.comap SemidirectProduct.rightHom) : ℝ) = _
    rw [over_card A B, Nat.cast_mul]
    ring
  have hpure (B : {B : Subgroup (Cyclic (q ^ s)) // B ≠ ⊤}) :
      w (e.symm (.inr (.inl B))) = 1 / (Nat.card B.val : ℝ) := by
    change (1 : ℝ) / (Nat.card (B.val.map SemidirectProduct.inr) : ℝ) = _
    rw [Subgroup.card_map_of_injective SemidirectProduct.inr_injective]
  have hcompl (x : Cyclic p) :
      w (e.symm (.inr (.inr x))) = 1 / (q : ℝ) ^ s := by
    change (1 : ℝ) / (Nat.card ((SemidirectProduct.inr : Cyclic (q ^ s) →*
      SplitGroup A).range.map (MulAut.conj (SemidirectProduct.inl x : SplitGroup A)).toMonoidHom) : ℝ) = _
    rw [complement_card A x, Nat.cast_pow]
  rw [he, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp_rw [hover, hpure, hcompl]
  rw [← Finset.mul_sum]
  have hcount : (∑ _x : Cyclic p, (1 : ℝ) / (q : ℝ) ^ s) =
      (p : ℝ) / (q : ℝ) ^ s := by
    simp [← Nat.card_eq_fintype_card, cyclic_card p, div_eq_mul_inv]
  rw [hcount]
  have hproper : (∑ B : {B : Subgroup (Cyclic (q ^ s)) // B ≠ ⊤},
      (1 : ℝ) / (Nat.card B.val : ℝ)) ≤
      ∑ B : Subgroup (Cyclic (q ^ s)), (1 : ℝ) / (Nat.card B : ℝ) := by
    exact Finset.sum_le_sum_of_injOn
      (fun B : {B : Subgroup (Cyclic (q ^ s)) // B ≠ ⊤} => B.val)
      Subtype.coe_injective.injOn (by simp) (fun _ _ => le_rfl)
      (fun _ _ _ => by positivity)
  have hbound := quotient_sum_bound q s (Fact.out : q.Prime)
  have hp0 : (0 : ℝ) ≤ 1 / (p : ℝ) := one_div_nonneg.mpr (Nat.cast_nonneg p)
  linarith only [mul_le_mul_of_nonneg_left hbound hp0, hproper.trans hbound]

theorem result : claim := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (3 / (c - 1) + 1)
  obtain ⟨q, hnq, hq⟩ := Nat.exists_infinite_primes n
  have hqr : (1 : ℝ) < q := Nat.one_lt_cast.mpr hq.one_lt
  have hqbig : 3 / ((q : ℝ) - 1) < c - 1 := by
    have hnq' : (n : ℝ) ≤ q := Nat.cast_le.mpr hnq
    have hmul : (3 : ℝ) < (c - 1) * ((q : ℝ) - 1) := by
      have h := (div_lt_iff₀ (sub_pos.mpr hc)).mp (by linarith : 3 / (c - 1) < (q : ℝ) - 1)
      nlinarith
    exact (div_lt_iff₀ (sub_pos.mpr hqr)).2 (by nlinarith)
  obtain ⟨p, hp, hqp, hpmod⟩ := Nat.exists_prime_gt_modEq_one q hq.ne_zero
  have hd : q ∣ p - 1 := (Nat.modEq_iff_dvd' hp.one_lt.le).mp hpmod.symm
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).2 (by omega)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((p : ℝ) * ((q : ℝ) - 1)) hqr
  let s := k + 1
  have hs : 0 < s := Nat.zero_lt_succ k
  have hpow : (p : ℝ) * ((q : ℝ) - 1) < (q : ℝ) ^ s := by
    have hmono : (q : ℝ) ^ k ≤ (q : ℝ) ^ (k + 1) := by
      exact pow_le_pow_right₀ hqr.le (Nat.le_succ k)
    exact hk.trans_le hmono
  have hsmall : (p : ℝ) / (q : ℝ) ^ s < 1 / ((q : ℝ) - 1) := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ s)).2
    rw [one_div_mul_eq_div]
    exact (lt_div_iff₀ (sub_pos.mpr hqr)).2 hpow
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  letI : NeZero (q ^ s) := ⟨pow_ne_zero s hq.ne_zero⟩
  let A := actionData p q s hp hq hd hs
  have hb := split_sum_bound A hs hcop
  have hnoncyc := split_not_cyclic A
  have hlower := hbound (SplitGroup A) hnoncyc
  have hpq : (q : ℝ) < p := Nat.cast_lt.mpr hqp
  have hfirst : (1 / (p : ℝ)) * ((q : ℝ) / ((q : ℝ) - 1)) ≤
      1 / ((q : ℝ) - 1) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    apply (le_div_iff₀ (sub_pos.mpr hqr)).2
    have he : 1 / (p : ℝ) * ((q : ℝ) / ((q : ℝ) - 1)) * ((q : ℝ) - 1) =
        (q : ℝ) / p := by field_simp
    rw [he]
    exact (div_le_one hp0).2 hpq.le
  have hsecond : (q : ℝ) / ((q : ℝ) - 1) = 1 + 1 / ((q : ℝ) - 1) := by
    field_simp
    <;> ring
  rw [hsecond] at hfirst
  rw [hsecond] at hb
  have hqbig' : 3 * (1 / ((q : ℝ) - 1)) < c - 1 := by
    simpa only [div_eq_mul_inv, one_mul] using hqbig
  linarith only [hb, hfirst, hsmall, hqbig', hlower]

end D5.S3.FiniteGroups.TarnauceanuReciprocalSubgroupOrders
