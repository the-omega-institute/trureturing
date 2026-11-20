/- GID: D5/S1/Recurrence/Algebraic/MarkedAssemblyExtraMarker
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/MarkedAssemblyExtraMarker
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: One extra ambient root marker adds one power to the coefficient multiplier. -/

import D5.S1.Recurrence.Algebraic.MarkedAssemblyCoefficients

/-! Fixed-point sums with one extra ambient root marker. -/

set_option autoImplicit false

open Finset PowerSeries
open scoped BigOperators

namespace D5.S1.Recurrence.Algebraic.MarkedAssemblyExtraMarker

open MarkedAssemblyCoefficients MarkedAssemblyFixedPoints

noncomputable section

variable {d : ℕ} {V C : Type} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

private abbrev ExtraPointed (allowed : ℕ → C → Prop) :=
  PointedAssembly (d := d) (V := V) allowed × V

private def fixedExtraPointedEquiv (allowed : ℕ → C → Prop) (g : Equiv.Perm V) :
    MulAction.fixedBy (ExtraPointed (d := d) (V := V) allowed) g ≃
      MulAction.fixedBy (PointedAssembly (d := d) (V := V) allowed) g ×
        ↥(fixedVertices g (univ : Finset V)) where
  toFun R := ⟨⟨R.val.1, congrArg Prod.fst R.property⟩,
    ⟨R.val.2, mem_filter.mpr ⟨mem_univ _, congrArg Prod.snd R.property⟩⟩⟩
  invFun R := ⟨(R.1.val, R.2.val), Prod.ext R.1.property (mem_filter.mp R.2.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance extraPointedFixedFintype (allowed : ℕ → C → Prop) (g : Equiv.Perm V) :
    Fintype (MulAction.fixedBy (ExtraPointed (d := d) (V := V) allowed) g) :=
  Fintype.ofFinite _

private theorem extra_pointed_fixed_sum (allowed : ℕ → C → Prop)
    (sign : C → ℤ) (g : Equiv.Perm V) :
    (∑ R : MulAction.fixedBy (ExtraPointed (d := d) (V := V) allowed) g,
      pointedWeight sign R.val.1) =
      ((fixedVertices g (univ : Finset V)).card : ℤ) *
        ∑ R : MulAction.fixedBy (PointedAssembly (d := d) (V := V) allowed) g,
          pointedWeight sign R.val := by
  classical
  calc
    _ = ∑ R : MulAction.fixedBy (PointedAssembly (d := d) (V := V) allowed) g ×
          ↥(fixedVertices g (univ : Finset V)), pointedWeight sign R.1.val :=
      Fintype.sum_equiv (fixedExtraPointedEquiv allowed g) _ _ (fun _ => rfl)
    _ = _ := by
      simp only [Fintype.sum_prod_type, sum_const, card_univ, Fintype.card_coe,
        nsmul_eq_mul, mul_sum]

private def difference (allowed : ℕ → C → Prop) (sign : C → ℤ) (g : Equiv.Perm V) : ℤ :=
  (∑ E : MulAction.fixedBy (FullAssembly (d := d) (V := V) allowed) g, weight sign E.val.val) -
    ∑ R : MulAction.fixedBy (ExtraPointed (d := d) (V := V) allowed) g,
      pointedWeight sign R.val.1

private theorem difference_coefficient (allowed : ℕ → C → Prop) (sign : C → ℤ)
    (g : Equiv.Perm V) (hf : 1 ≤ (fixedVertices g (univ : Finset V)).card) :
    let f := (fixedVertices g (univ : Finset V)).card
    let H := (exp ℚ).subst (PowerSeries.C ((f : ℚ) ^ d) * colorSeries allowed sign)
    let M := ∑ B : FixedAssembly (k := d) allowed (movedVertices g univ) univ g, weight sign B.val
    (difference (d := d) allowed sign g : ℚ) =
      (M : ℚ) * (f.factorial : ℚ) * (coeff f H - (f : ℚ) ^ (d + 1) * coeff (f - 1) H) := by
  classical
  dsimp only
  let f := (fixedVertices g (univ : Finset V)).card
  let H := (exp ℚ).subst (PowerSeries.C ((f : ℚ) ^ d) * colorSeries allowed sign)
  let M := ∑ B : FixedAssembly (k := d) allowed (movedVertices g univ) univ g, weight sign B.val
  let E := ∑ E : MulAction.fixedBy (FullAssembly (d := d) (V := V) allowed) g, weight sign E.val.val
  let R := ∑ R : MulAction.fixedBy (PointedAssembly (d := d) (V := V) allowed) g,
    pointedWeight sign R.val
  have hE : (E : ℚ) = (f.factorial : ℚ) * coeff f H * (M : ℚ) := by
    dsimp only [E]
    rw [(assembly_action_fixed_sum allowed sign g).2,
      fixed_assembly_weight_factorization allowed univ univ g sign, Int.cast_mul,
      assembly_sum_coefficient]
  have hER : ((E - R : ℤ) : ℚ) =
      (M : ℚ) * (f.factorial : ℚ) * (coeff f H - (f : ℚ) ^ d * coeff (f - 1) H) :=
    fixed_point_subtraction_coefficient allowed sign g hf
  rw [difference, extra_pointed_fixed_sum, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  change (E : ℚ) - (f : ℚ) * (R : ℚ) = _
  rw [Int.cast_sub] at hER
  rw [pow_succ]
  linear_combination (f : ℚ) * hER + (1 - (f : ℚ)) * hE

private theorem difference_burnside (allowed : ℕ → C → Prop) (sign : C → ℤ)
    (hs : ∀ c, sign c = 1 ∨ sign c = -1) (G : Subgroup (Equiv.Perm V)) :
    let : Fintype G := Fintype.ofFinite _
    (Nat.card G : ℤ) ∣ ∑ g : G, difference (d := d) allowed sign g.val := by
  classical
  let : Fintype G := Fintype.ofFinite _
  have hE := signed_burnside (Γ := G)
    (fun E : FullAssembly (d := d) (V := V) allowed => weight sign E.val)
    (fun g E => (assembly_action_fixed_sum allowed sign g.val).1 E)
    (fun E => weight_unit_sign sign hs E.val)
  have hR := signed_burnside (Γ := G)
    (fun R : ExtraPointed (d := d) (V := V) allowed => pointedWeight sign R.1)
    (fun g R => (pointed_action_fixed_sum allowed sign g.val).1 R.1)
    (fun R => weight_unit_sign sign hs R.1.val.2.2)
  rw [Nat.card_eq_fintype_card]
  simp only [difference, sum_sub_distrib]
  exact dvd_sub hE hR

omit [DecidableEq V] [DecidableEq C] in
private theorem residual_local_integral (allowed : ℕ → C → Prop) (sign : C → ℤ)
    (hs : ∀ c, sign c = 1 ∨ sign c = -1) (hn : 1 ≤ Fintype.card V)
    (p : ℕ) (hp : p.Prime) (hpn : ¬p ∣ Fintype.card V)
    (hlower : ∀ f : ℕ, 1 ≤ f → f < Fintype.card V →
      let H := (exp ℚ).subst (PowerSeries.C ((f : ℚ) ^ d) * colorSeries allowed sign)
      coeff f H = (f : ℚ) ^ (d + 1) * coeff (f - 1) H) :
    let n := Fintype.card V
    let H := (exp ℚ).subst (PowerSeries.C ((n : ℚ) ^ d) * colorSeries allowed sign)
    0 ≤ padicValRat p (coeff n H - (n : ℚ) ^ (d + 1) * coeff (n - 1) H) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let n := Fintype.card V
  let H := (exp ℚ).subst (PowerSeries.C ((n : ℚ) ^ d) * colorSeries allowed sign)
  let q := coeff n H - (n : ℚ) ^ (d + 1) * coeff (n - 1) H
  let z := difference (d := d) allowed sign (1 : Equiv.Perm V)
  let P : Sylow p (Equiv.Perm V) := Classical.choice inferInstance
  let : Fintype P := Fintype.ofFinite _
  have hd := difference_burnside (d := d) allowed sign hs P.toSubgroup
  dsimp only at hd
  rw [sum_eq_single 1] at hd
  · have hcard : Nat.card P = p ^ n.factorial.factorization p := by
      rw [P.card_eq_multiplicity, Nat.card_eq_fintype_card, Fintype.card_perm]
    change (Nat.card P : ℤ) ∣ z at hd
    rw [hcard, Nat.cast_pow] at hd
    have hf : fixedVertices (1 : Equiv.Perm V) (univ : Finset V) = univ := by
      ext x
      simp [fixedVertices]
    have he : (z : ℚ) = (n.factorial : ℚ) * q := by
      have h := difference_coefficient (d := d) allowed sign (1 : Equiv.Perm V)
        (by simpa only [hf, card_univ] using hn)
      dsimp only at h
      rw [hf, card_univ, moved_identity_sum, Int.cast_one, one_mul] at h
      exact h
    change 0 ≤ padicValRat p q
    by_cases hq : q = 0
    · simp [hq]
    have hnq : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hzq : (z : ℚ) ≠ 0 := by rw [he]; exact mul_ne_zero hnq hq
    have hz : z ≠ 0 := by exact_mod_cast hzq
    have hv := ((padicValInt_dvd_iff _ z).mp hd).resolve_left hz
    rw [Nat.factorization_def _ hp] at hv
    have hev := congrArg (padicValRat p) he
    rw [padicValRat.mul hnq hq, padicValRat.of_int, padicValRat.of_nat] at hev
    omega
  · intro g _ hg
    have hf := sylow_fixed_card p P g hpn
    have hlt := proper_fixed_card g.val (fun h => hg (Subtype.ext h))
    have he := difference_coefficient (d := d) allowed sign g.val hf
    dsimp only at he
    rw [hlower _ hf hlt, sub_self, mul_zero] at he
    exact_mod_cast he
  · simp

/-- An integral strict prefix obeying the lower mixed-power equations has a locally integral
residual at every prime coprime to its endpoint. The pointed side uses one extra ambient marker. -/
theorem signed_prefix_residual_local_integral (d N : ℕ) (a : ℕ → ℤ) (hN : 1 ≤ N)
    (p : ℕ) (hp : p.Prime) (hpn : ¬p ∣ N)
    (hlower : ∀ f : ℕ, 1 ≤ f → f < N →
      let H := (exp ℚ).subst (PowerSeries.C ((f : ℚ) ^ d) * prefixSeries N a)
      coeff f H = (f : ℚ) ^ (d + 1) * coeff (f - 1) H) :
    let H := (exp ℚ).subst (PowerSeries.C ((N : ℚ) ^ d) * prefixSeries N a)
    0 ≤ padicValRat p (coeff N H - (N : ℚ) ^ (d + 1) * coeff (N - 1) H) := by
  classical
  have he := residual_local_integral (d := d) (V := Fin N) (prefixAllowed N a)
    (prefixSign N a) (prefix_sign_unit N a) (by simpa using hN) p hp (by simpa using hpn)
  simp only [Fintype.card_fin, prefix_series_eq] at he
  exact he hlower

end

end D5.S1.Recurrence.Algebraic.MarkedAssemblyExtraMarker
