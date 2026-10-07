/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIA2ExponentDescent
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIA2ExponentDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA2Orbital
set_option autoImplicit false
/-! PartII p260 height filtration and Lemma3.2, made concrete in the actual
nonabelian A2 orbital subgroup. The abelian quotient descent is followed by
actual scalar-root reconstruction of its central discrepancy. No target
coverage or semilinear/extraction conclusion is assumed. -/
namespace NikolovSegal.PartIIA2ExponentDescent
open PartIIA2Orbital
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

-- Actual abelian height-one quotient, with the central coordinate retained.
def firstTwo : upperUnipotent (F := F) →* Multiplicative (F × F) where
  toFun g := Multiplicative.ofAdd (g.val 0 1,g.val 1 2)
  map_one' := by rfl
  map_mul' x z := by
    obtain ⟨a,b,c,hx⟩ := x.prop
    obtain ⟨A,B,C,hz⟩ := z.prop
    change Multiplicative.ofAdd (((x.val*z.val) 0 1),((x.val*z.val) 1 2)) = _
    rw [← hx,← hz]
    apply Prod.ext
    · change ((upper3 a b c).val*(upper3 A B C).val) 0 1 = a+A
      simp [upper3,Matrix.mul_apply,Fin.sum_univ_succ,add_comm]
    · change ((upper3 a b c).val*(upper3 A B C).val) 1 2 = b+B
      simp [upper3,Matrix.mul_apply,Fin.sum_univ_succ,add_comm]

private theorem zero_firstTwo (g : upperUnipotent (F := F)) (h : firstTwo g = 1) :
    ∃ z : F, g.val = upper3 0 0 z := by
  obtain ⟨a,b,c,hg⟩ := g.prop
  change (g.val 0 1,g.val 1 2) = (0,0) at h
  rw [← hg] at h
  have ha : a = 0 := by simpa [upper3] using congrArg Prod.fst h
  have hb : b = 0 := by simpa [upper3] using congrArg Prod.snd h
  exact ⟨c,by simpa only [ha,hb] using hg.symm⟩

-- The actual ordered power-sum substitution from PartII Lemma3.2.
private def powerWitness {G : Type u} [Group G] (gamma : Monoid.End G) (x : G) : ℕ → G
  | 0 => 1
  | n+1 => powerWitness gamma x n * (gamma^n) x

private theorem quotient_power_descent {G A : Type u} [Group G] [CommGroup A]
    (f : G →* A) (gamma : Monoid.End G) (x : G) (n : ℕ) :
    f ((powerWitness gamma x n)⁻¹ * gamma (powerWitness gamma x n)) =
      f (x⁻¹ * (gamma^n) x) := by
  induction n with
  | zero => simp [powerWitness]
  | succ n ih =>
    simp only [powerWitness,map_mul,map_inv,mul_inv_rev]
    have hstep : gamma ((gamma^n) x) = (gamma^(n+1)) x := by
      rw [pow_succ']
      rfl
    rw [hstep]
    have hh := ih
    simp only [map_mul,map_inv] at hh
    calc
      _ = (f (powerWitness gamma x n))⁻¹ * f (gamma (powerWitness gamma x n)) *
          ((f ((gamma^n) x))⁻¹*f ((gamma^(n+1)) x)) := by ac_rfl
      _ = (f x)⁻¹*f ((gamma^n) x)*((f ((gamma^n) x))⁻¹*f ((gamma^(n+1)) x)) := by rw [hh]
      _ = (f x)⁻¹*f ((gamma^(n+1)) x) := by group

/-- Actual nonabelian A2 height-one exponent descent. Opposite root values
are not commuted in SL3. The power-sum witness matches the two abelian
coordinates and retains the genuine central discrepancy as upper3(0,0,z).
This is an equation transformation, not a coverage premise. -/
theorem actual_A2_power_value_descent {m : ℕ}
    (gamma : Fin m → MulAut SL(3,F))
    (hpres : ∀ j g, g ∈ upperUnipotent → gamma j g ∈ upperUnipotent)
    (x : Fin m → SL(3,F)) (hx : ∀ j, x j ∈ upperUnipotent)
    (r : Fin m → ℕ) :
    ∃ c : Fin m → SL(3,F), (∀ j, c j ∈ upperUnipotent) ∧ ∃ z : F,
      orderedProduct (fun j => (c j)⁻¹*gamma j (c j)) =
        orderedProduct (fun j => (x j)⁻¹*(gamma j^r j) (x j))*upper3 0 0 z := by
  let g : Fin m → Monoid.End (upperUnipotent (F := F)) := fun j =>
    { toFun := fun s => ⟨gamma j s.val,hpres j s.val s.prop⟩
      map_one' := Subtype.ext (map_one (gamma j))
      map_mul' := fun s t => Subtype.ext (map_mul (gamma j) s.val t.val) }
  let X : Fin m → upperUnipotent (F := F) := fun j => ⟨x j,hx j⟩
  let C := fun j => powerWitness (g j) (X j) (r j)
  have hgpow : ∀ j n (s : upperUnipotent (F := F)), ((g j^n) s).val = (gamma j^n) s.val := by
    intro j n s
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ',Monoid.End.coe_mul,Function.comp_apply,pow_succ',MulAut.mul_apply]; exact congrArg (gamma j) ih
  let P := orderedProduct (fun j => (C j)⁻¹ * g j (C j))
  let Q := orderedProduct (fun j => (X j)⁻¹ * (g j^r j) (X j))
  have hpq : firstTwo P = firstTwo Q := by
    simp only [P,Q,orderedProduct,map_list_prod,List.map_ofFn,Function.comp_def]
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext j
    exact quotient_power_descent firstTwo (g j) (X j) (r j)
  obtain ⟨z,hz⟩ := zero_firstTwo (Q⁻¹*P) (by rw [map_mul,map_inv,hpq,inv_mul_cancel])
  refine ⟨fun j => (C j).val,fun j => (C j).prop,z,?_⟩
  have hm : ∀ v : Fin m → upperUnipotent (F := F),
      (orderedProduct v).val = orderedProduct (fun j => (v j).val) := by
    intro v
    simpa only [orderedProduct,List.map_ofFn,Function.comp_def,Subgroup.subtype_apply] using
      map_list_prod (upperUnipotent (F := F)).subtype (List.ofFn v)
  have hP : P.val = orderedProduct (fun j => ((C j).val)⁻¹ * gamma j (C j).val) := by
    rw [hm]
    rfl
  have hQ : Q.val = orderedProduct (fun j => (x j)⁻¹ * (gamma j^r j) (x j)) := by
    rw [hm]
    simp only [X,Subgroup.coe_mul,Subgroup.coe_inv,hgpow]
  rw [← hP,← hQ,← hz]
  change P.val = Q.val*(Q.val⁻¹*P.val)
  group

private theorem central_chart (z : F) :
    Matrix.SpecialLinearGroup.transvection (show (0:Fin 3) ≠ 2 by decide) z = upper3 0 0 z := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [upper3,Matrix.SpecialLinearGroup.transvection_coe,Matrix.one_apply,Matrix.single_apply]

/-- Consume the actual Lemma7.1 central-root supplier to remove the exact
central discrepancy of height-one exponent descent. y is chosen before ALL
higher-power witnesses and all residual values, while the prescribed gamma
(and its earlier correction) is fixed. The original ordered higher-power
VALUE product is reconstructed using allowed U witnesses; no arbitrary
word/list product or whole-orbital coverage is a hypothesis. -/
theorem actual_A2_power_descent_and_central_reconstruction [Fintype F] [DecidableEq F]
    {m q M : ℕ} (hq : 0 < q) (hM : q*(2*q+1) < M)
    (hF : 2*(2*q+1)^q < Fintype.card F)
    (gamma : Fin m → MulAut SL(3,F))
    (hpres : ∀ j g, g ∈ upperUnipotent → gamma j g ∈ upperUnipotent)
    (beta : Fin M → MulAut SL(3,F)) (phi : Fin M → RingAut F)
    (chi : Fin M → F) (hchi : ∀ j, chi j ≠ 0)
    (e : Fin M → ℕ) (he : ∀ j, 0 < e j ∧ e j ∣ q)
    (hbeta : ∀ j t, beta j
      (Matrix.SpecialLinearGroup.transvection (show (0:Fin 3) ≠ 2 by decide) t) =
        Matrix.SpecialLinearGroup.transvection (show (0:Fin 3) ≠ 2 by decide) (chi j*phi j t)) :
    ∃ y : Fin M → SL(3,F), ∀ x : Fin m → SL(3,F),
      (∀ j, x j ∈ upperUnipotent) → ∀ r : Fin m → ℕ,
      ∃ c : Fin m → SL(3,F), ∃ w : Fin M → SL(3,F),
        (∀ j, c j ∈ upperUnipotent) ∧ (∀ j, w j ∈ upperUnipotent) ∧
        orderedProduct (fun j => (c j)⁻¹*gamma j (c j)) *
          orderedProduct (fun j => (w j)⁻¹*
            (((beta j*MulAut.conj (y j)⁻¹)^(q/e j)) (w j))) =
          orderedProduct (fun j => (x j)⁻¹*(gamma j^r j) (x j)) := by
  let d := fun j => q/e j
  have hd : ∀ j, 0 < d j ∧ d j ∣ q := by
    intro j
    exact ⟨Nat.div_pos (Nat.le_of_dvd hq (he j).2) (he j).1,Nat.div_dvd_of_dvd (he j).2⟩
  obtain ⟨y,hy⟩ := PartIITransvectionSupply.actual_transvection_scalar_product
    (show (0:Fin 3) ≠ 2 by decide) hq hM hF beta phi chi hchi d hd hbeta
  refine ⟨y,?_⟩
  intro x hx r
  obtain ⟨c,hc,z,hvalue⟩ := actual_A2_power_value_descent gamma hpres x hx r
  obtain ⟨t,ht⟩ := hy (-z)
  refine ⟨c,fun j => Matrix.SpecialLinearGroup.transvection (show (0:Fin 3) ≠ 2 by decide) (t j),hc,?_,?_⟩
  · intro j
    exact ⟨0,0,t j,(central_chart _).symm⟩
  · rw [hvalue,ht,mul_assoc,← central_chart z,
      Matrix.SpecialLinearGroup.transvection_mul_neg,mul_one]
end NikolovSegal.PartIIA2ExponentDescent
