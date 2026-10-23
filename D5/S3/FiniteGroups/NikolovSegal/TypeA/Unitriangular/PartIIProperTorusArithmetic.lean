/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIProperTorusArithmetic
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIProperTorusArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIFieldMaps
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Lean Elab Term in
elab "properField%" id:ident : term => do
  let env ← getEnv
  let owner := "PartIIFieldMaps"
  let suffix := ".NikolovSegal." ++ owner ++ "." ++ id.getId.toString
  let cs := env.constants.toList.filter fun (n,_) =>
    n.toString.endsWith suffix && match env.getModuleIdxFor? n with
      | none => false
      | some i => env.header.moduleNames[i.toNat]!.toString == "D5.S3.FiniteGroups.NikolovSegal.PartIIFieldMaps"
  match cs with
  | [(n,_)] => elabTerm (mkIdent n) none
  | _ => throwError "Unique actual finite-field kernel {id} not found"
namespace NikolovSegal.PartIIProperTorusArithmetic
open PartIIFieldMaps
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
/-- The actual quantitative torus scalar in printed PartII Lemma9.1.
The bound depends only on d; lambda precedes every matrix/target.
Both nontrivial field powers and large fixed fields are proved cases. -/
theorem lemma9_1_torus_scalar (phi : RingAut F) (d : ℕ) (hd : 0 < d)
    (hF : (d+1)^d < Fintype.card F) :
    ∃ lambda : F, lambda ≠ 0 ∧ orbitProduct phi d lambda ≠ 1 := by
  classical
  by_cases hp : phi^d=1
  · let K := FixedBy.subfield F phi
    letI : Fintype K := Fintype.ofFinite K
    have hcF : Nat.card F ≤ (Nat.card K)^d := by
      have h := (properField% fixed_power_card_le) phi d hd
      let E := FixedBy.subfield F (phi^d)
      let e : E ≃ F :=
        { toFun := Subtype.val
          invFun := fun x => ⟨x,by change (phi^d) x=x; rw [hp]; rfl⟩
          left_inv := fun x => rfl
          right_inv := fun x => rfl }
      exact (Nat.card_congr e).symm.le.trans h
    have hK : d+1 < Nat.card K := by
      by_contra hn
      have hle : Nat.card F ≤ (d+1)^d := hcF.trans (Nat.pow_le_pow_left (Nat.le_of_not_gt hn) d)
      exact (not_lt_of_ge hle) (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
    have hgd : g^d ≠ 1 := by
      intro he
      have hh := orderOf_dvd_of_pow_eq_one he
      rw [hg,Nat.card_units] at hh
      exact (not_le_of_gt (show d < Nat.card K-1 by omega)) (Nat.le_of_dvd hd hh)
    let a : F := (g.val : K).val
    have ha : a ≠ 0 := by
      intro h
      apply g.ne_zero
      exact Subtype.ext h
    have hfix : ∀ l : ℕ, (phi^l) a=a := by
      intro l
      induction l with
      | zero => rfl
      | succ l ih =>
        rw [pow_succ',RingAut.mul_apply,ih]
        exact g.val.prop
    have hprod : orbitProduct phi d a=a^d := by
      simp only [orbitProduct,hfix,Finset.prod_const,Finset.card_range]
    refine ⟨a,ha,?_⟩
    rw [hprod]
    intro h
    apply hgd
    apply Units.ext
    apply Subtype.ext
    exact h
  · have hmove : ∃ a : F, (phi^d) a ≠ a := by
      by_contra h
      apply hp
      apply RingEquiv.ext
      simpa only [not_exists,not_not,RingAut.one_apply] using h
    obtain ⟨a,ha⟩ := hmove
    have hlt : (Finset.univ.filter (fun t : F => (phi^d) t=t)).card < Fintype.card F := by
      apply lt_of_lt_of_eq (Finset.card_lt_card ?_) (Finset.card_univ)
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.filter_subset _ _,?_⟩
      intro he
      have hh : a ∈ Finset.univ.filter (fun t : F => (phi^d) t=t) := by rw [he]; exact Finset.mem_univ a
      exact ha (Finset.mem_filter.mp hh).2
    obtain ⟨a,ha,hN⟩ := (properField% nontrivial_orbit_power) phi d 1 (by decide) (by simpa only [one_mul] using hlt)
    exact ⟨a,ha,by simpa only [pow_one] using hN⟩
end NikolovSegal.PartIIProperTorusArithmetic
