/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeIntrinsicLeadingAction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeIntrinsicLeadingAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Coinvariants, mathlib/module/Mathlib.Algebra.Module.ZMod]
   utility: none
   digest: Cyclic projectivity and ordered mixed vanishing intrinsically extract a normalized commuting leading action. -/

import D5.S3.FiniteGroups.GroupAlgebra.FiniteFieldCyclicDimension
import D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.Tactic

/-!
For an arbitrary actual representation of an odd-prime elementary abelian
group, cyclic projectivity supplies the cyclic norm image and its dimension.
The independent vanishing of every ordered length-p augmentation product
identifies the augmentation ranges with the existing coinvariant kernel.

For a nonidentity anchor with augmentation D, the maps induced by D^(p-1)
and D^(p-2)Ng extract a normalized prime-field-linear action on those
coinvariants. Equal augmentation ranges force nonzero directions to be units.
Applying D^(p-3)Ng to the lift error in range D^2 forces commutation, including
p=3. The quotient-level equivalence characterizes this construction intrinsically.
No Jordan coordinates, linear section, coefficient map or field conjugacy is
assumed. Cyclic projectivity alone is not asserted to imply mixed vanishing.
-/

set_option autoImplicit false

noncomputable section
namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeIntrinsicLeadingAction

open Polynomial
open scoped BigOperators MonoidAlgebra
universe uK uV

private abbrev EAdd (p r : ℕ) := Fin r → ZMod p
private abbrev E (p r : ℕ) := Multiplicative (EAdd p r)

variable {p r m : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type uK} [Field K] [Finite K] [CharP K p]
variable {V : Type uV} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

local instance primeFieldAlgebra : Algebra (ZMod p) K := ZMod.algebra K p

/- This is exactly restriction of the K-scalar action on End_K(U) through the
standard prime-field embedding. It does not change U or its K-module structure. -/
local instance primeEndModule (rho : Representation K (E p r) V) :
    Module (ZMod p) (Module.End K (Representation.Coinvariants rho)) :=
  Module.compHom _ (algebraMap (ZMod p) K)

private def aug (rho : Representation K (E p r) V) (g : EAdd p r) : Module.End K V :=
  rho (Multiplicative.ofAdd g) - 1

private theorem aug_zero (rho : Representation K (E p r) V) : aug rho 0 = 0 := by
  simp [aug]

private theorem aug_add (rho : Representation K (E p r) V) (g k : EAdd p r) :
    aug rho (g + k) = aug rho g + aug rho k + aug rho g * aug rho k := by
  change rho (Multiplicative.ofAdd g * Multiplicative.ofAdd k) - 1 = _
  rw [rho.map_mul]
  dsimp [aug]
  noncomm_ring

private theorem aug_comm (rho : Representation K (E p r) V) (g k : EAdd p r) :
    Commute (aug rho g) (aug rho k) := by
  have hc : Commute (rho (Multiplicative.ofAdd g)) (rho (Multiplicative.ofAdd k)) := by
    change rho (Multiplicative.ofAdd g) * rho (Multiplicative.ofAdd k) = _
    rw [← rho.map_mul, ← rho.map_mul, mul_comm]
  exact (hc.sub_left (Commute.one_left _)).sub_right (Commute.one_right _)

private theorem group_pow_p (g : EAdd p r) :
    (Multiplicative.ofAdd g : E p r) ^ p = 1 := by
  apply Multiplicative.ext
  rw [toAdd_pow, toAdd_one]
  funext i
  exact ZModModule.char_nsmul_eq_zero p (g i)

private theorem actual_order {g : EAdd p r} (hg : g ≠ 0) :
    orderOf (Multiplicative.ofAdd g : E p r) = p := by
  apply orderOf_eq_prime (group_pow_p g)
  intro he
  exact hg (by simpa using congrArg (fun x : E p r => x.toAdd) he)

/- These are literal instances of the all-ordered-length-p hypothesis. -/
private theorem mixed_one_tail (rho : Representation K (E p r) V)
    (hmixed : ∀ xs : List (EAdd p r), xs.length = p → (xs.map (aug rho)).prod = 0)
    (a b : EAdd p r) : aug rho a ^ (p - 1) * aug rho b = 0 := by
  have hp : 3 ≤ p := by have := (Fact.out : 2 < p); omega
  have h := hmixed (List.replicate (p - 1) a ++ [b]) (by
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega)
  simpa only [List.map_append, List.map_replicate, List.map_cons, List.map_nil,
    List.prod_append, List.prod_replicate, List.prod_cons, List.prod_nil, mul_one] using h

private theorem mixed_two_tail (rho : Representation K (E p r) V)
    (hmixed : ∀ xs : List (EAdd p r), xs.length = p → (xs.map (aug rho)).prod = 0)
    (a b c : EAdd p r) : aug rho a ^ (p - 2) * aug rho b * aug rho c = 0 := by
  have hp : 3 ≤ p := by have := (Fact.out : 2 < p); omega
  have h := hmixed (List.replicate (p - 2) a ++ [b, c]) (by
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega)
  simpa only [List.map_append, List.map_replicate, List.map_cons, List.map_nil,
    List.prod_append, List.prod_replicate, List.prod_cons, List.prod_nil, mul_one,
    mul_assoc] using h

/- A private, live-consumed normalization lemma.  It uses only the base
ker D = range D^(p-1) and nilpotence, and constructs no chain/quotient framework. -/
private theorem ker_pow_eq_range_pow (D : Module.End K V)
    (hDp : D ^ p = 0) (hker : LinearMap.ker D = LinearMap.range (D ^ (p - 1))) :
    ∀ j : ℕ, j ≤ p → LinearMap.ker (D ^ j) = LinearMap.range (D ^ (p - j)) := by
  intro j
  induction j with
  | zero =>
      intro hj
      ext x
      constructor
      · intro hx
        have hx0 : x = 0 := by simpa using hx
        subst x
        exact ⟨0, by simp⟩
      · rintro ⟨y, hy⟩
        have hx0 : x = 0 := by simpa [hDp] using hy.symm
        simpa [hx0]
  | succ j ih =>
      intro hj
      have hj' : j ≤ p := by omega
      have hi := ih hj'
      have he1 : p - (j + 1) + 1 = p - j := by omega
      have he2 : p - (j + 1) + j = p - 1 := by omega
      have he3 : (j + 1) + (p - (j + 1)) = p := by omega
      ext x
      constructor
      · intro hx
        have hDx : D x ∈ LinearMap.ker (D ^ j) := by
          change (D ^ j) (D x) = 0
          change (D ^ j * D) x = 0
          rw [← pow_succ]
          exact hx
        rw [hi] at hDx
        obtain ⟨y, hy⟩ := hDx
        have hdiff : x - (D ^ (p - (j + 1))) y ∈ LinearMap.ker D := by
          change D (x - (D ^ (p - (j + 1))) y) = 0
          rw [map_sub]
          change D x - (D * D ^ (p - (j + 1))) y = 0
          rw [← pow_succ', he1, hy, sub_self]
        rw [hker] at hdiff
        obtain ⟨z, hz⟩ := hdiff
        refine ⟨y + (D ^ j) z, ?_⟩
        rw [map_add]
        change (D ^ (p - (j + 1))) y +
          (D ^ (p - (j + 1)) * D ^ j) z = x
        rw [← pow_add, he2, hz]
        abel
      · rintro ⟨y, rfl⟩
        change (D ^ (j + 1) * D ^ (p - (j + 1))) y = 0
        rw [← pow_add, he3, hDp]
        rfl

/- The original prime-field polynomial identity is reused at its defining module.
Map it to K[X], then evaluate at the actual K-linear operator. -/
private theorem geometric_norm_over_K :
    (∑ i ∈ Finset.range p, (X : K[X]) ^ i) = (X - 1) ^ (p - 1) := by
  have hX : Polynomial.mapRingHom (algebraMap (ZMod p) K)
      (X : (ZMod p)[X]) = (X : K[X]) := Polynomial.map_X _
  simpa only [map_sum, map_pow, map_sub, map_one, hX] using
    congrArg (Polynomial.mapRingHom (algebraMap (ZMod p) K))
      (PrimeFieldCyclicProjectivityDimension.geometric_norm_polynomial (p := p))

private theorem actual_norm (rho : Representation K (E p r) V)
    {g : EAdd p r} (hg : g ≠ 0) :
    (rho.comp (Subgroup.zpowers (Multiplicative.ofAdd g)).subtype).norm =
      aug rho g ^ (p - 1) := by
  classical
  let γ : E p r := Multiplicative.ofAdd g
  let e := finEquivZPowers (isOfFinOrder_of_finite γ)
  have hs : (∑ h : Subgroup.zpowers γ, rho (h : E p r)) =
      ∑ i : Fin (orderOf γ), rho (γ ^ (i : ℕ)) := by
    simpa only [e, finEquivZPowers_apply] using
      (e.sum_comp (fun h : Subgroup.zpowers γ => rho (h : E p r))).symm
  have ho : orderOf γ = p := actual_order hg
  rw [ho] at hs
  change (∑ h : Subgroup.zpowers γ, rho (h : E p r)) = _
  calc
    _ = ∑ i : Fin p, (rho γ) ^ (i : ℕ) := by simpa only [map_pow] using hs
    _ = ∑ i ∈ Finset.range p, (rho γ) ^ i :=
      (Finset.sum_range (fun i : ℕ => (rho γ) ^ i)).symm
    _ = (rho γ - 1) ^ (p - 1) := by
      simpa only [map_sum, map_pow, map_sub, map_one, Polynomial.aeval_X] using
        congrArg (Polynomial.aeval (rho γ)) (geometric_norm_over_K (p := p) (K := K))
    _ = aug rho g ^ (p - 1) := rfl

private theorem fixed_pow (T : Module.End K V) {v : V} (hv : T v = v) (n : ℕ) :
    (T ^ n) v = v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, hv]

private theorem cyclic_invariants (rho : Representation K (E p r) V) (g : EAdd p r) :
    (rho.comp (Subgroup.zpowers (Multiplicative.ofAdd g)).subtype).invariants =
      LinearMap.ker (aug rho g) := by
  classical
  let γ : E p r := Multiplicative.ofAdd g
  ext v
  constructor
  · intro hv
    change rho γ v - v = 0
    exact sub_eq_zero.mpr (hv ⟨γ, Subgroup.mem_zpowers γ⟩)
  · intro hv
    have hfix : rho γ v = v := sub_eq_zero.mp hv
    intro x
    let e := finEquivZPowers (isOfFinOrder_of_finite γ)
    obtain ⟨i, rfl⟩ := e.surjective x
    change rho (γ ^ (i : ℕ)) v = v
    rw [map_pow]
    exact fixed_pow (rho γ) hfix i

private theorem cyclic_power_data (rho : Representation K (E p r) V)
    (hproj : ∀ H : Subgroup (E p r), IsCyclic H →
      Module.Projective K[H] (rho.comp H.subtype).asModule)
    {g : EAdd p r} (hg : g ≠ 0) :
    aug rho g ^ p = 0 ∧
      LinearMap.ker (aug rho g) = LinearMap.range (aug rho g ^ (p - 1)) := by
  classical
  let γ : E p r := Multiplicative.ofAdd g
  let σ : Representation K (Subgroup.zpowers γ) V := rho.comp (Subgroup.zpowers γ).subtype
  have ho : orderOf γ = p := actual_order hg
  have hP : IsPGroup p (Subgroup.zpowers γ) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, ho, pow_one])
  have hpK : (p : K) ^ 1 = 0 := by
    simpa only [pow_one] using CharP.cast_eq_zero K p
  have hN :=
    ((PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective
      p 1 (by decide) hpK hP σ).mp (hproj _ inferInstance)).2
  have hpowγ : (rho γ) ^ p = 1 := by rw [← map_pow, group_pow_p g, map_one]
  have hpoly : ((X - 1 : K[X]) ^ p) = X ^ p - 1 := by
    simpa only [one_pow] using sub_pow_char (X : K[X]) 1
  have hDp : aug rho g ^ p = 0 := by
    have he := congrArg (Polynomial.aeval (rho γ)) hpoly
    simpa only [aug, map_pow, map_sub, map_one, Polynomial.aeval_X,
      hpowγ, one_pow, sub_self] using he
  refine ⟨hDp, le_antisymm ?_ ?_⟩
  · intro v hv
    have hinv : v ∈ σ.invariants := by rw [cyclic_invariants]; exact hv
    obtain ⟨x, hx⟩ := hN ⟨v, hinv⟩
    exact ⟨x, by simpa only [σ, actual_norm rho hg] using hx⟩
  · rintro v ⟨x, rfl⟩
    change (aug rho g * aug rho g ^ (p - 1)) x = 0
    rw [← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_le, hDp]
    rfl

private theorem cyclic_ker_finrank (rho : Representation K (E p r) V)
    (hproj : ∀ H : Subgroup (E p r), IsCyclic H →
      Module.Projective K[H] (rho.comp H.subtype).asModule)
    (hV : Module.finrank K V = p * m) {g : EAdd p r} (hg : g ≠ 0) :
    Module.finrank K (LinearMap.ker (aug rho g)) = m := by
  classical
  let γ : E p r := Multiplicative.ofAdd g
  have ho : orderOf γ = p := actual_order hg
  have hcard : Fintype.card (Subgroup.zpowers γ) = p := Fintype.card_zpowers.trans ho
  have hP : IsPGroup p (Subgroup.zpowers γ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_eq_fintype_card, hcard, pow_one])
  have hdim := FiniteFieldCyclicDimension.finrank_eq_card_mul_invariants p hP
    (rho.comp (Subgroup.zpowers γ).subtype) (hproj _ inferInstance)
  rw [hcard, cyclic_invariants] at hdim
  exact Nat.mul_left_cancel (Fact.out : p.Prime).pos (hdim.symm.trans hV)

/-- Intrinsic extraction on the existing coinvariants of an arbitrary actual
representation. The mixed-product assumption is independent of projectivity. -/
theorem intrinsic_leading_action
    (rho : Representation K (E p r) V)
    (hr : 0 < r) (hm : 0 < m) (hV : Module.finrank K V = p * m)
    (hproj : ∀ H : Subgroup (E p r), IsCyclic H →
      Module.Projective K[H] (rho.comp H.subtype).asModule)
    (hmixed : ∀ xs : List (EAdd p r), xs.length = p → (xs.map (aug rho)).prod = 0)
    (h : E p r) (hh : h ≠ 1) :
    ∃ A : EAdd p r →ₗ[ZMod p] Module.End K (Representation.Coinvariants rho),
      Module.finrank K (Representation.Coinvariants rho) = m ∧
      A h.toAdd = 1 ∧
      (∀ g, g ≠ 0 → IsUnit (A g)) ∧
      (∀ g k, Commute (A g) (A k)) ∧
      (∀ g v w,
        A g (Representation.Coinvariants.mk rho v) = Representation.Coinvariants.mk rho w ↔
          aug rho g v - aug rho h.toAdd w ∈ LinearMap.range (aug rho h.toAdd ^ 2)) := by
  classical
  have hp3 : 3 ≤ p := by have := (Fact.out : 2 < p); omega
  have he1 : p - 1 + 1 = p := by omega
  have he2 : p - 2 + 1 = p - 1 := by omega
  have he3 : p - 3 + 1 = p - 2 := by omega
  have he32 : p - 3 + 2 = p - 1 := by omega
  have ha : h.toAdd ≠ 0 := by
    intro hz
    apply hh
    apply Multiplicative.ext
    simpa using hz
  let D := aug rho h.toAdd
  have hdata := cyclic_power_data rho hproj ha
  have hDp : D ^ p = 0 := hdata.1
  have hker : LinearMap.ker D = LinearMap.range (D ^ (p - 1)) := hdata.2
  have hnorm := ker_pow_eq_range_pow D hDp hker
  have hker1 : LinearMap.ker (D ^ (p - 1)) = LinearMap.range D := by
    have hn : p - (p - 1) = 1 := by omega
    simpa only [hn, pow_one] using hnorm (p - 1) (by omega)
  have hker2 : LinearMap.ker (D ^ (p - 2)) = LinearMap.range (D ^ 2) := by
    have hn : p - (p - 2) = 2 := by omega
    simpa only [hn] using hnorm (p - 2) (by omega)
  have htopzero (g : EAdd p r) : D ^ (p - 1) * aug rho g = 0 :=
    mixed_one_tail rho hmixed h.toAdd g
  have hrange_le (g : EAdd p r) : LinearMap.range (aug rho g) ≤ LinearMap.range D := by
    rintro x ⟨v, rfl⟩
    rw [← hker1]
    exact LinearMap.congr_fun (htopzero g) v
  have hrange_eq (g : EAdd p r) (hg : g ≠ 0) :
      LinearMap.range (aug rho g) = LinearMap.range D := by
    apply le_antisymm (hrange_le g)
    have hgdata := cyclic_power_data rho hproj hg
    have hgker := ker_pow_eq_range_pow (aug rho g) hgdata.1 hgdata.2 (p - 1) (by omega)
    have hn : p - (p - 1) = 1 := by omega
    simp only [hn, pow_one] at hgker
    rintro x ⟨v, rfl⟩
    rw [← hgker]
    exact LinearMap.congr_fun (mixed_one_tail rho hmixed g h.toAdd) v
  have hM : Representation.Coinvariants.ker rho = LinearMap.range D := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro x ⟨⟨g, v⟩, rfl⟩
      exact hrange_le g.toAdd ⟨v, rfl⟩
    · rintro x ⟨v, rfl⟩
      exact Representation.Coinvariants.sub_mem_ker h v
  let q : V →ₗ[K] Representation.Coinvariants rho := Representation.Coinvariants.mk rho
  have hq : Function.Surjective q := Representation.Coinvariants.mk_surjective rho
  let e0 : V →ₗ[K] LinearMap.ker D :=
    (D ^ (p - 1)).codRestrict (LinearMap.ker D) (by
      intro v
      change (D * D ^ (p - 1)) v = 0
      rw [← pow_succ', he1, hDp]
      rfl)
  let e : Representation.Coinvariants rho →ₗ[K] LinearMap.ker D :=
    (Representation.Coinvariants.ker rho).liftQ e0 (by
      intro x hx
      rw [hM] at hx
      obtain ⟨t, rfl⟩ := hx
      apply Subtype.ext
      change (D ^ (p - 1) * D) t = 0
      rw [← pow_succ, he1, hDp]
      rfl)
  have heval (v : V) : (e (q v) : V) = (D ^ (p - 1)) v := rfl
  have hezero (u : Representation.Coinvariants rho) (hu : e u = 0) : u = 0 := by
    obtain ⟨v, rfl⟩ := hq u
    have hv : (D ^ (p - 1)) v = 0 := congrArg Subtype.val hu
    have hv' : v ∈ LinearMap.ker (D ^ (p - 1)) := hv
    rw [hker1] at hv'
    apply (Representation.Coinvariants.mk_eq_zero rho).mpr
    rw [hM]
    exact hv'
  have heinj : Function.Injective e := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hezero
    rw [map_sub, huv, sub_self]
  have hesurj : Function.Surjective e := by
    intro y
    have hy : (y : V) ∈ LinearMap.range (D ^ (p - 1)) := by
      rw [← hker]
      exact y.property
    obtain ⟨v, hv⟩ := hy
    exact ⟨q v, Subtype.ext hv⟩
  let eD : Representation.Coinvariants rho ≃ₗ[K] LinearMap.ker D :=
    LinearEquiv.ofBijective e ⟨heinj, hesurj⟩
  have heDval (v : V) : (eD (q v) : V) = (D ^ (p - 1)) v := heval v
  have hdimU : Module.finrank K (Representation.Coinvariants rho) = m :=
    eD.finrank_eq.trans (cyclic_ker_finrank rho hproj hV ha)
  let n0 (g : EAdd p r) : V →ₗ[K] LinearMap.ker D :=
    (D ^ (p - 2) * aug rho g).codRestrict (LinearMap.ker D) (by
      intro v
      change (D * (D ^ (p - 2) * aug rho g)) v = 0
      rw [← mul_assoc, ← pow_succ', he2]
      exact LinearMap.congr_fun (htopzero g) v)
  let n (g : EAdd p r) : Representation.Coinvariants rho →ₗ[K] LinearMap.ker D :=
    (Representation.Coinvariants.ker rho).liftQ (n0 g) (by
      intro x hx
      rw [hM] at hx
      obtain ⟨t, rfl⟩ := hx
      apply Subtype.ext
      change ((D ^ (p - 2) * aug rho g) * D) t = 0
      have hc : aug rho g * D = D * aug rho g := (aug_comm rho g h.toAdd).eq
      rw [mul_assoc, hc, ← mul_assoc, ← pow_succ, he2]
      exact LinearMap.congr_fun (htopzero g) t)
  have hnval (g : EAdd p r) (v : V) :
      (n g (q v) : V) = (D ^ (p - 2) * aug rho g) v := rfl
  let A0 (g : EAdd p r) : Module.End K (Representation.Coinvariants rho) :=
    eD.symm.toLinearMap.comp (n g)
  have hEA0 (g : EAdd p r) (u : Representation.Coinvariants rho) :
      eD (A0 g u) = n g u := eD.apply_symm_apply _
  have hAzero : A0 0 = 0 := by
    ext u
    apply eD.injective
    rw [hEA0, map_zero]
    obtain ⟨v, rfl⟩ := hq u
    apply Subtype.ext
    rw [hnval, aug_zero, mul_zero]
    rfl
  have hAadd (g k : EAdd p r) : A0 (g + k) = A0 g + A0 k := by
    ext u
    apply eD.injective
    change eD (A0 (g + k) u) = eD (A0 g u + A0 k u)
    rw [map_add, hEA0, hEA0, hEA0]
    obtain ⟨v, rfl⟩ := hq u
    apply Subtype.ext
    change (D ^ (p - 2)) (aug rho (g + k) v) =
      (D ^ (p - 2)) (aug rho g v) + (D ^ (p - 2)) (aug rho k v)
    rw [aug_add]
    simp only [LinearMap.add_apply, Module.End.mul_apply, map_add]
    have hz : (D ^ (p - 2)) (aug rho g (aug rho k v)) = 0 :=
      LinearMap.congr_fun (mixed_two_tail rho hmixed h.toAdd g k) v
    rw [hz, add_zero]
  let Aadd : EAdd p r →+ Module.End K (Representation.Coinvariants rho) :=
    { toFun := A0, map_zero' := hAzero, map_add' := hAadd }
  let A : EAdd p r →ₗ[ZMod p] Module.End K (Representation.Coinvariants rho) :=
    Aadd.toZModLinearMap p
  have hEA (g : EAdd p r) (u : Representation.Coinvariants rho) :
      eD (A g u) = n g u := hEA0 g u
  have hAval (g : EAdd p r) (v : V) :
      (eD (A g (q v)) : V) = (D ^ (p - 2)) (aug rho g v) := by
    rw [hEA, hnval]
    rfl
  have hAh : A h.toAdd = 1 := by
    ext u
    obtain ⟨v, rfl⟩ := hq u
    apply eD.injective
    apply Subtype.ext
    rw [hAval]
    change (D ^ (p - 2) * D) v = (D ^ (p - 1)) v
    rw [← pow_succ, he2]
  have hnSurj (g : EAdd p r) (hg : g ≠ 0) : Function.Surjective (n g) := by
    intro y
    have hy : (y : V) ∈ LinearMap.range (D ^ (p - 1)) := by
      rw [← hker]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    have hDx : D x ∈ LinearMap.range (aug rho g) := by
      rw [hrange_eq g hg]
      exact ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hDx
    refine ⟨q z, Subtype.ext ?_⟩
    rw [hnval]
    change (D ^ (p - 2)) (aug rho g z) = (y : V)
    rw [hz]
    change (D ^ (p - 2) * D) x = (y : V)
    rw [← pow_succ, he2]
    exact hx
  have hunit (g : EAdd p r) (hg : g ≠ 0) : IsUnit (A g) := by
    apply (LinearMap.isUnit_iff_range_eq_top _).mpr
    apply LinearMap.range_eq_top.mpr
    intro u
    obtain ⟨v, hv⟩ := hnSurj g hg (eD u)
    refine ⟨v, eD.injective ?_⟩
    rw [hEA, hv]
  have hcert (g : EAdd p r) (v w : V) :
      A g (q v) = q w ↔ aug rho g v - D w ∈ LinearMap.range (D ^ 2) := by
    have hEq : A g (q v) = q w ↔
        (D ^ (p - 2)) (aug rho g v) = (D ^ (p - 1)) w := by
      constructor
      · intro heq
        have hv := congrArg (fun u => (eD u : V)) heq
        simpa only [hAval, heDval] using hv
      · intro heq
        apply eD.injective
        apply Subtype.ext
        rw [hAval, heDval]
        exact heq
    rw [hEq, ← hker2]
    change _ ↔ (D ^ (p - 2)) (aug rho g v - D w) = 0
    rw [map_sub]
    have hDw : (D ^ (p - 2)) (D w) = (D ^ (p - 1)) w := by
      change (D ^ (p - 2) * D) w = _
      rw [← pow_succ, he2]
    rw [hDw, sub_eq_zero]
  /- This identity is proved from the lift error, not supplied as a coefficient
  or multiplication assumption. hp3 and he3/he32 cover p=3 explicitly. -/
  have hproduct (g k : EAdd p r) (v w : V) (hw : q w = A k (q v)) :
      (eD (A g (A k (q v))) : V) = (D ^ (p - 3) * aug rho g * aug rho k) v := by
    have hrel := (hcert k v w).mp hw.symm
    obtain ⟨t, ht⟩ := hrel
    have hk : aug rho k v = D w + (D ^ 2) t := by rw [ht]; abel
    have hc : aug rho g * D = D * aug rho g := (aug_comm rho g h.toAdd).eq
    have hc2 : aug rho g * D ^ 2 = D ^ 2 * aug rho g :=
      ((aug_comm rho g h.toAdd).pow_right 2).eq
    have hlin : (D ^ (p - 3) * aug rho g) * D = D ^ (p - 2) * aug rho g := by
      rw [mul_assoc, hc, ← mul_assoc, ← pow_succ, he3]
    have herr : (D ^ (p - 3) * aug rho g) * D ^ 2 = 0 := by
      rw [mul_assoc, hc2, ← mul_assoc, ← pow_add, he32, htopzero g]
    have htzero : (D ^ (p - 3) * aug rho g) ((D ^ 2) t) = 0 :=
      LinearMap.congr_fun herr t
    have hDw : (D ^ (p - 3) * aug rho g) (D w) =
        (D ^ (p - 2) * aug rho g) w := LinearMap.congr_fun hlin w
    have heq := congrArg (fun x : V => (D ^ (p - 3) * aug rho g) x) hk
    rw [map_add, htzero, add_zero, hDw] at heq
    rw [← hw, hAval]
    exact heq.symm
  have hcomm (g k : EAdd p r) : Commute (A g) (A k) := by
    change A g * A k = A k * A g
    ext u
    obtain ⟨v, rfl⟩ := hq u
    obtain ⟨w, hw⟩ := hq (A k (q v))
    obtain ⟨w', hw'⟩ := hq (A g (q v))
    apply eD.injective
    apply Subtype.ext
    rw [hproduct g k v w hw, hproduct k g v w' hw']
    simpa only [mul_assoc] using LinearMap.congr_fun
      (congrArg (fun T : Module.End K V => D ^ (p - 3) * T) (aug_comm rho g k).eq) v
  exact ⟨A, hdimU, hAh, hunit, hcomm, hcert⟩

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeIntrinsicLeadingAction
