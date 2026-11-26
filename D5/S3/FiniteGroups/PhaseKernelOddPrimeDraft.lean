import Mathlib.GroupTheory.Sylow

/-!
# Commuting odd-prime lifts through a phase kernel

Group-theoretic lifting step for the P48q anomaly obstruction in the search for a
strongly rational holomorphic VOA of central charge 48 with `V₁ = 0` and `V₂ = ℂω`.
-/

set_option autoImplicit false

namespace PhaseKernelOddPrimeDraft

/-- A normalizing lift that inverts the kernel can be made to commute
with the odd-prime lift by a square-root correction inside the same p-subgroup. -/
private theorem lift_of_normalizes {G H : Type*} [Group G] [Group H]
    {p : ℕ} (hcop : p.Coprime 2) (f : G →* H) (S : Subgroup G)
    (hS : IsPGroup p S) {g u : G} (hg : g ∈ S)
    (hu : u ∈ Subgroup.normalizer (S : Set G))
    (hcomm : Commute (f u) (f g)) (hpow : f g ^ p = 1)
    (hinv : ∀ z ∈ f.ker, u * z * u⁻¹ = z⁻¹) :
    ∃ y : G, f y = f g ∧ y ^ p = 1 ∧ Commute y u := by
  let K : Subgroup G := S ⊓ f.ker
  have hK : IsPGroup p K := hS.to_inf_left
  let square : K ≃ K := hK.powEquiv hcop
  let c := u * g * u⁻¹ * g⁻¹
  have hcS : c ∈ S :=
    S.mul_mem ((Subgroup.mem_normalizer_iff.mp hu g).mp hg) (S.inv_mem hg)
  have hcKer : c ∈ f.ker := by
    change f (u * g * u⁻¹ * g⁻¹) = 1
    simp only [map_mul, map_inv, hcomm.eq, mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨b, hb⟩ := square.surjective (⟨c, ⟨hcS, hcKer⟩⟩ : K)
  have hb2 : (b : G) ^ 2 = c := congrArg (fun z : K => (z : G)) hb
  have hbKer : (b : G) ∈ f.ker := b.property.2
  let y := (b : G) * g
  have hyS : y ∈ S := S.mul_mem b.property.1 hg
  have hyf : f y = f g := by
    change f ((b : G) * g) = f g
    rw [map_mul, MonoidHom.mem_ker.mp hbKer, one_mul]
  have hcg : MulAut.conj u g = c * g := by
    change u * g * u⁻¹ = (u * g * u⁻¹ * g⁻¹) * g
    rw [inv_mul_cancel_right]
  have hyfix : MulAut.conj u y = y := by
    change MulAut.conj u ((b : G) * g) = (b : G) * g
    rw [map_mul, MulAut.conj_apply u (b : G), hinv _ hbKer, hcg, ← hb2, pow_two]
    simp only [mul_assoc, inv_mul_cancel_left]
  have hyComm : Commute y u := by
    have heq : u * y * u⁻¹ = y := hyfix
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  have hypK : y ^ p ∈ K := by
    refine ⟨S.pow_mem hyS p, MonoidHom.mem_ker.mpr ?_⟩
    rw [map_pow, hyf, hpow]
  have hselfInv : y ^ p = (y ^ p)⁻¹ := by
    calc
      y ^ p = MulAut.conj u (y ^ p) := by rw [map_pow, hyfix]
      _ = (y ^ p)⁻¹ := hinv _ hypK.2
  have hsqOne : (y ^ p) ^ 2 = 1 := by
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp hselfInv
  have hpK : (⟨y ^ p, hypK⟩ : K) = 1 := by
    apply square.injective
    apply Subtype.ext
    change (y ^ p) ^ 2 = (1 : G) ^ 2
    rw [hsqOne, one_pow]
  exact ⟨y, hyf, congrArg (fun z : K => (z : G)) hpK, hyComm⟩

/-- A commuting pair in the image of a finite group homomorphism
lifts to a commuting pair with the same odd-prime order on the first factor,
provided every lift of the second factor acts on the kernel by inversion. -/
theorem exists_commuting_odd_prime_lifts {G H : Type*} [Group G] [Group H] [Finite G]
    (pi : G →* H) (x t : G) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (horder : orderOf (pi x) = p) (hcomm : Commute (pi t) (pi x))
    (hinv : ∀ u : G, pi u = pi t → ∀ z ∈ pi.ker, u * z * u⁻¹ = z⁻¹) :
    ∃ x' t' : G, pi x' = pi x ∧ pi t' = pi t ∧ x' ^ p = 1 ∧ Commute x' t' ∧ orderOf x' = p := by
  letI : Fact p.Prime := ⟨hp⟩
  let C := Subgroup.zpowers (pi x)
  let E := C.comap pi
  let M := Subgroup.normalizer (E : Set G)
  let N := E.subgroupOf M
  letI : N.Normal := Subgroup.normal_in_normalizer (H := E)
  let f : M →* H := pi.comp M.subtype
  have hxE : x ∈ E := Subgroup.mem_zpowers (pi x)
  have htM : t ∈ M := by
    apply Subgroup.mem_normalizer_fintype (S := (E : Set G))
    intro n hn
    have hnC : pi n ∈ C := hn
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hnC
    have htn : Commute (pi t) (pi n) := by
      rw [← hj]
      exact hcomm.zpow_right j
    change pi (t * n * t⁻¹) ∈ C
    simpa only [map_mul, map_inv, htn.eq, mul_inv_cancel_right] using hnC
  let xN : N := ⟨⟨x, Subgroup.le_normalizer hxE⟩, hxE⟩
  let tM : M := ⟨t, htM⟩
  let q : N →* C := (f.comp N.subtype).codRestrict C (fun n => n.property)
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp v.property
    refine ⟨xN ^ j, Subtype.ext ?_⟩
    rw [map_zpow q]
    exact hj
  let P : Sylow p N := Sylow.nonempty.some
  have hC : IsPGroup p C := IsPGroup.of_card (n := 1) (by
    simpa only [C, Nat.card_zpowers, pow_one] using horder)
  have hmap : P.toSubgroup.map q = ⊤ := by
    have htop : (⊤ : Subgroup C) = (P.mapSurjective hq).toSubgroup :=
      (P.mapSurjective hq).is_maximal' (hC.to_subgroup ⊤) le_top
    simpa only [Sylow.coe_mapSurjective] using htop.symm
  let S : Subgroup M := P.toSubgroup.map N.subtype
  have lift_mem_sylow (v : C) : ∃ s : M, s ∈ S ∧ f s = (v : H) := by
    have hv : v ∈ P.toSubgroup.map q := by
      rw [hmap]
      exact Subgroup.mem_top v
    obtain ⟨w, hw, hqw⟩ := Subgroup.mem_map.mp hv
    exact ⟨(w : M), Subgroup.mem_map_of_mem N.subtype hw,
      congrArg (fun z : C => (z : H)) hqw⟩
  obtain ⟨g, hg, hfg⟩ := lift_mem_sylow ⟨pi x, Subgroup.mem_zpowers _⟩

  -- Frattini's argument factors t into a normalizer element and an element of N.
  have hsup : Subgroup.normalizer (S : Set M) ⊔ N = ⊤ :=
    Sylow.normalizer_sup_eq_top P
  have htSup : tM ∈ Subgroup.normalizer (S : Set M) ⊔ N := by
    rw [hsup]
    exact Subgroup.mem_top tM
  obtain ⟨a, ha, n, hn, han⟩ := Subgroup.mem_sup_of_normal_right.mp htSup
  obtain ⟨s, hs, hsn⟩ := lift_mem_sylow ⟨f n, hn⟩
  let u := a * s
  have hu : u ∈ Subgroup.normalizer (S : Set M) :=
    (Subgroup.normalizer (S : Set M)).mul_mem ha (Subgroup.le_normalizer hs)
  have hfu : f u = pi t := by
    calc
      f u = f a * f s := f.map_mul _ _
      _ = f a * f n := by rw [hsn]
      _ = f (a * n) := (f.map_mul _ _).symm
      _ = pi t := congrArg f han
  have hcomm' : Commute (f u) (f g) := by
    rw [hfu, hfg]
    exact hcomm
  have hpow : f g ^ p = 1 := by
    rw [hfg, ← horder]
    exact pow_orderOf_eq_one (pi x)
  have hinv' (z : M) (hz : z ∈ f.ker) : u * z * u⁻¹ = z⁻¹ :=
    Subtype.ext (hinv (u : G) hfu (z : G) hz)
  obtain ⟨y, hy, hyp, hyu⟩ := lift_of_normalizes hodd.coprime_two_right f S
    (P.isPGroup'.map N.subtype) hg hu hcomm' hpow hinv'
  have hyG : pi (y : G) = pi x := hy.trans hfg
  have hypG : (y : G) ^ p = 1 := congrArg (fun v : M => (v : G)) hyp
  have horderG : orderOf (y : G) = p := by
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hypG)
    rw [← horder, ← hyG]
    exact orderOf_map_dvd pi (y : G)
  exact ⟨(y : G), (u : G), hyG, hfu, hypG,
    congrArg (fun v : M => (v : G)) hyu.eq, horderG⟩

end PhaseKernelOddPrimeDraft

#print axioms PhaseKernelOddPrimeDraft.exists_commuting_odd_prime_lifts
