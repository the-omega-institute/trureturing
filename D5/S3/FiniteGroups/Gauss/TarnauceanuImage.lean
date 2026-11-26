/- GID: D5/S3/FiniteGroups/Gauss/TarnauceanuImage
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Gauss/TarnauceanuImage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Basic, mathlib/module/Mathlib.Data.SetLike.Fintype, mathlib/module/Mathlib.Tactic.Positivity]
   utility: none
   digest: Cyclic-product Gauss values disprove simultaneous closedness and discreteness. -/

/- Escape audit unfinished for image_not_closed_and_discrete.
   The exact closed proposition has no source state binder. A template must
   bind the same image to both topological predicates with faithful variation
   and dependence evidence. See https://github.com/the-omega-institute/trureturing/issues/34522. -/

import D5.S3.FiniteGroups.CyclicPrimePowerAction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.SetLike.Fintype
import Mathlib.Tactic.Positivity

namespace D5.S3.FiniteGroups.Gauss.TarnauceanuImage

open D5.S3.FiniteGroups.CyclicPrimePowerAction
open D5.S3.FiniteGroups.SubgroupConjugacyRatio (FiniteGroup)
open Subgroup MonoidHom
open scoped BigOperators Classical

set_option autoImplicit false
set_option linter.style.haveILetI false

variable {G : Type*} [Group G]

/-- Tărnăuceanu's invariant, summed over the entire lattice of actual subgroups. -/
noncomputable def gauss (G : Type*) [Group G] : ℝ :=
  (∑ᶠ H : Subgroup G, (Nat.card (MulAut H) : ℝ)) / (Nat.card G : ℝ)

private def generatorFiberEquiv [Finite G] (H : Subgroup G) :
    {x : G // zpowers x = H} ≃ {x : H // orderOf x = Nat.card H} where
  toFun x := by
    obtain ⟨x, hx⟩ := x
    have hxmem : x ∈ H := by rw [← hx]; exact mem_zpowers x
    refine ⟨⟨x, hxmem⟩, orderOf_eq_card_of_forall_mem_zpowers ?_⟩
    intro y
    have hy : y.val ∈ zpowers x := hx.symm ▸ y.property
    obtain ⟨k, hk⟩ := hy
    exact ⟨k, Subtype.ext hk⟩
  invFun x := by
    refine ⟨x.val.val, eq_of_le_of_card_ge (zpowers_le_of_mem x.val.property) ?_⟩
    rw [Nat.card_zpowers, ← Subgroup.orderOf_mk x.val.val x.val.property, x.property]
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_generatorFiber [Finite G] (H : Subgroup G) :
    Nat.card {x : G // zpowers x = H} =
      if IsCyclic H then Nat.card (MulAut H) else 0 := by
  classical
  rw [Nat.card_congr (generatorFiberEquiv H)]
  split_ifs with h
  · letI := h
    letI := Fintype.ofFinite H
    letI := Fintype.ofFinite {x : H // orderOf x = Nat.card H}
    rw [IsCyclic.card_mulAut, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simpa only [Nat.card_eq_fintype_card] using
      (IsCyclic.card_orderOf_eq_totient (α := H) (d := Fintype.card H) dvd_rfl)
  · haveI : IsEmpty {x : H // orderOf x = Nat.card H} :=
      ⟨fun x => h (isCyclic_of_orderOf_eq_card x.val x.property)⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

/-- Isomorphisms carry actual subgroups and their full automorphism groups along with them. -/
private theorem gauss_mulEquiv {K : Type*} [Group K] [Finite G] [Finite K] (e : G ≃* K) :
    gauss G = gauss K := by
  classical
  letI := Fintype.ofFinite (Subgroup G)
  letI := Fintype.ofFinite (Subgroup K)
  simp only [gauss, finsum_eq_sum_of_fintype, Nat.card_congr e.toEquiv]
  congr 1
  exact Fintype.sum_equiv e.mapSubgroup.toEquiv _ _ (fun H => by
    exact_mod_cast Nat.card_congr (MulAut.congr (e.subgroupMap H)).toEquiv)

/-- Counting generators gives the cyclic contribution in Equation (1). -/
private theorem cyclic_contribution [Finite G] :
    (∑ᶠ H : {H : Subgroup G // IsCyclic H}, (Nat.card (MulAut H.val) : ℝ)) =
      Nat.card G := by
  classical
  letI := Fintype.ofFinite (Subgroup G)
  letI := Fintype.ofFinite G
  have hc := Nat.card_congr (Equiv.sigmaFiberEquiv (zpowers : G → Subgroup G))
  rw [Nat.card_sigma] at hc
  simp only [card_generatorFiber] at hc
  have hrc := congrArg (fun n : ℕ => (n : ℝ)) hc
  push_cast at hrc
  rw [finsum_eq_sum_of_fintype, ← hrc]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) (fun H : Subgroup G =>
    (Nat.card (MulAut H) : ℝ))).symm

private theorem gauss_eq_one_add_noncyclic [Finite G] :
    gauss G = 1 +
      (∑ᶠ H : {H : Subgroup G // ¬ IsCyclic H}, (Nat.card (MulAut H.val) : ℝ)) /
        (Nat.card G : ℝ) := by
  classical
  letI := Fintype.ofFinite (Subgroup G)
  unfold gauss
  have hp : (Nat.card G : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [← div_self hp, ← add_div]
  congr 1
  rw [← cyclic_contribution (G := G)]
  simp only [finsum_eq_sum_of_fintype]
  exact (Fintype.sum_subtype_add_sum_subtype (fun H : Subgroup G => IsCyclic H)
    (fun H => (Nat.card (MulAut H) : ℝ))).symm

private theorem one_le_gauss [Finite G] : 1 ≤ gauss G := by
  classical
  letI := Fintype.ofFinite (Subgroup G)
  rw [gauss_eq_one_add_noncyclic, finsum_eq_sum_of_fintype]
  exact le_add_of_nonneg_right (by positivity)

abbrev Family (n : ℕ) := Cyclic (2 ^ n) × Cyclic 2

private instance familyPowNeZero (n : ℕ) : NeZero (2 ^ n) := ⟨by positivity⟩

private theorem card_family (n : ℕ) : Nat.card (Family n) = 2 ^ n * 2 := by
  rw [Nat.card_prod, cyclic_card, cyclic_card]

private theorem noncyclic_prod_top_iff {P : Type*} [Group P] [Finite P]
    (K : Subgroup P) : ¬ IsCyclic (K.prod (⊤ : Subgroup (Cyclic 2))) ↔
      ¬ (IsCyclic K ∧ (Nat.card K).Coprime 2) := by
  have e := (K.prodEquiv (⊤ : Subgroup (Cyclic 2))).trans
    (MulEquiv.prodCongr (MulEquiv.refl K) Subgroup.topEquiv)
  rw [e.isCyclic, Group.isCyclic_prod_iff, cyclic_card]
  exact not_congr (by simp only [show IsCyclic (Cyclic 2) from inferInstance, true_and])

/-- Projection identifies the actual noncyclic subgroups with the nontrivial subgroups of
the first cyclic factor. The inverse takes the full inverse image. -/
private noncomputable def noncyclicSubgroupProjection (n : ℕ) :
    {H : Subgroup (Family n) // ¬ IsCyclic H} ≃
      {K : Subgroup (Cyclic (2 ^ n)) // K ≠ ⊥} := by
  let π := fst (Cyclic (2 ^ n)) (Cyclic 2)
  let ι := inr (Cyclic (2 ^ n)) (Cyclic 2)
  have hker : ∀ H : Subgroup (Family n), ¬ IsCyclic H → π.ker ≤ H := by
    intro H hH
    letI : Fact (Nat.card (Cyclic 2)).Prime := ⟨by rw [cyclic_card]; decide⟩
    rcases (H.comap ι).eq_bot_or_eq_top_of_prime_card with h | h
    · exfalso
      apply hH
      apply isCyclic_of_injective (π.domRestrict H)
      apply (π.domRestrict H).ker_eq_bot_iff.mp
      apply bot_unique
      intro x hx
      have hx₁ : x.val.1 = 1 := hx
      have hx₂ : x.val.2 ∈ H.comap ι := by
        change (1, x.val.2) ∈ H
        simpa only [← hx₁, Prod.eta] using x.property
      rw [h, mem_bot] at hx₂
      exact mem_bot.mpr (Subtype.ext (Prod.ext hx₁ hx₂))
    · rintro ⟨a,b⟩ hab
      have ha : a = 1 := hab
      subst a
      change b ∈ H.comap ι
      rw [h]
      trivial
  have hn : ∀ K : Subgroup (Cyclic (2 ^ n)),
      (¬ IsCyclic (K.comap π)) ↔ K ≠ ⊥ := by
    intro K
    rw [← Subgroup.prod_top, noncyclic_prod_top_iff]
    have hd : Nat.card K ∣ 2 ^ n := by
      simpa only [cyclic_card] using card_subgroup_dvd_card K
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    rw [ne_eq, Subgroup.eq_bot_iff_card, hj]
    simp only [show IsCyclic K from inferInstance, true_and]
    cases j with
    | zero => simp
    | succ j =>
      have hdiv : 2 ∣ 2 ^ (j + 1) := dvd_pow_self _ (by omega)
      have hc : ¬ (2 ^ (j + 1)).Coprime 2 := by
        rw [Nat.Coprime, Nat.gcd_eq_right hdiv]
        decide
      simp [hc]
  have hmap : ∀ K : Subgroup (Cyclic (2 ^ n)), (K.comap π).map π = K := by
    intro K
    apply map_comap_eq_self
    intro a _
    exact ⟨(a,1), rfl⟩
  refine
    { toFun := fun H => ⟨H.val.map π, (hn _).mp (by
        rw [Subgroup.comap_map_eq_self (hker H.val H.property)]
        exact H.property)⟩
      invFun := fun K => ⟨K.val.comap π, (hn _).mpr K.property⟩
      left_inv := fun H => Subtype.ext (Subgroup.comap_map_eq_self (hker H.val H.property))
      right_inv := fun K => Subtype.ext (hmap K.val) }

private theorem ker_power_ne_bot_iff (n : ℕ) (j : Fin (n + 1)) :
    (powMonoidHom (2 ^ j.val) : Cyclic (2 ^ n) →* Cyclic (2 ^ n)).ker ≠ ⊥ ↔
      j.val ≠ 0 := by
  rw [ne_eq, Subgroup.eq_bot_iff_card, kernel_power_card (cyclic_card _)]
  exact not_congr (pow_eq_one_iff_right (by decide : (2 : ℕ) ≠ 1))

/-- There is one actual noncyclic subgroup for each positive exponent up to n. -/
private noncomputable def noncyclicSubgroupEquiv (n : ℕ) :
    {H : Subgroup (Family n) // ¬ IsCyclic H} ≃ Fin n := by
  let e := cyclicSubgroupEquiv Nat.prime_two (cyclic_card (2 ^ n))
  let e' : {K : Subgroup (Cyclic (2 ^ n)) // K ≠ ⊥} ≃ {j : Fin (n + 1) // j.val ≠ 0} :=
    e.subtypeEquiv (fun K => by
      have h := ker_power_ne_bot_iff n (e K)
      change e.symm (e K) ≠ ⊥ ↔ _ at h
      rwa [e.symm_apply_apply] at h)
  exact (noncyclicSubgroupProjection n).trans (e'.trans
    { toFun := fun j => ⟨j.val.val - 1, by have := j.val.isLt; have := j.property; omega⟩
      invFun := fun j => ⟨j.succ, by simp⟩
      left_inv := fun j => Subtype.ext (Fin.ext (by have := j.property; simp; omega))
      right_inv := fun j => Fin.ext (by simp) })

/-- The actual subgroup indexed by j has cyclic first factor of order 2^(j+1). -/
private noncomputable def noncyclicSubgroupMulEquiv (n : ℕ) (j : Fin n) :
    ((noncyclicSubgroupEquiv n).symm j).val ≃* Family (j.val + 1) := by
  let K : Subgroup (Cyclic (2 ^ n)) := (powMonoidHom (2 ^ j.succ.val)).ker
  have hK : Nat.card K = 2 ^ (j.val + 1) := kernel_power_card (cyclic_card _) j.succ
  let e : K ≃* Cyclic (2 ^ (j.val + 1)) := by
    rw [← hK]
    exact (zmodCyclicMulEquiv (inferInstance : IsCyclic K)).symm
  have hsub : ((noncyclicSubgroupEquiv n).symm j).val = K.prod ⊤ := by
    unfold noncyclicSubgroupEquiv noncyclicSubgroupProjection
    exact (Subgroup.prod_top K).symm
  rw [hsub]
  exact (K.prodEquiv (⊤ : Subgroup (Cyclic 2))).trans
    (MulEquiv.prodCongr e Subgroup.topEquiv)

private theorem gauss_family_eq_sum (n : ℕ) :
    gauss (Family n) = 1 +
      (∑ j : Fin n, (Nat.card (MulAut (Family (j.val + 1))) : ℝ)) / (2 ^ n * 2) := by
  classical
  letI := Fintype.ofFinite {H : Subgroup (Family n) // ¬ IsCyclic H}
  rw [gauss_eq_one_add_noncyclic, finsum_eq_sum_of_fintype, card_family]
  push_cast
  congr 2
  apply Fintype.sum_equiv (noncyclicSubgroupEquiv n)
  intro H
  have e := noncyclicSubgroupMulEquiv n (noncyclicSubgroupEquiv n H)
  rw [Equiv.symm_apply_apply] at e
  exact_mod_cast Nat.card_congr (MulAut.congr e).toEquiv

private def a (n : ℕ) : Family n := (generator (2 ^ n), 1)
private def b (n : ℕ) : Family n := (1, generator 2)

private theorem order_a (n : ℕ) : orderOf (a n) = 2 ^ n := by
  change orderOf (inl (Cyclic (2 ^ n)) (Cyclic 2) (generator (2 ^ n))) = _
  rw [orderOf_injective _ (fun _ _ h => congrArg Prod.fst h), generator_order]

private theorem order_b (n : ℕ) : orderOf (b n) = 2 := by
  change orderOf (inr (Cyclic (2 ^ n)) (Cyclic 2) (generator 2)) = _
  rw [orderOf_injective _ (fun _ _ h => congrArg Prod.snd h), generator_order]

private theorem cyclic_two_sq (v : Cyclic 2) : v ^ 2 = 1 := by
  simpa only [cyclic_card] using (pow_card_eq_one' (x := v))

private theorem cyclic_two_eq_gen {v : Cyclic 2} (hv : v ≠ 1) : v = generator 2 := by
  revert v
  decide

/-- The endomorphism specified by the images of the two cyclic generators. -/
private noncomputable def ofImages (n : ℕ) (x y : Family n)
    (hx : x ^ (2 ^ n) = 1) (hy : y ^ 2 = 1) : Family n →* Family n :=
  (monoidHomOfForallMemZpowers (generator_generates (2 ^ n))
    (by rw [generator_order]; exact orderOf_dvd_of_pow_eq_one hx)).coprod
  (monoidHomOfForallMemZpowers (generator_generates 2)
    (by rw [generator_order]; exact orderOf_dvd_of_pow_eq_one hy))

@[simp] private theorem ofImages_a (n : ℕ) (x y : Family n) (hx) (hy) :
    ofImages n x y hx hy (a n) = x := by
  simp [ofImages, a, coprod_apply]

@[simp] private theorem ofImages_b (n : ℕ) (x y : Family n) (hx) (hy) :
    ofImages n x y hx hy (b n) = y := by
  simp [ofImages, b, coprod_apply]

private theorem hom_ext (n : ℕ) {f g : Family n →* Family n}
    (ha : f (a n) = g (a n)) (hb : f (b n) = g (b n)) : f = g := by
  let l := inl (Cyclic (2 ^ n)) (Cyclic 2)
  let r := inr (Cyclic (2 ^ n)) (Cyclic 2)
  have hl : f.comp l = g.comp l :=
    (MonoidHom.eq_iff_eq_on_generator (generator_generates (2 ^ n)) _ _).mpr ha
  have hr : f.comp r = g.comp r :=
    (MonoidHom.eq_iff_eq_on_generator (generator_generates 2) _ _).mpr hb
  apply MonoidHom.ext
  intro z
  let p : Family n := l z.1
  let q : Family n := r z.2
  have hz : p * q = z := by
    change (z.1 * 1, 1 * z.2) = z
    simp
  rw [← hz, map_mul, map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun hl z.1) (DFunLike.congr_fun hr z.2)

private theorem aut_ext (n : ℕ) {f g : MulAut (Family n)}
    (ha : f (a n) = g (a n)) (hb : f (b n) = g (b n)) : f = g :=
  MulEquiv.toMonoidHom_injective (hom_ext n ha hb)

/-- The six ordered pairs of distinct nonidentity elements give the Klein four automorphisms. -/
private theorem card_aut_klein : Nat.card (MulAut (Family 1)) = 6 := by
  let P := {p : Family 1 × Family 1 // p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.2 ≠ p.1}
  have ha : a 1 ≠ 1 := by decide
  have hb : b 1 ≠ 1 := by decide
  have hab : b 1 ≠ a 1 := by decide
  have hsq : ∀ x : Family 1, x ^ 2 = 1 := by decide
  have hall : ∀ p : Family 1 × Family 1 × Family 1,
      p.1 ≠ 1 → p.2.1 ≠ 1 → p.2.1 ≠ p.1 →
      p.2.2 = 1 ∨ p.2.2 = p.1 ∨ p.2.2 = p.2.1 ∨ p.2.2 = p.1 * p.2.1 := by decide
  let eval : MulAut (Family 1) → P := fun f => ⟨(f (a 1), f (b 1)),
    fun h => ha (f.injective (h.trans f.map_one.symm)),
    fun h => hb (f.injective (h.trans f.map_one.symm)),
    fun h => hab (f.injective h)⟩
  have hbij : Function.Bijective eval := by
    constructor
    · intro f g h
      exact aut_ext 1 (congrArg (fun p : P => p.val.1) h)
        (congrArg (fun p : P => p.val.2) h)
    · rintro ⟨⟨x,y⟩,h⟩
      let f := ofImages 1 x y (hsq x) (hsq y)
      have hs : Function.Surjective f := by
        intro z
        rcases hall (x,y,z) h.1 h.2.1 h.2.2 with hz | hz | hz | hz
        · exact ⟨1, f.map_one.trans hz.symm⟩
        · exact ⟨a 1, (ofImages_a 1 x y (hsq x) (hsq y)).trans hz.symm⟩
        · exact ⟨b 1, (ofImages_b 1 x y (hsq x) (hsq y)).trans hz.symm⟩
        · refine ⟨a 1 * b 1, ?_⟩
          change z = x * y at hz
          simp [f, hz]
      refine ⟨MulEquiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hs, hs⟩, ?_⟩
      apply Subtype.ext
      change (f (a 1), f (b 1)) = (x,y)
      simp [f]
  rw [Nat.card_congr (Equiv.ofBijective eval hbij), Nat.card_eq_fintype_card]
  decide

private abbrev Large (k : ℕ) := Cyclic (2 ^ (k + 2))

private theorem pow_large (k : ℕ) (x : Family (k + 2)) : x ^ (2 ^ (k + 2)) = 1 := by
  have h₁ : x.1 ^ (2 ^ (k + 2)) = 1 := by
    simpa only [cyclic_card] using (pow_card_eq_one' (x := x.1))
  have h₂ : x.2 ^ (2 ^ (k + 2)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_pow_eq_one (cyclic_two_sq x.2)).trans (dvd_pow_self _ (by omega)))
  exact Prod.ext h₁ h₂

private theorem snd_half_pow (k : ℕ) (x : Family (k + 2)) :
    (x ^ (2 ^ (k + 1))).2 = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_of_pow_eq_one (cyclic_two_sq x.2)).trans (dvd_pow_self _ (by omega)))

private theorem card_involutions_fst (k : ℕ) :
    Nat.card (powMonoidHom 2 : Large k →* Large k).ker = 2 := by
  rw [IsCyclic.card_powMonoidHom_ker, cyclic_card, Nat.gcd_eq_right (dvd_pow_self _ (by omega))]

private theorem order_fst_of_order (k : ℕ) (x : Family (k + 2))
    (hx : orderOf x = 2 ^ (k + 2)) : orderOf x.1 = 2 ^ (k + 2) := by
  have hdiv : orderOf x.1 ∣ 2 ^ (k + 2) :=
    orderOf_dvd_of_pow_eq_one (congrArg Prod.fst (pow_large k x))
  obtain ⟨j, hj, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  by_contra hn
  have hj' : j ≤ k + 1 := by
    have hjne : j ≠ k + 2 := fun e => hn (he.trans (congrArg (fun t : ℕ => 2 ^ t) e))
    omega
  have hf : x.1 ^ (2 ^ (k + 1)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (he ▸ pow_dvd_pow 2 hj')
  have ht : x ^ (2 ^ (k + 1)) = 1 := Prod.ext hf (snd_half_pow k x)
  have hd := orderOf_dvd_of_pow_eq_one ht
  rw [hx] at hd
  have hle := Nat.le_of_dvd (by positivity) hd
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ] at hle
  have hp : 0 < 2 ^ (k + 1) := by positivity
  omega

private theorem zpowers_half (k : ℕ) (u : Large k) (hu : orderOf u = 2 ^ (k + 2)) :
    zpowers (u ^ (2 ^ (k + 1))) = (powMonoidHom 2 : Large k →* Large k).ker := by
  apply eq_of_le_of_card_ge
  · apply zpowers_le_of_mem
    change (u ^ (2 ^ (k + 1))) ^ 2 = 1
    rw [← pow_mul, ← pow_succ]
    simpa only [hu] using pow_orderOf_eq_one u
  · rw [card_involutions_fst, Nat.card_zpowers, orderOf_pow, hu]
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    have h : 2 ^ (k + 1) ∣ 2 ^ (k + 1) * 2 := dvd_mul_right _ _
    rw [Nat.gcd_eq_right h, Nat.mul_div_cancel_left _ (by positivity)]

/-- Any first-coordinate involution can be lifted to a power with trivial second coordinate. -/
private theorem lift_involution (k : ℕ) (x : Family (k + 2))
    (hx : orderOf x.1 = 2 ^ (k + 2)) (u : Large k) (hu : u ^ 2 = 1) :
    (u, 1) ∈ zpowers x := by
  have hmem : u ∈ (powMonoidHom 2 : Large k →* Large k).ker := hu
  rw [← zpowers_half k x.1 hx] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hhalf : x ^ (2 ^ (k + 1)) = (x.1 ^ (2 ^ (k + 1)), 1) :=
    Prod.ext rfl (snd_half_pow k x)
  have hp : x ^ (2 ^ (k + 1)) ∈ zpowers x :=
    (zpowers x).pow_mem (mem_zpowers x) _
  have hz' := (zpowers x).zpow_mem hp z
  rw [hhalf] at hz'
  change ((x.1 ^ (2 ^ (k + 1))) ^ z, (1 : Cyclic 2) ^ z) ∈ _ at hz'
  change (x.1 ^ (2 ^ (k + 1))) ^ z = u at hz
  rwa [hz, one_zpow] at hz'

private theorem b_not_mem (n : ℕ) : b n ∉ zpowers (a n) := by
  rintro ⟨z, hz⟩
  have h := congrArg Prod.snd hz
  have hh : (1 : Cyclic 2) = generator 2 := by simpa [a, b] using h
  exact (show (1 : Cyclic 2) ≠ generator 2 by decide) hh

private theorem aut_b_snd (k : ℕ) (e : MulAut (Family (k + 2))) :
    (e (b (k + 2))).2 = generator 2 := by
  let x := e (a (k + 2))
  let y := e (b (k + 2))
  change y.2 = generator 2
  apply cyclic_two_eq_gen
  intro hy
  have hx := order_fst_of_order k x ((e.orderOf_eq _).trans (order_a _))
  have hy2 : y.1 ^ 2 = 1 := by
    have h := pow_orderOf_eq_one y
    rw [show orderOf y = 2 from (e.orderOf_eq _).trans (order_b _)] at h
    exact congrArg Prod.fst h
  have hmem := lift_involution k x hx y.1 hy2
  have hxy : y = (y.1, 1) := Prod.ext rfl hy
  rw [← hxy] at hmem
  obtain ⟨z, hz⟩ := hmem
  apply b_not_mem (k + 2)
  refine ⟨z, e.injective ?_⟩
  rw [map_zpow]
  exact hz

private theorem surjective_of_large_images (k : ℕ) (x y : Family (k + 2))
    (hx : orderOf x.1 = 2 ^ (k + 2)) (hy : y ^ 2 = 1) (hyb : y.2 = generator 2) :
    Function.Surjective (ofImages (k + 2) x y (pow_large k x) hy) := by
  let f := ofImages (k + 2) x y (pow_large k x) hy
  let R := f.range
  have hmx : x ∈ R := ⟨a (k + 2), ofImages_a _ _ _ _ _⟩
  have hmy : y ∈ R := ⟨b (k + 2), ofImages_b _ _ _ _ _⟩
  have hlift : (y.1, 1) ∈ R :=
    zpowers_le_of_mem hmx (lift_involution k x hx y.1 (congrArg Prod.fst hy))
  have hbmem : b (k + 2) ∈ R := by
    have h := R.mul_mem (R.inv_mem hlift) hmy
    change (y.1⁻¹ * y.1, 1⁻¹ * y.2) ∈ R at h
    simpa [b, hyb] using h
  have hsecond (v : Cyclic 2) : (1, v) ∈ R := by
    obtain ⟨z, hz⟩ := generator_generates 2 v
    simpa [b, hz] using R.zpow_mem hbmem z
  have htop : zpowers x.1 = ⊤ :=
    (Subgroup.card_eq_iff_eq_top _).mp (by rw [Nat.card_zpowers, hx, cyclic_card])
  rintro ⟨u,v⟩
  have hm : u ∈ zpowers x.1 := htop.symm ▸ mem_top u
  obtain ⟨z, hz⟩ := hm
  have h := R.mul_mem (R.zpow_mem hmx z) (hsecond ((x.2 ^ z)⁻¹ * v))
  change (x.1 ^ z * 1, x.2 ^ z * ((x.2 ^ z)⁻¹ * v)) ∈ R at h
  change (u,v) ∈ R
  simpa [hz] using h

/-- Parameters for the two generator images in the higher-order cases. -/
private abbrev LargeAutParameters (k : ℕ) :=
  ({u : Large k // orderOf u = 2 ^ (k + 2)} × Cyclic 2) ×
    (powMonoidHom 2 : Large k →* Large k).ker

/-- Generator images for automorphisms of C_(2^(k+2)) × C₂. -/
private noncomputable def largeAutEquiv (k : ℕ) :
    MulAut (Family (k + 2)) ≃ LargeAutParameters k := by
  let eval (e : MulAut (Family (k + 2))) : LargeAutParameters k :=
    let x := e (a (k + 2))
    let y := e (b (k + 2))
    ((⟨x.1, order_fst_of_order k x ((e.orderOf_eq _).trans (order_a _))⟩, x.2),
      ⟨y.1, show y.1 ^ 2 = 1 by
        have hy := pow_orderOf_eq_one y
        rw [show orderOf y = 2 from (e.orderOf_eq _).trans (order_b _)] at hy
        exact congrArg Prod.fst hy⟩)
  apply Equiv.ofBijective eval
  constructor
  · intro e f h
    apply aut_ext (k + 2)
    · exact Prod.ext (congrArg (fun p => p.1.1.val) h) (congrArg (fun p => p.1.2) h)
    · exact Prod.ext (congrArg (fun p => p.2.val) h) ((aut_b_snd k e).trans (aut_b_snd k f).symm)
  · rintro ⟨⟨u,v⟩,t⟩
    let x : Family (k + 2) := (u.val, v)
    let y : Family (k + 2) := (t.val, generator 2)
    have hy : y ^ 2 = 1 := Prod.ext t.property (cyclic_two_sq _)
    let f := ofImages (k + 2) x y (pow_large k x) hy
    have hs : Function.Surjective f := surjective_of_large_images k x y u.property hy rfl
    let e := MulEquiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
    refine ⟨e, Prod.ext ?_ ?_⟩
    · change ((⟨(f (a (k + 2))).1, _⟩, (f (a (k + 2))).2) :
        {u : Large k // orderOf u = 2 ^ (k + 2)} × Cyclic 2) = (u,v)
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst (ofImages_a _ x y (pow_large k x) hy))
      · change (f (a (k + 2))).2 = v
        exact congrArg Prod.snd (ofImages_a _ x y (pow_large k x) hy)
    · exact Subtype.ext (congrArg Prod.fst (ofImages_b _ x y (pow_large k x) hy))

private theorem card_aut_large (k : ℕ) : Nat.card (MulAut (Family (k + 2))) = 2 ^ (k + 3) := by
  classical
  have hc : Nat.card {u : Large k // orderOf u = 2 ^ (k + 2)} = 2 ^ (k + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hcard : Fintype.card (Large k) = 2 ^ (k + 2) := by
      rw [← Nat.card_eq_fintype_card, cyclic_card]
    rw [IsCyclic.card_orderOf_eq_totient (hcard.symm ▸ dvd_rfl), Nat.totient_prime_pow_succ Nat.prime_two]
    simp
  rw [Nat.card_congr (largeAutEquiv k), Nat.card_prod, Nat.card_prod, hc, cyclic_card,
    card_involutions_fst]
  simp only [pow_succ]

open Filter Topology

private theorem sum_aut_family (n : ℕ) :
    (∑ j : Fin (n + 1), (Nat.card (MulAut (Family (j.val + 1))) : ℝ)) =
      4 * (2 : ℝ) ^ (n + 1) - 2 := by
  induction n with
  | zero =>
    change (∑ j : Fin 1, (Nat.card (MulAut (Family (j.val + 1))) : ℝ)) = _
    rw [Fin.sum_univ_one]
    change (Nat.card (MulAut (Family 1)) : ℝ) = _
    rw [card_aut_klein]
    norm_num
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ j : Fin (n + 1), (Nat.card (MulAut (Family (j.val + 1))) : ℝ)) +
      Nat.card (MulAut (Family (n + 2))) = _
    rw [ih, card_aut_large]
    push_cast
    ring

/-- The exact value of the invariant on C_(2^n) × C₂, for every positive exponent. -/
theorem gauss_family (n : ℕ) (hn : 1 ≤ n) :
    gauss (Family n) = 3 - (2 : ℝ) ^ (-(n : ℤ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [gauss_family_eq_sum, sum_aut_family, zpow_neg, zpow_natCast]
  have hp : (2 : ℝ) ^ (m + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- The global image as a subset of the relative real space [1, ∞). -/
def gaussImage : Set (Set.Ici (1 : ℝ)) :=
  Set.range (fun G : FiniteGroup => (⟨gauss G.Carrier, one_le_gauss⟩ : Set.Ici (1 : ℝ)))

/-- Any finite group in any universe is represented in the image. -/
private theorem gauss_mem_image (G : Type*) [Group G] [Finite G] :
    (⟨gauss G, one_le_gauss⟩ : Set.Ici (1 : ℝ)) ∈ gaussImage := by
  obtain ⟨K, groupK, finiteK, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact ⟨⟨K, groupK, inferInstance⟩, Subtype.ext (gauss_mulEquiv e).symm⟩

/-- The relative-space point with real coordinate 3. -/
private def three : Set.Ici (1 : ℝ) := ⟨3, by norm_num⟩

/-- The sequence of invariants of the positive-exponent family. -/
private noncomputable def gaussSequence (n : ℕ) : Set.Ici (1 : ℝ) :=
  ⟨gauss (Family (n + 1)), one_le_gauss⟩

private theorem gaussSequence_mem (n : ℕ) : gaussSequence n ∈ gaussImage :=
  gauss_mem_image (Family (n + 1))

private theorem gaussSequence_ne_three (n : ℕ) : gaussSequence n ≠ three := by
  intro h
  have hc : gauss (Family (n + 1)) = 3 := congrArg Subtype.val h
  rw [gauss_family _ (by omega)] at hc
  have hp : 0 < (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := zpow_pos (by norm_num) _
  linarith

private theorem tendsto_gaussSequence : Tendsto gaussSequence atTop (𝓝 three) := by
  apply tendsto_subtype_rng.mpr
  have h : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hs := h.comp (tendsto_add_atTop_nat 1)
  have ht := (tendsto_const_nhds (x := (3 : ℝ))).sub hs
  simpa only [gaussSequence, three, gauss_family _ (Nat.succ_pos _), zpow_neg, zpow_natCast,
    inv_pow, Function.comp_apply, sub_zero] using ht

/-- If 3 is in the image, its singleton is not relatively open in the image. -/
private theorem three_not_isolated (h : three ∈ gaussImage) :
    ¬ IsOpen ({⟨three, h⟩} : Set gaussImage) := by
  intro hopen
  let x : gaussImage := ⟨three, h⟩
  let s (n : ℕ) : gaussImage := ⟨gaussSequence n, gaussSequence_mem n⟩
  have ht : Tendsto s atTop (𝓝 x) := tendsto_subtype_rng.mpr tendsto_gaussSequence
  have he : ∀ᶠ n in atTop, s n ∈ ({x} : Set gaussImage) :=
    ht.eventually_mem (hopen.mem_nhds (Set.mem_singleton x))
  obtain ⟨n, hn⟩ := he.exists
  exact gaussSequence_ne_three n (congrArg Subtype.val (Set.mem_singleton_iff.mp hn))

/-- Negative answer to Remark 3.4, in the relative topology of [1, ∞). -/
theorem image_not_closed_and_discrete :
    ¬ (IsClosed gaussImage ∧ DiscreteTopology gaussImage) := by
  rintro ⟨hclosed, hdiscrete⟩
  have h : three ∈ gaussImage :=
    hclosed.mem_of_tendsto tendsto_gaussSequence (Eventually.of_forall gaussSequence_mem)
  exact three_not_isolated h ((discreteTopology_iff_isOpen_singleton.mp hdiscrete) ⟨three, h⟩)

end D5.S3.FiniteGroups.Gauss.TarnauceanuImage
