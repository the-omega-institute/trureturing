/- GID: D5/S3/FiniteGroups/SimpleOrderSixty
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SimpleOrderSixty
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite nonabelian simple group of order sixty is multiplicatively equivalent to the alternating group on five letters. -/

/-
Selected source from Moonshine-in-Kansas/atlas, revision
1bc46341457aab119f667c43b6ce7216cbb899b6, Apache-2.0.
Original declaration names and proof bodies are retained. Changes: concatenate
the six-module recognition closure, route imports to Mathlib, and omit the
unused simple-quotient lemma. No declaration identifier is changed.
Full source attribution and license: docs/reports/licenses/atlas-simple-order-sixty.md.
Source locators and own-pin retirement condition: Library/FiniteGroups/atlas2026simpleordersixty.md.
-/

import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Alternating


noncomputable section
namespace Atlas.GroupTheory
variable {G ι : Type*} [Group G]

theorem subgroup_nonidentity_sigma_injective (H : ι → Subgroup G)
    (hH : Pairwise (fun i j => Disjoint (H i) (H j))) :
    Function.Injective (fun x : (Σi,{g : H i // g≠1}) => x.2.val.val) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ hxy
  change x.val.val=y.val.val at hxy
  have hij : i=j := by
    by_contra hn
    have hx : x.val.val=1 := (Subgroup.disjoint_def.mp (hH hn))
      x.val.prop (by rw [hxy]; exact y.val.prop)
    exact x.prop (Subtype.ext hx)
  subst j
  congr 1
  exact Subtype.ext (Subtype.ext hxy)

theorem card_subgroup_nonidentity [Finite G] (H : Subgroup G) :
    Nat.card {x : H // x≠1}=Nat.card H-1 := by
  classical
  letI := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp [Nat.card_eq_fintype_card]

theorem disjoint_subgroup_nonidentity_card_bound [Finite G] [Fintype ι]
    (H : ι → Subgroup G) (hH : Pairwise (fun i j => Disjoint (H i) (H j))) :
    (∑i,(Nat.card (H i)-1)) ≤ Nat.card G := by
  classical
  have hi := Nat.card_le_card_of_injective _ (subgroup_nonidentity_sigma_injective H hH)
  have hc : Nat.card (Σi,{g : H i // g≠1})=∑i,(Nat.card (H i)-1) := by
    letI (i : ι) := Fintype.ofFinite {g : H i // g≠1}
    rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [←Nat.card_eq_fintype_card,card_subgroup_nonidentity]
  rwa [hc] at hi

end Atlas.GroupTheory

namespace Atlas.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem subgroups_prime_card_disjoint {p : ℕ} (hp : p.Prime)
    (H K : Subgroup G) (hH : Nat.card H=p) (hK : Nat.card K=p) (hne : H≠K) : Disjoint H K := by
  apply Subgroup.disjoint_def.mpr
  intro x hxH hxK
  by_contra hx
  have hd : orderOf x∣p := by
    rw [←hH,Subgroup.orderOf_coe (⟨x,hxH⟩ : H)]
    exact orderOf_dvd_natCard _
  have ho : orderOf x=p := by
    rcases (Nat.dvd_prime hp).mp hd with he|he
    · exact (hx (orderOf_eq_one_iff.mp he)).elim
    · exact he
  have hZ : Nat.card (Subgroup.zpowers x)=p := by rw [Nat.card_zpowers,ho]
  have hZH : Subgroup.zpowers x=H := Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hxH) (by rw [hZ,hH])
  have hZK : Subgroup.zpowers x=K := Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hxK) (by rw [hZ,hK])
  exact hne (hZH.symm.trans hZK)

end Atlas.GroupTheory


namespace Atlas.GroupTheory

/-- A proper subgroup of a finite simple group has index large enough for the
faithful coset action. No classification of subgroups is used. -/
theorem subgroup_eq_top_of_index_factorial_lt {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (H : Subgroup G) (hcard : H.index.factorial < Nat.card G) : H=⊤ := by
  classical
  let f := MulAction.toPermHom G (G ⧸ H)
  have hk : f.ker=⊤ := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · have hi := (MonoidHom.ker_eq_bot_iff f).mp h
      have hc := Nat.card_le_card_of_injective f hi
      have he : Nat.card (Equiv.Perm (G ⧸ H)) = H.index.factorial := by
        letI := Fintype.ofFinite (G ⧸ H)
        rw [Nat.card_eq_fintype_card,Fintype.card_perm]
        rw [Subgroup.index_eq_card,Nat.card_eq_fintype_card]
      rw [he] at hc
      omega
    · exact h
  letI : Subsingleton (G ⧸ H) := ⟨by
    intro x y
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
    have hm : g ∈ f.ker := by rw [hk]; trivial
    have he : f g = 1 := hm
    have hx : g • x=x := congrArg (fun p : Equiv.Perm (G ⧸ H) => p x) he
    exact hx.symm.trans hg⟩
  apply (Subgroup.index_eq_one).mp
  rw [Subgroup.index_eq_card]
  exact Nat.card_unique

end Atlas.GroupTheory


namespace Atlas.GroupTheory

/-- A nonabelian simple group has trivial center. -/
theorem center_eq_bot_of_simple_nonabelian (G : Type*) [Group G] [IsSimpleGroup G]
    (hn : ¬IsMulCommutative G) : Subgroup.center G=⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h|h
  · exact h
  · exact (hn (Subgroup.center_eq_top_iff.mp h)).elim

end Atlas.GroupTheory


noncomputable section
namespace Atlas.GroupTheory
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
local instance simpleOrderSixtySylowPrime1 : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance simpleOrderSixtySylowPrime2 : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem simple_sixty_proper_index_ge_five (hG : Nat.card G=60) (H : Subgroup G) (hH : H≠⊤) :
    5≤H.index := by
  by_contra hn
  have hh : H.index.factorial < Nat.card G := by
    have hm := Nat.factorial_le (show H.index≤4 by omega)
    rw [hG]
    exact lt_of_le_of_lt hm (by decide)
  exact hH (subgroup_eq_top_of_index_factorial_lt H hh)

theorem sylow_two_card_of_sixty (hG : Nat.card G=60) (P : Sylow 2 G) : Nat.card P=4 := by
  rw [Sylow.card_eq_multiplicity,hG]
  rw [show 60 = 2^2*15 from rfl,
    Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime (2^2) 15),
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣15)]
  norm_num

theorem sylow_five_card_of_sixty (hG : Nat.card G=60) (P : Sylow 5 G) : Nat.card P=5 := by
  rw [Sylow.card_eq_multiplicity,hG]
  rw [show 60 = 5*12 from rfl,
    Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime 5 12),
    (by decide : Nat.Prime 5).factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬5∣12)]
  norm_num

private theorem normalizer_ne_top_of_card {p : ℕ} (hG : Nat.card G=60) (P : Sylow p G)
    (hP : 1<Nat.card P) (hP' : Nat.card P<60) : Subgroup.normalizer (P : Set G)≠⊤ := by
  intro hn
  haveI : P.toSubgroup.Normal := Subgroup.normalizer_eq_top_iff.mp hn
  rcases (inferInstance : P.toSubgroup.Normal).eq_bot_or_eq_top with hp|hp
  · have h := congrArg (fun H : Subgroup G => Nat.card H) hp
    simp only [Subgroup.card_bot] at h
    omega
  · have h := congrArg (fun H : Subgroup G => Nat.card H) hp
    simp only [Subgroup.card_top,hG] at h
    omega

theorem sylow_two_count_of_simple_sixty (hG : Nat.card G=60) :
    Nat.card (Sylow 2 G)=5 ∨ Nat.card (Sylow 2 G)=15 := by
  let P : Sylow 2 G := Classical.choice inferInstance
  have hp := sylow_two_card_of_sixty hG P
  have hi : P.toSubgroup.index=15 := by
    have hh := P.toSubgroup.card_mul_index
    rw [hp,hG] at hh
    omega
  have hd := P.card_dvd_index
  rw [hi] at hd
  have hl : 5≤Nat.card (Sylow 2 G) := by
    rw [Sylow.card_eq_index_normalizer P]
    exact simple_sixty_proper_index_ge_five hG _ (normalizer_ne_top_of_card hG P (by omega) (by omega))
  have hu := Nat.le_of_dvd (by decide : 0<15) hd
  interval_cases hc : Nat.card (Sylow 2 G) <;> omega

theorem sylow_five_count_of_simple_sixty (hG : Nat.card G=60) : Nat.card (Sylow 5 G)=6 := by
  let P : Sylow 5 G := Classical.choice inferInstance
  have hp := sylow_five_card_of_sixty hG P
  have hi : P.toSubgroup.index=12 := by
    have hh := P.toSubgroup.card_mul_index
    rw [hp,hG] at hh
    omega
  have hd := P.card_dvd_index
  rw [hi] at hd
  have hl : 5≤Nat.card (Sylow 5 G) := by
    rw [Sylow.card_eq_index_normalizer P]
    exact simple_sixty_proper_index_ge_five hG _ (normalizer_ne_top_of_card hG P (by omega) (by omega))
  have hu := Nat.le_of_dvd (by decide : 0<12) hd
  have hm : Nat.card (Sylow 5 G)%5=1 := card_sylow_modEq_one 5 G
  interval_cases hc : Nat.card (Sylow 5 G) <;> omega

end Atlas.GroupTheory

namespace Atlas.GroupTheory
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
local instance simpleOrderSixtySylowPrime3 : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem simple_sixty_index_five_of_sylow_intersection (hG : Nat.card G=60)
    (hn : ¬IsMulCommutative G) (P Q : Sylow 2 G) (hPQ : P≠Q)
    (t : G) (ht : t≠1) (htP : t∈P) (htQ : t∈Q) :
    ∃H : Subgroup G,H.index=5 := by
  let C := Subgroup.centralizer ({t} : Set G)
  have hin (R : Sylow 2 G) (htR : t∈R) : R.toSubgroup≤C := by
    letI := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
      (show Nat.card R=2^2 from sylow_two_card_of_sixty hG R)
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    have hy' : y=t := Set.mem_singleton_iff.mp hy
    subst y
    exact congrArg Subtype.val ((inferInstance : IsMulCommutative R).is_comm.comm (⟨t,htR⟩ : R) ⟨x,hx⟩)
  have hp := hin P htP
  have hq := hin Q htQ
  have hproper : C≠⊤ := by
    intro hc
    have hz : t∈Subgroup.center G :=
      (Subgroup.centralizer_eq_top_iff_subset.mp hc) (Set.mem_singleton t)
    rw [center_eq_bot_of_simple_nonabelian G hn] at hz
    exact ht hz
  have hd : 4∣Nat.card C := by
    simpa [sylow_two_card_of_sixty hG P] using Subgroup.card_dvd_of_le hp
  have hc4 : 4<Nat.card C := by
    have hh := Nat.le_of_dvd (Nat.card_pos (α := C)) hd
    by_contra hlt
    have he : Nat.card C=4 := by omega
    have hPC : P.toSubgroup=C := Subgroup.eq_of_le_of_card_ge hp (by rw [he,sylow_two_card_of_sixty hG P])
    have hQC : Q.toSubgroup=C := Subgroup.eq_of_le_of_card_ge hq (by rw [he,sylow_two_card_of_sixty hG Q])
    exact hPQ (Sylow.ext (hPC.trans hQC.symm))
  have hindex := simple_sixty_proper_index_ge_five hG C hproper
  have hprod := C.card_mul_index
  rw [hG] at hprod
  have hupper : Nat.card C≤12 := by nlinarith
  have hdiv := C.card_subgroup_dvd_card
  rw [hG] at hdiv
  have hcard : Nat.card C=12 := by
    interval_cases hc : Nat.card C <;> omega
  refine ⟨C,?_⟩
  rw [hcard] at hprod
  omega

end Atlas.GroupTheory

namespace Atlas.GroupTheory
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
local instance simpleOrderSixtySylowPrime4 : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance simpleOrderSixtySylowPrime5 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- An elementary Sylow-counting construction of a subgroup of index five. -/
theorem subgroup_index_five_of_simple_card_sixty (hG : Nat.card G=60) (hn : ¬IsMulCommutative G) :
    ∃H : Subgroup G,H.index=5 := by
  classical
  rcases sylow_two_count_of_simple_sixty hG with hc|hc
  · let P : Sylow 2 G := Classical.choice inferInstance
    exact ⟨Subgroup.normalizer (P : Set G),(Sylow.card_eq_index_normalizer P).symm.trans hc⟩
  · by_cases hd : Pairwise (fun P Q : Sylow 2 G => Disjoint P.toSubgroup Q.toSubgroup)
    · letI := Fintype.ofFinite (Sylow 2 G)
      letI := Fintype.ofFinite (Sylow 5 G)
      let H : Sylow 2 G ⊕ Sylow 5 G → Subgroup G := Sum.elim (fun P => P.toSubgroup) (fun P => P.toSubgroup)
      have hH : Pairwise (fun i j => Disjoint (H i) (H j)) := by
        intro i j hij
        cases i with
        | inl P =>
          cases j with
          | inl Q => exact hd (fun h => hij (congrArg Sum.inl h))
          | inr Q => exact IsPGroup.disjoint_of_ne 2 5 (by decide) P.toSubgroup Q.toSubgroup P.isPGroup' Q.isPGroup'
        | inr P =>
          cases j with
          | inl Q => exact (IsPGroup.disjoint_of_ne 2 5 (by decide) Q.toSubgroup P.toSubgroup Q.isPGroup' P.isPGroup').symm
          | inr Q =>
            exact subgroups_prime_card_disjoint (G := G) (by decide : Nat.Prime 5)
              P.toSubgroup Q.toSubgroup (sylow_five_card_of_sixty hG P) (sylow_five_card_of_sixty hG Q)
              (fun h => hij (congrArg Sum.inr (Sylow.ext h)))
      have hb := disjoint_subgroup_nonidentity_card_bound H hH
      have h5 := sylow_five_count_of_simple_sixty hG
      simp [H,Fintype.sum_sum_type,sylow_two_card_of_sixty hG,sylow_five_card_of_sixty hG,
        ←Nat.card_eq_fintype_card,hc,h5,hG] at hb
    · simp only [Pairwise] at hd
      push_neg at hd
      obtain ⟨P,Q,hPQ,hd⟩ := hd
      rw [Subgroup.disjoint_def] at hd
      push_neg at hd
      obtain ⟨t,htP,htQ,ht⟩ := hd
      exact simple_sixty_index_five_of_sylow_intersection hG hn P Q hPQ t ht htP htQ

end Atlas.GroupTheory


noncomputable section
namespace Atlas.GroupTheory
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- A nontrivial coset action of a simple group is faithful. -/
theorem simple_coset_action_injective (H : Subgroup G) (hi : H.index≠1) :
    Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
  let f := MulAction.toPermHom G (G ⧸ H)
  apply (MonoidHom.ker_eq_bot_iff f).mp
  rcases f.normal_ker.eq_bot_or_eq_top with hk|hk
  · exact hk
  · letI : Subsingleton (G ⧸ H) := ⟨by
      intro x y
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
      have hm : g∈f.ker := by rw [hk]; trivial
      have he : f g=1 := hm
      have hx : g • x=x := congrArg (fun p : Equiv.Perm (G ⧸ H) => p x) he
      exact hx.symm.trans hg⟩
    have hc : Nat.card (G ⧸ H)=1 := Nat.card_unique
    exact (hi ((Subgroup.index_eq_card H).trans hc)).elim

/-- The actual coset permutation representation, marked by five coordinates, yields A5. -/
def simpleOrderSixtyEquivAlt5OfIndexFive (hG : Nat.card G=60) (H : Subgroup G) (hH : H.index=5) :
    G ≃* alternatingGroup (Fin 5) := by
  classical
  letI := Fintype.ofFinite (G ⧸ H)
  let e : (G ⧸ H) ≃ Fin 5 := Fintype.equivFinOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Subgroup.index_eq_card,hH])
  let p : G →* Equiv.Perm (Fin 5) := e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))
  have hp : Function.Injective p := e.permCongrHom.injective.comp
    (simple_coset_action_injective H (by omega))
  let s := Equiv.Perm.sign.comp p
  have hs : s.ker=⊤ := by
    rcases s.normal_ker.eq_bot_or_eq_top with hh|hh
    · have hi := (MonoidHom.ker_eq_bot_iff s).mp hh
      have hc := Nat.card_le_card_of_injective s hi
      have hu : Nat.card ℤˣ=2 := by simp [Nat.card_eq_fintype_card]
      rw [hG,hu] at hc
      omega
    · exact hh
  let f : G →* alternatingGroup (Fin 5) := p.codRestrict _ (fun g => by
    change s g=1
    exact MonoidHom.mem_ker.mp (hs ▸ Subgroup.mem_top g))
  have hf : Function.Injective f := fun a b he => hp (congrArg Subtype.val he)
  have hc : Nat.card G=Nat.card (alternatingGroup (Fin 5)) := by
    rw [hG,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hc⟩)

end Atlas.GroupTheory


/-! # Elementary recognition of a nonabelian simple group of order sixty

The comparison is the coset action of the subgroup of index five constructed
by Sylow counting and a centralizer argument. No classification is used.
-/
noncomputable section
namespace Atlas.GroupTheory

/-- The actual index-five coset action realizes every nonabelian simple group of order sixty as A5. -/
def smallSimpleOrder60EquivAlt5 (G : Type*) [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : Nat.card G = 60) (hnoncomm : ¬IsMulCommutative G) :
    G ≃* alternatingGroup (Fin 5) :=
  simpleOrderSixtyEquivAlt5OfIndexFive hcard
    (Classical.choose (subgroup_index_five_of_simple_card_sixty hcard hnoncomm))
    (Classical.choose_spec (subgroup_index_five_of_simple_card_sixty hcard hnoncomm))

end Atlas.GroupTheory
