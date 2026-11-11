/- GID: D5/S3/Quantum/Algebra/SplitQuarticIrreducibility
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/SplitQuarticIrreducibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fewer-than-twenty-zero squarefree quartics are irreducible by a structural exchange-pair bound; the Fin 8 specialization only normalizes choose 6 3 = 20 and does not enumerate cuts or factor shapes. -/

module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

/-! Homogeneous support and the obstruction to a nontrivial factor variable cut. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.SplitQuarticIrreducibility

open MvPolynomial Finset
open scoped Pointwise
open scoped Classical

variable {k : Type*} [Field k]

/-- The squarefree exponent with exactly the indicated original labels. -/
def squareExponent (I : Finset (Fin 8)) : Fin 8 →₀ ℕ :=
  ∑ i ∈ I, Finsupp.single i 1

lemma square_exponent_apply (I : Finset (Fin 8)) (i : Fin 8) :
    squareExponent I i = if i ∈ I then 1 else 0 := by
  classical
  simp [squareExponent, Finsupp.single_apply]

lemma square_exponent_degree (I : Finset (Fin 8)) :
    (squareExponent I).degree = I.card := by
  classical
  simp [Finsupp.degree_eq_sum, square_exponent_apply]

private lemma coeff_product_disjoint {F G : MvPolynomial (Fin 8) k}
    (hd : Disjoint F.vars G.vars) {a b : Fin 8 →₀ ℕ}
    (ha : a ∈ F.support) (hb : b ∈ G.support) :
    (F * G).coeff (a + b) = F.coeff a * G.coeff b := by
  classical
  apply AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd
  intro u v hu hv huv
  have hzeroF (w : Fin 8 →₀ ℕ) (hw : w ∈ F.support) (i : Fin 8)
      (hi : i ∉ F.vars) : w i = 0 := mem_support_notMem_vars_zero hw hi
  have hzeroG (w : Fin 8 →₀ ℕ) (hw : w ∈ G.support) (i : Fin 8)
      (hi : i ∈ F.vars) : w i = 0 :=
    mem_support_notMem_vars_zero hw (fun hj => Finset.disjoint_left.mp hd hi hj)
  constructor <;> ext i
  · have hi := DFunLike.congr_fun huv i
    by_cases h : i ∈ F.vars
    · simpa [hzeroG v hv i h, hzeroG b hb i h] using hi
    · simp [hzeroF u hu i h, hzeroF a ha i h]
  · have hi := DFunLike.congr_fun huv i
    by_cases h : i ∈ F.vars
    · simp [hzeroG v hv i h, hzeroG b hb i h]
    · simpa [hzeroF u hu i h, hzeroF a ha i h] using hi

private lemma vars_nonempty_of_nonunit {F : MvPolynomial (Fin 8) k}
    (hF : F ≠ 0) (hu : ¬ IsUnit F) : F.vars.Nonempty := by
  classical
  by_contra hn
  have he : F = C (F.coeff 0) := vars_eq_empty_iff_eq_C.mp (Finset.not_nonempty_iff_eq_empty.mp hn)
  have hc : F.coeff 0 ≠ 0 := by
    intro h
    apply hF
    simpa [h] using he
  apply hu
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

/-- In a finite carrier, opposite labels pair every `(k - 1)`-set avoiding them
with the two `k`-sets obtained by exchanging the distinguished label. -/
private lemma card_insert_of_not_mem {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (ha : a ∉ s) : (insert a s).card = s.card + 1 := by
  have h := Finset.card_erase_add_one (s := insert a s) (a := a) (by simp)
  rw [Finset.erase_insert ha] at h
  omega

/-- The exchange map is the substantive consumed helper: it is uniform in the
finite label carrier and proves the cut bound by an injective pairing. -/
private lemma exchange_bound {α : Type*} [Fintype α] [DecidableEq α]
    (H : Finset α) (u v : α) (k d : ℕ)
    (hu : u ∈ H) (hv : v ∉ H) (huv : u ≠ v) (hk : 0 < k) :
    (((Finset.univ.erase u).erase v).powersetCard (k - 1)).card ≤
      (((Finset.univ : Finset α).powersetCard k).filter
        (fun I => (I ∩ H).card ≠ d)).card := by
  let carrier : Finset α := (Finset.univ.erase u).erase v
  let pairs : Finset (Finset α) := carrier.powersetCard (k - 1)
  let pick : Finset α → Finset α := fun T =>
    if ((insert u T) ∩ H).card ≠ d then insert u T else insert v T
  have hpick_mem (T : Finset α) (hT : T ∈ pairs) :
      pick T ∈ ((Finset.univ : Finset α).powersetCard k).filter
        (fun I => (I ∩ H).card ≠ d) := by
    have hTsub : T ⊆ carrier := (mem_powersetCard.mp hT).1
    have hTcard : T.card = k - 1 := (mem_powersetCard.mp hT).2
    have hut : u ∉ T := by
      intro h
      simpa [carrier] using hTsub h
    have hvt : v ∉ T := by
      intro h
      simpa [carrier] using hTsub h
    have hAu : (insert u T).card = k := by
      rw [card_insert_of_not_mem hut, hTcard]
      omega
    have hAv : (insert v T).card = k := by
      rw [card_insert_of_not_mem hvt, hTcard]
      omega
    have hAu_sub : insert u T ⊆ (Finset.univ : Finset α) := by simp
    have hAv_sub : insert v T ⊆ (Finset.univ : Finset α) := by simp
    have hIntU : (insert u T) ∩ H = insert u (T ∩ H) :=
      Finset.insert_inter_of_mem hu
    have hIntV : (insert v T) ∩ H = T ∩ H := by
      ext x
      simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxh⟩
        · exact (hv hxh).elim
        · exact ⟨hx, hxh⟩
      · rintro ⟨hx, hxh⟩
        exact ⟨Or.inr hx, hxh⟩
    have hcardU : ((insert u T) ∩ H).card = (T ∩ H).card + 1 := by
      rw [hIntU, card_insert_of_not_mem]
      intro hmem
      exact hut (mem_of_mem_inter_left hmem)
    have hcardV : ((insert v T) ∩ H).card = (T ∩ H).card := by rw [hIntV]
    by_cases hbad : ((insert u T) ∩ H).card ≠ d
    · rw [show pick T = insert u T by simp [pick, hbad]]
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hAu_sub, hAu⟩, hbad⟩
    · rw [show pick T = insert v T by simp [pick, hbad]]
      refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hAv_sub, hAv⟩, ?_⟩
      intro heq
      apply hbad
      have hdiff : ((insert u T) ∩ H).card = ((insert v T) ∩ H).card + 1 := by
        rw [hcardU, hcardV]
      omega
  have hpick_inj : Set.InjOn pick (pairs : Set (Finset α)) := by
    intro T hT T' hT' heq
    have hTsub : T ⊆ carrier := (mem_powersetCard.mp hT).1
    have hT'sub : T' ⊆ carrier := (mem_powersetCard.mp hT').1
    have hut : u ∉ T := by
      intro h
      simpa [carrier] using hTsub h
    have hvt : v ∉ T := by
      intro h
      simpa [carrier] using hTsub h
    have huT' : u ∉ T' := by
      intro h
      simpa [carrier] using hT'sub h
    have hvT' : v ∉ T' := by
      intro h
      simpa [carrier] using hT'sub h
    by_cases hbad : ((insert u T) ∩ H).card ≠ d
    · by_cases hbad' : ((insert u T') ∩ H).card ≠ d
      · have hEq : insert u T = insert u T' := by
          simpa only [pick, if_pos hbad, if_pos hbad'] using heq
        have hErase := congrArg (fun S => S.erase u) hEq
        simpa [Finset.erase_insert hut, Finset.erase_insert huT'] using hErase
      · have hEq : insert u T = insert v T' := by
          simpa only [pick, if_pos hbad, if_neg hbad'] using heq
        have hmem : u ∈ insert v T' := hEq ▸ (by simp)
        have hfalse : False := by simpa [huT', huv] using hmem
        exact hfalse.elim
    · by_cases hbad' : ((insert u T') ∩ H).card ≠ d
      · have hEq : insert v T = insert u T' := by
          simpa only [pick, if_neg hbad, if_pos hbad'] using heq
        have hmem : u ∈ insert v T := hEq ▸ (by simp)
        have hfalse : False := by simpa [hut, huv] using hmem
        exact hfalse.elim
      · have hEq : insert v T = insert v T' := by
          simpa only [pick, if_neg hbad, if_neg hbad'] using heq
        have hErase := congrArg (fun S => S.erase v) hEq
        simpa [Finset.erase_insert hvt, Finset.erase_insert hvT'] using hErase
  have himage : (Finset.image pick pairs).card = pairs.card := by
    exact Finset.card_image_iff.mpr hpick_inj
  apply le_trans ?_ (card_le_card (show Finset.image pick pairs ⊆ _ from by
    intro I hI
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hI
    exact hpick_mem T hT))
  rw [← himage]

/-- The original threshold is the `Fin 8`, `k = 4` specialization of
`exchange_bound`; its only arithmetic step is `Nat.choose 6 3 = 20`. -/
private lemma cut_count :
    ∀ H : Finset (Fin 8), H.Nonempty → H ≠ univ → ∀ d : Fin 5,
      20 ≤ (((univ : Finset (Fin 8)).powersetCard 4).filter
        (fun I => (I ∩ H).card ≠ d.val)).card := by
  intro H hH hHne d
  obtain ⟨u, hu⟩ := hH
  have hUnivNot : ¬ (univ : Finset (Fin 8)) ⊆ H := by
    intro hs
    apply hHne
    exact Finset.Subset.antisymm (by simp) hs
  obtain ⟨v, _, hv⟩ := Finset.not_subset.mp hUnivNot
  have huv : u ≠ v := by
    intro h
    subst v
    exact hv hu
  have hb := exchange_bound H u v 4 d.val hu hv huv (by norm_num)
  have hcard : (((univ : Finset (Fin 8)).erase u).erase v).card = 6 := by
    have hu_univ : u ∈ (univ : Finset (Fin 8)) := by simp
    have hv_erase : v ∈ (univ : Finset (Fin 8)).erase u := by simp [Ne.symm huv]
    calc
      (((univ : Finset (Fin 8)).erase u).erase v).card =
          ((univ : Finset (Fin 8)).erase u).card - 1 :=
        Finset.card_erase_of_mem hv_erase
      _ = (univ : Finset (Fin 8)).card - 1 - 1 := by
        rw [Finset.card_erase_of_mem hu_univ]
      _ = 6 := by norm_num
  have hpairs : ((((univ : Finset (Fin 8)).erase u).erase v).powersetCard (4 - 1)).card = 20 := by
    rw [card_powersetCard, hcard]
    norm_num [Nat.choose]
  rw [show 4 - 1 = 3 by norm_num, hpairs] at hb
  exact hb


/-- A homogeneous multiaffine quartic in eight variables with fewer than twenty
zero squarefree quartic coefficients is irreducible over its coefficient field. -/
theorem irreducible_of_fewer_than_twenty_zeros
    (f : MvPolynomial (Fin 8) k)
    (hh : f.IsHomogeneous 4) (hm : ∀ i, f.degreeOf i ≤ 1)
    (hz : (((univ : Finset (Fin 8)).powersetCard 4).filter
      (fun I => f.coeff (squareExponent I) = 0)).card < 20) : Irreducible f := by
  classical
  have hf : f ≠ 0 := by
    intro h
    subst f
    norm_num [Finset.card_powersetCard, Nat.choose] at hz
  have hfu : ¬ IsUnit f := by
    intro hu
    have hd := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    have he := hh.totalDegree hf
    omega
  refine ⟨hfu, ?_⟩
  intro F G hFG
  by_contra hn
  obtain ⟨hFu, hGu⟩ := not_or.mp hn
  have hF : F ≠ 0 := left_ne_zero_of_mul (hFG ▸ hf)
  have hG : G ≠ 0 := right_ne_zero_of_mul (hFG ▸ hf)
  have hdis : Disjoint F.vars G.vars := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hFi := mem_vars_iff_degreeOf_ne_zero.mp hi
    have hGi := mem_vars_iff_degreeOf_ne_zero.mp hj
    have hd := hm i
    rw [hFG, degreeOf_mul_eq hF hG] at hd
    omega
  let H := F.vars
  have hH : H.Nonempty := vars_nonempty_of_nonunit hF hFu
  have hHne : H ≠ univ := by
    obtain ⟨j, hj⟩ := vars_nonempty_of_nonunit hG hGu
    intro h
    exact Finset.disjoint_left.mp hdis (by simpa [H, ← h] using mem_univ j) hj
  obtain ⟨a₀, ha₀⟩ := exists_coeff_ne_zero hF
  obtain ⟨b₀, hb₀⟩ := exists_coeff_ne_zero hG
  have hp (a b : Fin 8 →₀ ℕ) (ha : a ∈ F.support) (hb : b ∈ G.support) :
      a.degree + b.degree = 4 := by
    have hc : f.coeff (a + b) ≠ 0 := by
      rw [hFG, coeff_product_disjoint hdis ha hb]
      exact mul_ne_zero (mem_support_iff.mp ha) (mem_support_iff.mp hb)
    have he : (a + b).degree = 4 := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hh hc
    simpa only [map_add] using he
  have ha0mem : a₀ ∈ F.support := mem_support_iff.mpr ha₀
  have hb0mem : b₀ ∈ G.support := mem_support_iff.mpr hb₀
  have hd0 := hp a₀ b₀ ha0mem hb0mem
  let d : Fin 5 := ⟨a₀.degree, by omega⟩
  have hcut (I : Finset (Fin 8)) (hc : f.coeff (squareExponent I) ≠ 0) :
      (I ∩ H).card = d.val := by
    have hmem : squareExponent I ∈ (F * G).support := by
      rw [← hFG]
      exact mem_support_iff.mpr hc
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (support_mul F G hmem)
    have hadeg : a.degree = a₀.degree := by
      have h1 := hp a b₀ ha hb0mem
      omega
    have hrestrict : ∑ i ∈ H, (squareExponent I) i = a.degree := by
      rw [Finsupp.degree_eq_sum]
      calc
        ∑ i ∈ H, (squareExponent I) i = ∑ i ∈ H, a i := by
          apply sum_congr rfl
          intro i hi
          have hbzero : b i = 0 := mem_support_notMem_vars_zero hb
            (fun hj => Finset.disjoint_left.mp hdis hi hj)
          simpa [← hab, hbzero]
        _ = ∑ i : Fin 8, a i := by
          apply sum_subset (subset_univ H)
          intro i _ hi
          exact mem_support_notMem_vars_zero ha hi
    have hcard : (∑ i ∈ H, (squareExponent I) i) = (I ∩ H).card := by
      simp [square_exponent_apply, Finset.inter_comm]
    exact hcard.symm.trans (hrestrict.trans hadeg)
  have hsub : (((univ : Finset (Fin 8)).powersetCard 4).filter
      (fun I => (I ∩ H).card ≠ d.val)) ⊆
      (((univ : Finset (Fin 8)).powersetCard 4).filter
        (fun I => f.coeff (squareExponent I) = 0)) := by
    intro I hi
    obtain ⟨hi, hc⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨hi, ?_⟩
    by_contra hzI
    exact hc (hcut I hzI)
  exact (not_le_of_gt hz) ((cut_count H hH hHne d).trans (card_le_card hsub))

end D5.S3.Quantum.Algebra.SplitQuarticIrreducibility
