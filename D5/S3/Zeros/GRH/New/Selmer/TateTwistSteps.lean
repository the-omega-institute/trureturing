/- GID: D5/S3/Zeros/GRH/New/Selmer/TateTwistSteps
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/TateTwistSteps
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.TateTwistSteps. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/TateTwistSteps.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.CrystallineRank
import D5.S3.Zeros.GRH.New.Selmer.RibetFirstOrder
import D5.S3.Zeros.GRH.New.Selmer.TiltingLemma
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Ribet's method with congruent blocks and tied auxiliary primes (see
New.Selmer.RibetElement).

This file: Cocycles in a Tate twist cost only local loss and odd classes. -/


open LinearMap Module Finset
variable {ℓ} [ThePrime ℓ] {E J : Type} [Field E] [UnramCMField E] {O : CoeffRing ℓ}
attribute [local simp] tateTwist cycInv sub_smul funext_iff idOrConjInv eq_neg_iff_add_eq_zero

/-- Let e ≠ 0 and c be a continuous cocycle in O(−e)/ℓ^ν, unramified off ℓ, S, S̄ and zero on
`shaLocalSet`. Then g ↦ c(g) + c(g^c) lies in `evenClasses`. -/
lemma add_conjGal_mem_evenClasses {e S ν c} (he : e ≠ 0) (h :
  c ∈ selmerModule (tateTwist ℓ E O e) (placesDividing E ℓ ∪ .conjClosure S) ∅ _ ⊓ .pi
  (shaLocalSet ℓ E e) ⊥) : c + c ∘ conjGal ∈ evenClasses O S ν e := by
  simp_all [evenClasses, mem_selmerModule_iff, add_add_add_comm _ (_ • _), shaLocalSet, obeying]
  exact h.elim fun localCocycle h ↦
    have u := localCocycle.2.1
    have l := localCocycle.2.2
    ⟨⟨fun _ ⟨_, _, _, b, c⟩ ↦ u _ ⟨_, by aesop, _, b.conjPlace_star,
    c.conjPlace_conjGal⟩, l.add (l.comp_continuous (by fun_prop))⟩, by simp [add_comm], by
    intros; simp [*, h _ ‹_›, h _ _ _ (decompGroup.map cmConj_conjGal_smul ‹_›), ↓val_comap_lt_one]⟩

/-- Assume `IsPrimeTriangle`. Let Z be a module of cocycles of O(−e)/ℓ^ν unramified off ℓ, the
w_j, w̄_j, whose coboundaries are killed by cyc(γ)^{−e} − 1. If b bounds its local loss at ℓ
plus length `shaOdd`, `HasTriangleCost` holds with ℓ^h, b. -/
lemma hasTriangleCost_tateTwist [Fintype J] [LinearOrder J] {ν w τ φ t γ h c} {e : Fin t} {ty : J →o
  _} (tri : IsPrimeTriangle ν w τ φ γ t ty h c) {Z : Submodule O _} (N : Z ≤ selmerModule (tateTwist
  ℓ E O e) (placesDividing E ℓ ∪ .conjClosure (.range w)) ∅ (QuotSpan (ℓ ^ ν : ↑O))) (H : ∀ c ∈ Z,
  ∀ m, (∀ g, c g = (cycInv ℓ E O g ^ e.1 - 1) • m) → ∀ g, (cycInv ℓ E O γ ^ e.1 - 1) • c g = 0) {b}
  (hb : relLength Z (obeying (crysRels (tateTwist ℓ E O e)) _) + length O (shaOdd ℓ E O e ν) ≤ b) :
  HasTriangleCost Z (withConjInv τ) (withConjInv φ) {j | (ty j).1 = e}
  (ℓ ^ h) b := have C {z} k := (mem_selmerModule_iff.1 (@N z k)).1
  have F j := by simpa using
    (tri.isNewPlaces.cycInv_withConjInv O (j, false)).imp_right (smul_quot_eq_zero_of_dvd <| · e)
  ⟨shaLocalSet ℓ E e, fun j hj z k ↦ by
    cases (mem_filter.1 hj).2
    simpa [F, cocycle_apply_inv (C k.1), ← Nat.cast_smul_eq_nsmul O] using
      tri.step O j _ (add_conjGal_mem_evenClasses (ty j).2.ne' ⟨N k.1, k.2⟩), fun S hS a ↦
  have K {z} k := tri.isNewPlaces.mem_selmerModule_of_tame_eq_zero (N (hS k).1) (a z k).1 .rfl
  hb.trans' (add_le_add (relLength_le_of_inj 1 (by simp) fun _ k l g ⟨_, h, a⟩ ↦ by
    let ⟨v, p⟩ := exists_isPlaceOver_of_val_ne_one E NeZero.out h.ne
    let ⟨x, n⟩ := p.exists_smul Gal(Ω/E) v.isPlaceOver_placeOver
    split_ifs at a with i <;> have d := n ▸ conj_mem_decompGroup_smul a.1 <;> simpa [← mul_assoc,
      C k g, a, i, by simpa using mem_obeying.1 l _ ⟨_, ⟨⟨v, p.valuation_natCast_lt_one_iff.1 h⟩,
      rfl⟩, .single ⟨_, d⟩ 1, fun z y ↦ by simp [crysCocycles.apply_eq_zero_of_cyclotomicGp (𝒥 :=
      _) (tateTwist_smul e) y (s := ⟨_, d⟩) (ext (by simp [*])) fun c ↦
      (localChart ..).isWeilPair_zero_iff.2 (n ▸ IsFrob.conj (by tauto) x :)], rfl⟩] using
      C k x⁻¹ (x * g * x⁻¹)) ((relLength_bot _).le.trans' (if n :
    e.1 = 0 then relLength_mono (fun z k ↦ ⟨⟨(hS k).2, by simp [n]⟩,
    K k⟩) bot_le else have A {z} k :=
      add_conjGal_mem_evenClasses (S := ∅) n ⟨selmerModule_mono (@K z k) .rfl, (hS k).2⟩
    (tri.coboundary O ⟨e, by omega⟩).elim fun D L ↦ D.elim fun q t ↦
      relLength_le_of_inj (funLeft _ _ conjGal - 1) (fun z k ↦ ⟨⟨sub_mem ((add_mem_cancel_left
      (hS k).2).1 (by simpa [shaLocalSet, n] using (A k).2.2)) (hS k).2, by simp⟩,
      sub_mem ((add_mem_cancel_left (K k)).1 (selmerModule_mono (A k).1 .rfl)) (K k)⟩) fun
    z k v ↦ funext fun g ↦ by linear_combination (norm := (simp [-funext_iff]; module)) q • H _ (hS
      (S.smul_mem _ (by simp [add_mem, k]))).1 _ ((sub_eq_zero.1 v : _ ∘ _ = z) ▸ L _ (A k) (by
      simpa [cocycle_apply_inv (C (hS k).1), F, Subtype.ext_iff] using (a z k).2)) g + t • z g)))⟩
