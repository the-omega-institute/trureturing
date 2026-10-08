/- GID: D5/S3/Combinatorics/AdditiveCodes/AdditiveCodesWeighting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/AdditiveCodes/AdditiveCodesWeighting
   mirror-E: none(waiver:incidence-weighting)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Projectivization.Action]
   utility: none
   digest: Incidence-weighted linear encoders have two exact Hamming distances. -/

import Mathlib.LinearAlgebra.Projectivization.Action
import D5.S3.Combinatorics.AdditiveCodes.AdditiveExtensionDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.AdditiveCodes

open Module Submodule AdditiveExtensionDefs

variable {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] [Fintype V]

open Classical in
/-- A blocking set and a fibre-avoiding label give an extendable additively maximal code. -/
theorem incidenceConstruction (m k r : ℕ) (hm : 0 < m) (hr : 1 ≤ r)
    (hkdim : finrank F V = k * m) (hrdim : r + m = k * m)
    (B : Finset (Projectivization F V)) (hB : 1 < B.card)
    (block : ∀ K : Submodule F V, finrank F K = r →
      ∃ P ∈ B, P.submodule ≤ K)
    (label : V → Fin m → F)
    (hlabel : ∀ x y (hxy : x ≠ y), label x = label y →
      Projectivization.mk F (x-y) (sub_ne_zero.mpr hxy) ∉ B) :
    ∃ n d : ℕ, ∃ C : Finset (Fin n → Fin m → F),
      ExtendableAdditivelyMaximal C k d := by
  classical
  have hdim : finrank F V = r + m := hkdim.trans hrdim.symm
  have hkm := hrdim
  have subspaceExtensionAvoiding (P : Submodule F V) (v : V) (hv : v ∉ P)
      (r : ℕ) (hPr : finrank F P ≤ r) (hr : r < finrank F V) :
      ∃ K : Submodule F V, P ≤ K ∧ finrank F K = r ∧ v ∉ K := by
    classical
    have aux : ∀ j : ℕ, ∀ Q : Submodule F V, v ∉ Q → finrank F Q + j = r →
        ∃ K : Submodule F V, Q ≤ K ∧ finrank F K = r ∧ v ∉ K := by
      intro j
      induction j with
      | zero =>
          intro Q hvQ hQ
          exact ⟨Q, le_rfl, by simpa using hQ, hvQ⟩
      | succ j ih =>
          intro Q hvQ hQ
          have hs : finrank F (Q ⊔ F ∙ v : Submodule F V) = finrank F Q + 1 :=
            finrank_sup_span_singleton hvQ
          have hslt : finrank F (Q ⊔ F ∙ v : Submodule F V) < finrank F V := by omega
          obtain ⟨w, hw⟩ := (Q ⊔ F ∙ v).exists_of_finrank_lt hslt
          have hwS : w ∉ Q ⊔ F ∙ v := by simpa using hw 1 one_ne_zero
          have hwQ : w ∉ Q := fun h => hwS ((show Q ≤ Q ⊔ F ∙ v from le_sup_left) h)
          let Q' := Q ⊔ F ∙ w
          have hvQ' : v ∉ Q' := by
            intro h
            rcases mem_sup.mp h with ⟨a, ha, b, hb, hab⟩
            rcases mem_span_singleton.mp hb with ⟨c, hc⟩
            have hc0 : c ≠ 0 := by
              intro h0
              apply hvQ
              have hb0 : b = 0 := by simpa [h0] using hc.symm
              have hav : a = v := by simpa [hb0] using hab
              exact hav ▸ ha
            apply hwS
            have he : w = c⁻¹ • (v - a) := by
              rw [← hab, ← hc]
              simp [smul_smul, hc0]
            rw [he]
            apply smul_mem
            exact sub_mem
              ((show F ∙ v ≤ Q ⊔ F ∙ v from le_sup_right) (mem_span_singleton_self v))
              ((show Q ≤ Q ⊔ F ∙ v from le_sup_left) ha)
          have hQ' : finrank F Q' + j = r := by
            dsimp [Q']
            rw [finrank_sup_span_singleton hwQ]
            omega
          obtain ⟨K, hQK, hKr, hvK⟩ := ih Q' hvQ' hQ'
          exact ⟨K, le_trans le_sup_left hQK, hKr, hvK⟩
    exact aux (r - finrank F P) P hv (by omega)
  have incidenceCounts (r : ℕ) (hr : 1 ≤ r) (hrV : r < finrank F V)
      (P₀ Q₀ : Projectivization F V) (hPQ : P₀ ≠ Q₀) :
      ∃ R L : ℕ, L < R ∧
        (∀ P : Projectivization F V,
          Nat.card {K : Submodule F V // finrank F K = r ∧ P.submodule ≤ K} = R) ∧
        (∀ P Q : Projectivization F V, P ≠ Q →
          Nat.card {K : Submodule F V //
            finrank F K = r ∧ P.submodule ≤ K ∧ Q.submodule ≤ K} = L) := by
    classical
    letI : Finite (Submodule F V) :=
      Finite.of_injective (fun K : Submodule F V => (K : Set V)) SetLike.coe_injective
    have hmap (e : V ≃ₗ[F] V) (P : Projectivization F V) :
        (e • P).submodule = P.submodule.map e.toLinearMap := by
      induction P using Projectivization.ind with
      | h v hv =>
        simp only [Projectivization.smul_mk, LinearEquiv.smul_def,
          Projectivization.submodule_mk, map_span, Set.image_singleton]
        rfl
    have hp (e : V ≃ₗ[F] V) (P : Projectivization F V) (K : Submodule F V) :
        (e • P).submodule ≤ K.map e.toLinearMap ↔ P.submodule ≤ K := by
      rw [hmap]
      exact (Submodule.orderIsoMapComap e).le_iff_le
    have transport (e : V ≃ₗ[F] V) (P : Projectivization F V) :
        Nat.card {K : Submodule F V // finrank F K = r ∧ P.submodule ≤ K} =
          Nat.card {K : Submodule F V //
            finrank F K = r ∧ (e • P).submodule ≤ K} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv fun K => by
        change (finrank F K = r ∧ P.submodule ≤ K) ↔
          (finrank F (K.map e.toLinearMap) = r ∧
            (e • P).submodule ≤ K.map e.toLinearMap)
        rw [e.finrank_map_eq, hp]
    have transport₂ (e : V ≃ₗ[F] V) (P Q : Projectivization F V) :
        Nat.card {K : Submodule F V //
          finrank F K = r ∧ P.submodule ≤ K ∧ Q.submodule ≤ K} =
          Nat.card {K : Submodule F V // finrank F K = r ∧
            (e • P).submodule ≤ K ∧ (e • Q).submodule ≤ K} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv fun K => by
        change (finrank F K = r ∧ P.submodule ≤ K ∧ Q.submodule ≤ K) ↔
          (finrank F (K.map e.toLinearMap) = r ∧
            (e • P).submodule ≤ K.map e.toLinearMap ∧
            (e • Q).submodule ≤ K.map e.toLinearMap)
        rw [e.finrank_map_eq, hp, hp]
    let R := Nat.card {K : Submodule F V // finrank F K = r ∧ P₀.submodule ≤ K}
    let L := Nat.card {K : Submodule F V //
      finrank F K = r ∧ P₀.submodule ≤ K ∧ Q₀.submodule ≤ K}
    have two : ∀ {P Q P' Q' : Projectivization F V}, P ≠ Q → P' ≠ Q' →
        ∃ e : V ≃ₗ[F] V, e • P = P' ∧ e • Q = Q' :=
      MulAction.is_two_pretransitive_iff.mp inferInstance
    have hR (P : Projectivization F V) :
        Nat.card {K : Submodule F V // finrank F K = r ∧ P.submodule ≤ K} = R := by
      obtain ⟨Q, hQ⟩ : ∃ Q : Projectivization F V, P ≠ Q := by
        by_cases h : P = P₀
        · exact ⟨Q₀, h ▸ hPQ⟩
        · exact ⟨P₀, h⟩
      obtain ⟨e, he, _⟩ := two hPQ hQ
      simpa [he, R] using (transport e P₀).symm
    have hL (P Q : Projectivization F V) (h : P ≠ Q) :
        Nat.card {K : Submodule F V //
          finrank F K = r ∧ P.submodule ≤ K ∧ Q.submodule ≤ K} = L := by
      obtain ⟨e, heP, heQ⟩ := two hPQ h
      simpa [heP, heQ, L] using (transport₂ e P₀ Q₀).symm
    have hQnot : Q₀.rep ∉ P₀.submodule := by
      intro h
      apply hPQ
      apply Projectivization.submodule_injective
      apply (eq_of_le_of_finrank_eq (S₁ := Q₀.submodule) (S₂ := P₀.submodule) ?_ ?_).symm
      · rw [Q₀.submodule_eq]
        exact (span_singleton_le_iff_mem _ _).mpr h
      · rw [P₀.finrank_submodule, Q₀.finrank_submodule]
    obtain ⟨K, hPK, hKr, hQK⟩ :=
      subspaceExtensionAvoiding P₀.submodule Q₀.rep hQnot r
        (by rw [P₀.finrank_submodule]; exact hr) hrV
    let inclusion : {K : Submodule F V //
        finrank F K = r ∧ P₀.submodule ≤ K ∧ Q₀.submodule ≤ K} →
        {K : Submodule F V // finrank F K = r ∧ P₀.submodule ≤ K} :=
      fun K => ⟨K.val, K.property.1, K.property.2.1⟩
    have hinj : Function.Injective inclusion := by
      intro A B h
      apply Subtype.ext
      change (inclusion A).val = (inclusion B).val
      exact congrArg Subtype.val h
    have hnotsurj : ¬ Function.Surjective inclusion := by
      intro hs
      obtain ⟨A, hA⟩ := hs ⟨K, hKr, hPK⟩
      apply hQK
      have hAK : A.val = K := congrArg Subtype.val hA
      rw [← hAK]
      exact A.property.2.2 (by rw [Q₀.submodule_eq]; exact mem_span_singleton_self _)
    have hLR : L < R := by
      letI := Fintype.ofFinite (Submodule F V)
      change Nat.card _ < Nat.card _
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Fintype.card_lt_of_injective_not_surjective inclusion hinj hnotsurj
    exact ⟨R, L, hLR, hR, hL⟩
  have weightedEncoder :
    ∃ n d gap : ℕ, 0 < d ∧ 0 < gap ∧
      ∃ E : V →ₗ[F] (Fin n → Fin m → F), Function.Injective E ∧
        ∀ x y (hxy : x ≠ y), hammingDist (E x) (E y) =
          if Projectivization.mk F (x - y) (sub_ne_zero.mpr hxy) ∈ B then d
          else d + gap := by
    classical
    letI : Finite (Submodule F V) :=
      Finite.of_injective (fun K : Submodule F V => (K : Set V)) SetLike.coe_injective
    letI := Fintype.ofFinite (Submodule F V)
    obtain ⟨P₀, hP₀, Q₀, hQ₀, hPQ⟩ := Finset.one_lt_card.mp hB
    obtain ⟨R, L, hLR, hR, hL⟩ :=
      incidenceCounts r hr (by omega) P₀ Q₀ hPQ
    let I := (P : B) × {K : Submodule F V // finrank F K = r ∧ P.val.submodule ≤ K}
    let n := Fintype.card I
    let ν : Fin n ≃ I := (Fintype.equivFin I).symm
    let π (K : {K : Submodule F V // finrank F K = r}) : V →ₗ[F] (Fin m → F) :=
      (LinearEquiv.ofFinrankEq (V ⧸ K.val) (Fin m → F) (by
        have h := K.val.finrank_quotient_add_finrank
        rw [K.property, hdim] at h
        simpa using (show finrank F (V ⧸ K.val) = m by omega))).toLinearMap.comp K.val.mkQ
    have hπ (K : {K : Submodule F V // finrank F K = r}) (x y : V) :
        π K x = π K y ↔ x - y ∈ K.val := by
      rw [← sub_eq_zero, ← map_sub]
      change (LinearEquiv.ofFinrankEq (V ⧸ K.val) (Fin m → F) _) (K.val.mkQ (x-y)) = 0 ↔ _
      rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    let E : V →ₗ[F] (Fin n → Fin m → F) := {
      toFun := fun x j => π ⟨(ν j).2.val, (ν j).2.property.1⟩ x
      map_add' := by intro x y; funext j; exact map_add _ _ _
      map_smul' := by intro c x; funext j; exact map_smul _ _ _ }
    have hn : n = B.card * R := by
      change Fintype.card I = _
      rw [← Nat.card_eq_fintype_card, Nat.card_sigma]
      simp only [hR, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
    have agree (Q : Projectivization F V) :
        Nat.card {i : I // Q.submodule ≤ i.2.val} =
          if Q ∈ B then R + (B.card - 1) * L else B.card * L := by
      let e : {i : I // Q.submodule ≤ i.2.val} ≃
          ((P : B) × {K : Submodule F V //
            finrank F K = r ∧ P.val.submodule ≤ K ∧ Q.submodule ≤ K}) := {
        toFun := fun i => ⟨i.val.1, i.val.2.val,
          i.val.2.property.1, i.val.2.property.2, i.property⟩
        invFun := fun i => ⟨⟨i.1, i.2.val, i.2.property.1, i.2.property.2.1⟩,
          i.2.property.2.2⟩
        left_inv := by intro i; rfl
        right_inv := by intro i; rfl }
      rw [Nat.card_congr e, Nat.card_sigma]
      have ht (P : B) :
          Nat.card {K : Submodule F V //
            finrank F K = r ∧ P.val.submodule ≤ K ∧ Q.submodule ≤ K} =
            if P.val = Q then R else L := by
        split_ifs with h
        · subst Q
          calc
            _ = Nat.card {K : Submodule F V // finrank F K = r ∧ P.val.submodule ≤ K} :=
              Nat.card_congr (Equiv.subtypeEquivRight fun K => by tauto)
            _ = R := hR P.val
        · exact hL P.val Q h
      simp_rw [ht]
      rw [Finset.sum_coe_sort B (fun P => if P = Q then R else L)]
      by_cases hQ : Q ∈ B
      · rw [if_pos hQ, ← Finset.sum_erase_add _ _ hQ]
        have ht : ∑ P ∈ B.erase Q, (if P = Q then R else L) = (B.card-1)*L := by
          calc
            _ = ∑ _P ∈ B.erase Q, L := by
              apply Finset.sum_congr rfl
              intro P hP
              rw [if_neg (Finset.mem_erase.mp hP).1]
            _ = _ := by simp [Finset.card_erase_of_mem hQ]
        rw [ht, if_pos rfl]
        omega
      · rw [if_neg hQ]
        calc
          _ = ∑ _P ∈ B, L := by
            apply Finset.sum_congr rfl
            intro P hP
            rw [if_neg (show P ≠ Q from fun h => hQ (h ▸ hP))]
          _ = _ := by simp
    have distance (x y : V) (hxy : x ≠ y) :
        hammingDist (E x) (E y) =
          if Projectivization.mk F (x-y) (sub_ne_zero.mpr hxy) ∈ B
          then (R-L)*(B.card-1) else (R-L)*(B.card-1)+(R-L) := by
      let Q := Projectivization.mk F (x-y) (sub_ne_zero.mpr hxy)
      have heq (j : Fin n) : E x j = E y j ↔ Q.submodule ≤ (ν j).2.val := by
        change π _ x = π _ y ↔ _
        rw [hπ, Projectivization.submodule_mk, span_singleton_le_iff_mem]
      have hc : (Finset.univ.filter (fun j : Fin n => E x j = E y j)).card =
          Nat.card {i : I // Q.submodule ≤ i.2.val} := by
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
        exact Nat.card_congr (Equiv.subtypeEquiv ν fun j => heq j)
      have htotal : hammingDist (E x) (E y) +
          Nat.card {i : I // Q.submodule ≤ i.2.val} = n := by
        rw [← hc, hammingDist, add_comm]
        simpa only [not_not, Finset.card_univ, Fintype.card_fin] using
          (Finset.card_filter_add_card_filter_not
            (s := Finset.univ) (fun j : Fin n => E x j = E y j))
      rw [agree] at htotal
      have htotal' : hammingDist (E x) (E y) +
          (if Q ∈ B then R + (B.card-1)*L else B.card*L) = B.card*R :=
        htotal.trans hn
      clear htotal
      have htotal := htotal'
      change _ = if Q ∈ B then _ else _
      by_cases hQ : Q ∈ B
      · rw [if_pos hQ] at htotal ⊢
        have hb : 1 ≤ B.card := by omega
        have hmul : (R-L)*(B.card-1) + (R+(B.card-1)*L) = B.card*R := by
          nlinarith [Nat.sub_add_cancel (Nat.le_of_lt hLR),
            Nat.sub_add_cancel (show 1 ≤ B.card by omega)]
        omega
      · rw [if_neg hQ] at htotal ⊢
        have hmul : (R-L)*(B.card-1)+(R-L)+B.card*L = B.card*R := by
          nlinarith [Nat.sub_add_cancel (Nat.le_of_lt hLR),
            Nat.sub_add_cancel (show 1 ≤ B.card by omega)]
        omega
    have hd : 0 < (R-L)*(B.card-1) := Nat.mul_pos (by omega) (by omega)
    have hinj : Function.Injective E := by
      intro x y he
      by_contra hxy
      have hh := distance x y hxy
      rw [he, hammingDist_self] at hh
      split_ifs at hh <;> omega
    exact ⟨n, (R-L)*(B.card-1), R-L, hd, by omega, E, hinj, distance⟩
  obtain ⟨n, d, gap, hd, hgap, E, hE, distance⟩ := weightedEncoder
  let C := Finset.univ.image E
  have rangeCode : (E.range : Set (Fin n → Fin m → F)) = (C : Set _) := by
    ext z
    change (∃ x, E x = z) ↔ z ∈ C
    simp [C]
  have nk : k ≤ n := by
    have hi := LinearMap.finrank_le_finrank_of_injective hE
    have hi' : k * m ≤ n * m := by
      simpa [hdim, hkm, Module.finrank_pi_fintype] using hi
    nlinarith
  have hC : IsCode C k d := by
    refine ⟨nk, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hE, Finset.card_univ,
        Module.card_eq_pow_finrank (K := F), hdim, hkm]
      simp [Nat.card_eq_fintype_card, pow_mul, Nat.mul_comm]
    · constructor
      · intro a ha b hb hab
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
        have hxy : x ≠ y := fun heq => hab (congrArg E heq)
        rw [distance x y hxy]
        split_ifs <;> omega
      · obtain ⟨P, hP⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
        refine ⟨E P.rep, Finset.mem_image.mpr ⟨P.rep, Finset.mem_univ _, rfl⟩,
          E 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩,
          hE.ne P.rep_nonzero, ?_⟩
        simpa only [sub_zero, Projectivization.mk_rep, if_pos hP] using
          distance P.rep 0 P.rep_nonzero
  have sep : ∀ x y, x ≠ y → hammingDist (E x) (E y) = d → label x ≠ label y := by
    intro x y hxy heq hequal
    have hm := hlabel x y hxy hequal
    rw [distance x y hxy, if_neg hm] at heq
    omega
  have graphExtension : IsExtension C
      (Finset.univ.image (fun x => Fin.snoc (E x) (label x))) k d := by
    classical
    let G : V → Fin (n + 1) → Fin m → F := fun x => Fin.snoc (E x) (label x)
    have hG : Function.Injective G := by
      intro x y h
      apply hE
      simpa [G] using congrArg Fin.init h
    have distance (x y : V) : hammingDist (G x) (G y) =
        hammingDist (E x) (E y) + if label x = label y then 0 else 1 := by
      simp only [hammingDist, Finset.card_filter, Fin.sum_univ_castSucc,
        G, Fin.snoc_castSucc, Fin.snoc_last]
      by_cases h : label x = label y <;> simp [h]
    refine ⟨hC, ⟨Nat.le_trans hC.1 (Nat.le_succ n), ?_, ?_⟩, ?_⟩
    · rw [Finset.card_image_of_injective _ hG]
      simpa only [C, Finset.card_image_of_injective _ hE] using hC.2.1
    · constructor
      · intro a ha b hb hab
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
        have hxy : x ≠ y := fun h => hab (congrArg G h)
        have old := hC.2.2.1 (E x) (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
          (E y) (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩) (hE.ne hxy)
        rw [distance]
        by_cases heq : hammingDist (E x) (E y) = d
        · simp [sep x y hxy heq, heq]
        · split_ifs <;> omega
      · obtain ⟨a, ha, b, hb, hab, hd⟩ := hC.2.2.2
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
        have hxy : x ≠ y := fun h => hab (congrArg E h)
        refine ⟨G x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩,
          G y, Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩, hG.ne hxy, ?_⟩
        rw [distance]
        simp [sep x y hxy hd, hd]
    · ext w
      simp [C, Finset.mem_image, Fin.init_snoc]

  refine ⟨n, d, C, hC, ⟨E.range, rangeCode⟩,
    ⟨_, graphExtension⟩, ?_⟩
  rintro ⟨D, hext, hadd⟩
  have linearCriterion : ∃ fS : E.range →ₗ[F] (Fin m → F),
      ∀ x y : E.range, x ≠ y →
        hammingDist (x : Fin n → Fin m → F) y = d → fS x ≠ fS y := by
    classical
    obtain ⟨T, hT⟩ := hadd
    have memS (x : Fin n → Fin m → F) : x ∈ E.range ↔ x ∈ C := Set.ext_iff.mp rangeCode x
    have memT (x : Fin (n + 1) → Fin m → F) : x ∈ T ↔ x ∈ D :=
      Set.ext_iff.mp hT x
    let puncture : T →ₗ[F] E.range :=
      { toFun := fun z => ⟨Fin.init z.val, by
          have hz : z.val ∈ D := (memT _).mp z.property
          have hi : Fin.init z.val ∈ C := by
            rw [← hext.2.2]
            exact Finset.mem_image.mpr ⟨z.val, hz, rfl⟩
          exact (memS _).mpr hi⟩
        map_add' := fun x y => by ext i j; rfl
        map_smul' := fun a x => by ext i j; rfl }
    have surj : Function.Surjective puncture := by
      intro x
      have hx : (x : Fin n → Fin m → F) ∈ C := (memS _).mp x.property
      rw [← hext.2.2] at hx
      obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
      refine ⟨⟨z, (memT _).mpr hz⟩, ?_⟩
      exact Subtype.ext hzx
    let sEquiv : E.range ≃ {x // x ∈ C} :=
      { toFun := fun x => ⟨x, (memS _).mp x.property⟩
        invFun := fun x => ⟨x, (memS _).mpr x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let tEquiv : T ≃ {x // x ∈ D} :=
      { toFun := fun x => ⟨x, (memT _).mp x.property⟩
        invFun := fun x => ⟨x, (memT _).mpr x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have cardeq : Fintype.card T = Fintype.card E.range := by
      rw [Fintype.card_congr tEquiv, Fintype.card_congr sEquiv]
      simpa using hext.2.1.2.1.trans hext.1.2.1.symm
    let iso : T ≃ₗ[F] E.range := LinearEquiv.ofBijective puncture
      ((Fintype.bijective_iff_surjective_and_card puncture).mpr ⟨surj, cardeq⟩)
    let last : T →ₗ[F] (Fin m → F) :=
      { toFun := fun z => z.1 (Fin.last n)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine ⟨last.comp iso.symm.toLinearMap, ?_⟩
    intro x y hxy hdist hequal
    let u := iso.symm x
    let v := iso.symm y
    have hu : (u : Fin (n + 1) → Fin m → F) ∈ D := by
      exact (memT _).mp u.property
    have hv : (v : Fin (n + 1) → Fin m → F) ∈ D := by
      exact (memT _).mp v.property
    have huv : (u : Fin (n + 1) → Fin m → F) ≠ v := by
      intro h
      apply hxy
      exact iso.symm.injective (Subtype.ext h)
    have hiu : Fin.init (u : Fin (n + 1) → Fin m → F) = x :=
      congrArg Subtype.val (iso.apply_symm_apply x)
    have hiv : Fin.init (v : Fin (n + 1) → Fin m → F) = y :=
      congrArg Subtype.val (iso.apply_symm_apply y)
    have sameLast : u.1 (Fin.last n) = v.1 (Fin.last n) := hequal
    have distance : hammingDist (u : Fin (n + 1) → Fin m → F) v = d := by
      rw [← Fin.snoc_init_self u.1, ← Fin.snoc_init_self v.1, hiu, hiv]
      simpa only [hammingDist, Finset.card_filter, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last, sameLast, ne_eq, not_true_eq_false,
        ite_false, add_zero] using hdist
    have lower := hext.2.1.2.2.1 u hu v hv huv
    omega
  obtain ⟨fS, hseparates⟩ := linearCriterion
  let f : V →ₗ[F] (Fin m → F) := fS.comp E.rangeRestrict
  have kerDim : r ≤ finrank F f.ker := by
    have eq := f.finrank_range_add_finrank_ker
    have le := f.range.finrank_le
    have alphaDim : finrank F (Fin m → F) = m := by simp
    rw [hdim] at eq
    omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := F) (M := f.ker) kerDim
  let L : Submodule F f.ker := Submodule.span F (Set.range v)
  let K : Submodule F V := L.map f.ker.subtype
  have dimK : finrank F K = r := by
    rw [Submodule.finrank_map_subtype_eq]
    exact (finrank_span_eq_card hv).trans (Fintype.card_fin r)
  have leK : K ≤ f.ker := by
    rintro z ⟨w, _, rfl⟩
    exact w.property
  obtain ⟨P, hP, hPK⟩ := block K dimK
  have repK : P.rep ∈ K := by
    apply hPK
    rw [P.submodule_eq]
    exact mem_span_singleton_self P.rep
  have fzero : f P.rep = 0 := (LinearMap.mem_ker.mp (leK repK))
  have dist : hammingDist (E P.rep) (E 0) = d := by
    simpa only [sub_zero, Projectivization.mk_rep, if_pos hP] using
      distance P.rep 0 P.rep_nonzero
  have different : E.rangeRestrict P.rep ≠ E.rangeRestrict 0 := by
    intro heq
    exact P.rep_nonzero (hE (congrArg Subtype.val heq))
  apply hseparates (E.rangeRestrict P.rep) (E.rangeRestrict 0) different dist
  change f P.rep = f 0
  simpa only [map_zero] using fzero

end D5.S3.Combinatorics.AdditiveCodes
