/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFour
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFour
   mirror-E: none(waiver:fixed-row-four-proof)
   anchors: []
   utility: none
   digest: Formal proof of the row-four nonnesting generating-function identity. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveClassify
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFour

open PowerSeries
open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingFourIncCount
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveIncUnique
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveLarge
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveLargeConverse
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoInsert
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveTwoConstruct
open D5.S3.Combinatorics.Nonnesting.NonnestingFourPrimitiveClassify

-- The localized cardinality arguments need more elaboration heartbeats.
set_option maxHeartbeats 1000000 in
theorem result : NonnestingDefs.claimFour := by
  classical
  let Λ := [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]
  let firstFactorData (Λ : List (List ℕ)) (n : ℕ) : Type :=
    Σ k : {j : ℕ // j ∈ Finset.Icc 1 n},
      {u : List ℕ // u ∈ NonnestingDefs.avoiders k.1 Λ ∧ primitive u k.1} ×
        {v : List ℕ // v ∈ NonnestingDefs.avoiders (n - k.1) Λ}
  have classCount_zero (Λ : List (List ℕ))
      (hΛ : ∀ σ ∈ Λ, σ ≠ []) :
      (NonnestingDefs.avoiders 0 Λ).ncard = 1 := by
    have hset : NonnestingDefs.avoiders 0 Λ = ({[]} : Set (List ℕ)) := by
      ext w
      constructor
      · intro hw
        have hperm := hw.1
        have hlen : w.length = 0 := by
          simpa using hperm.length_eq
        have : w = [] := List.eq_nil_of_length_eq_zero hlen
        simpa [this]
      · intro hw
        have hw' : w = [] := by simpa using hw
        subst w
        simp only [NonnestingDefs.avoiders, NonnestingDefs.Occurs]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp
        · simp [D5.S3.Combinatorics.ArrowWilfDefs.Contains]
        · simp [D5.S3.Combinatorics.ArrowWilfDefs.Contains]
        · intro σ hσ hocc
          rcases hocc with ⟨x, _, _, hsub, _⟩
          have hempty : σ.map x = [] := by
            exact List.eq_nil_of_sublist_nil hsub
          have : σ = [] := by
            simpa using hempty
          exact hΛ σ hσ this
    rw [hset, Set.ncard_singleton]
  have classCount_convolution (Λ : List (List ℕ)) (n : ℕ)
      (hΛ : ∀ σ ∈ Λ, sumIndecomposable σ ∧
        (∀ a ∈ σ, 1 ≤ a) ∧
        (∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → i ∈ σ))
      (hn : 0 < n) :
      (NonnestingDefs.avoiders n Λ).ncard =
        ∑ j ∈ Finset.Icc 1 n,
          ({w : List ℕ | w ∈ NonnestingDefs.avoiders j Λ ∧ primitive w j}.ncard) *
            (NonnestingDefs.avoiders (n - j) Λ).ncard := by
    classical
    let firstFactorEquiv (Λ : List (List ℕ)) (n : ℕ)
        (hΛ : ∀ σ ∈ Λ, sumIndecomposable σ ∧
          (∀ a ∈ σ, 1 ≤ a) ∧
          (∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → i ∈ σ))
        (hn : 0 < n) :
        firstFactorData Λ n ≃ NonnestingDefs.avoiders n Λ := by
      have sumAvoiders (Λ : List (List ℕ)) (m n : ℕ) (u v : List ℕ)
          (hΛ : ∀ σ ∈ Λ, sumIndecomposable σ ∧
            (∀ a ∈ σ, 1 ≤ a) ∧
            (∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → i ∈ σ))
          (hpermU : u.Perm ((List.range' 1 m).flatMap fun i => [i, i]))
          (hpermV : v.Perm ((List.range' 1 n).flatMap fun i => [i, i])) :
          directSum m u v ∈ NonnestingDefs.avoiders (m + n) Λ ↔
            u ∈ NonnestingDefs.avoiders m Λ ∧
              v ∈ NonnestingDefs.avoiders n Λ := by
        have hubound : ∀ a ∈ u, a ≤ m := by
          intro a ha
          have hbase := hpermU.mem_iff.mp ha
          obtain ⟨i, hi, hii⟩ := List.mem_flatMap.mp hbase
          have hai : a = i := by simpa using hii
          subst a
          have hirange : 1 ≤ i ∧ i < 1 + m := by simpa using hi
          omega
        have hvpositive : ∀ b ∈ v, 1 ≤ b := by
          intro b hb
          have hbase := hpermV.mem_iff.mp hb
          obtain ⟨i, hi, hii⟩ := List.mem_flatMap.mp hbase
          have hbi : b = i := by simpa using hii
          subst b
          have hirange : 1 ≤ i ∧ i < 1 + n := by simpa using hi
          omega
        have hnest1 : sumIndecomposable [1, 2, 2, 1] := by
          intro k hk
          fin_cases k
          · simp at hk
          · dsimp at *; exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide⟩
          · dsimp at *; exact ⟨⟨1, by decide⟩, ⟨1, by decide⟩, by decide⟩
          · dsimp at *; exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩, by decide⟩
        have hnest2 : sumIndecomposable [2, 1, 1, 2] := by
          intro k hk
          fin_cases k
          · simp at hk
          · dsimp at *; exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩, by decide⟩
          · dsimp at *; exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩, by decide⟩
          · dsimp at *; exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩, by decide⟩
        have hnest1iff := occurs_directSum_iff m u v [1, 2, 2, 1]
          hubound hvpositive hnest1 (by decide) (by decide)
        have hnest2iff := occurs_directSum_iff m u v [2, 1, 1, 2]
          hubound hvpositive hnest2 (by decide) (by decide)
        constructor
        · intro hsum
          refine ⟨⟨hpermU, ?_, ?_, ?_⟩, ⟨hpermV, ?_, ?_, ?_⟩⟩
          · intro h
            exact hsum.2.1 (hnest1iff.mpr (Or.inl h))
          · intro h
            exact hsum.2.2.1 (hnest2iff.mpr (Or.inl h))
          · intro σ hσ h
            obtain ⟨hindec, hpos, hfull⟩ := hΛ σ hσ
            exact hsum.2.2.2 σ hσ
              ((occurs_directSum_iff m u v σ hubound hvpositive hindec hpos hfull).mpr
                (Or.inl h))
          · intro h
            exact hsum.2.1 (hnest1iff.mpr (Or.inr h))
          · intro h
            exact hsum.2.2.1 (hnest2iff.mpr (Or.inr h))
          · intro σ hσ h
            obtain ⟨hindec, hpos, hfull⟩ := hΛ σ hσ
            exact hsum.2.2.2 σ hσ
              ((occurs_directSum_iff m u v σ hubound hvpositive hindec hpos hfull).mpr
                (Or.inr h))
        · rintro ⟨hu, hv⟩
          change (directSum m u v).Perm
              ((List.range' 1 (m + n)).flatMap fun i => [i, i]) ∧
            ¬ NonnestingDefs.Occurs [1, 2, 2, 1] (directSum m u v) ∧
            ¬ NonnestingDefs.Occurs [2, 1, 1, 2] (directSum m u v) ∧
            ∀ σ ∈ Λ, ¬ NonnestingDefs.Occurs σ (directSum m u v)
          refine ⟨directSum_perm m n u v hpermU hpermV, ?_, ?_, ?_⟩
          · intro hocc
            rcases hnest1iff.mp hocc with h | h
            · exact hu.2.1 h
            · exact hv.2.1 h
          · intro hocc
            rcases hnest2iff.mp hocc with h | h
            · exact hu.2.2.1 h
            · exact hv.2.2.1 h
          · intro σ hσ hocc
            obtain ⟨hindec, hpos, hfull⟩ := hΛ σ hσ
            have hloc := (occurs_directSum_iff m u v σ
              hubound hvpositive hindec hpos hfull).mp hocc
            rcases hloc with h | h
            · exact hu.2.2.2 σ hσ h
            · exact hv.2.2.2 σ hσ h
      have factorUnique (Λ : List (List ℕ)) (n : ℕ) (w : List ℕ)
          (hΛ : ∀ σ ∈ Λ, sumIndecomposable σ ∧
            (∀ a ∈ σ, 1 ≤ a) ∧
            (∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → i ∈ σ))
          (hw : w ∈ NonnestingDefs.avoiders n Λ) (hn : 0 < n) :
          ∃! t : ℕ × List ℕ × List ℕ,
            1 ≤ t.1 ∧ t.1 ≤ n ∧
            w = directSum t.1 t.2.1 t.2.2 ∧ primitive t.2.1 t.1 ∧
            t.2.1 ∈ NonnestingDefs.avoiders t.1 Λ ∧
            t.2.2 ∈ NonnestingDefs.avoiders (n - t.1) Λ := by
        have hmeta : ∀ ku : ℕ × List ℕ,
            ku.2.Perm ((List.range' 1 ku.1).flatMap fun i => [i, i]) →
            ku.2.length = 2 * ku.1 ∧ (∀ x ∈ ku.2, 1 ≤ x ∧ x ≤ ku.1) := by
          intro ku hperm
          have hlenList : ∀ l : List ℕ,
              (l.flatMap fun i => [i, i]).length = 2 * l.length := by
            intro l
            induction l with
            | nil => simp
            | cons a l ih => simp [ih]; omega
          constructor
          · have hl := hperm.length_eq
            simpa [hlenList] using hl
          · intro x hx
            have hbase := hperm.mem_iff.mp hx
            obtain ⟨i, hi, hii⟩ := List.mem_flatMap.mp hbase
            have hxi : x = i := by simpa using hii
            subst x
            have hirange : 1 ≤ i ∧ i < 1 + ku.1 := by simpa using hi
            omega
        obtain ⟨k, u, v, hk, hkle, heq, hprim, huperm, hvperm⟩ :=
          first_primitive_factor n w hw.1 hn
        have ⟨hucls, hvcls⟩ :=
          (sumAvoiders Λ k (n - k) u v hΛ huperm hvperm).mp (by
            simpa [Nat.add_sub_of_le hkle, heq] using hw)
        refine ⟨(k, u, v), ⟨hk, hkle, heq, hprim, hucls, hvcls⟩, ?_⟩
        rintro ⟨j, u', v'⟩ ⟨hj, hjle, heq', hprim', hucls', hvcls'⟩
        have ⟨hlen, hubound⟩ := hmeta (k, u) huperm
        have ⟨hlen', hubound'⟩ := hmeta (j, u') hucls'.1
        have hvpositive : ∀ x ∈ v, 1 ≤ x := by
          intro x hx
          exact ((hmeta (n - k, v) hvperm).2 x hx).1
        have hvpositive' : ∀ x ∈ v', 1 ≤ x := by
          intro x hx
          exact ((hmeta (n - j, v') hvcls'.1).2 x hx).1
        obtain ⟨hkj, huu, hvv⟩ := primitive_split_unique w u v u' v' k j
          heq heq' hlen hlen' hubound hubound' hvpositive hvpositive' hk hj hprim hprim'
        cases hkj
        cases huu
        cases hvv
        rfl
      let f : firstFactorData Λ n → NonnestingDefs.avoiders n Λ := fun t => by
        let k := t.1.1
        let u := t.2.1.1
        let v := t.2.2.1
        have hkn : k ≤ n := (Finset.mem_Icc.mp t.1.2).2
        refine ⟨directSum k u v, ?_⟩
        have hsum := (sumAvoiders Λ k (n - k) u v hΛ
          t.2.1.2.1.1 t.2.2.2.1).mpr ⟨t.2.1.2.1, t.2.2.2⟩
        simpa [Nat.add_sub_of_le hkn] using hsum
      apply Equiv.ofBijective f
      constructor
      · intro t t' hft
        have hw : (f t).1 = (f t').1 := congrArg Subtype.val hft
        let w := (f t).1
        have huniq := factorUnique Λ n w hΛ (f t).2 hn
        have ht : (1 ≤ t.1.1 ∧ t.1.1 ≤ n ∧
            w = directSum t.1.1 t.2.1.1 t.2.2.1 ∧
            primitive t.2.1.1 t.1.1 ∧
            t.2.1.1 ∈ NonnestingDefs.avoiders t.1.1 Λ ∧
            t.2.2.1 ∈ NonnestingDefs.avoiders (n - t.1.1) Λ) := by
          exact ⟨(Finset.mem_Icc.mp t.1.2).1, (Finset.mem_Icc.mp t.1.2).2,
            rfl, t.2.1.2.2, t.2.1.2.1, t.2.2.2⟩
        have ht' : (1 ≤ t'.1.1 ∧ t'.1.1 ≤ n ∧
            w = directSum t'.1.1 t'.2.1.1 t'.2.2.1 ∧
            primitive t'.2.1.1 t'.1.1 ∧
            t'.2.1.1 ∈ NonnestingDefs.avoiders t'.1.1 Λ ∧
            t'.2.2.1 ∈ NonnestingDefs.avoiders (n - t'.1.1) Λ) := by
          exact ⟨(Finset.mem_Icc.mp t'.1.2).1, (Finset.mem_Icc.mp t'.1.2).2,
            hw, t'.2.1.2.2, t'.2.1.2.1, t'.2.2.2⟩
        have heq : (t.1.1, t.2.1.1, t.2.2.1) =
            (t'.1.1, t'.2.1.1, t'.2.2.1) := huniq.unique ht ht'
        rcases t with ⟨⟨k, hk⟩, ⟨⟨u, hu⟩, ⟨v, hv⟩⟩⟩
        rcases t' with ⟨⟨k', hk'⟩, ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩⟩
        simp only at heq
        cases heq
        rfl
      · intro w
        obtain ⟨⟨k, u, v⟩, ⟨hk, hkn, heq, hprim, hucls, hvcls⟩, _⟩ :=
          factorUnique Λ n w.1 hΛ w.2 hn
        let t : firstFactorData Λ n :=
          ⟨⟨k, Finset.mem_Icc.mpr ⟨hk, hkn⟩⟩,
            ⟨⟨u, ⟨hucls, hprim⟩⟩, ⟨v, hvcls⟩⟩⟩
        refine ⟨t, ?_⟩
        apply Subtype.ext
        exact heq.symm
    have hfinite (j : ℕ) : (NonnestingDefs.avoiders j Λ).Finite := by
      let base : List ℕ := (List.range' 1 j).flatMap (fun i => [i, i])
      have hbase : {w : List ℕ | w ∈ base.permutations}.Finite := by
        simpa using (Set.finite_mem_finset base.permutations.toFinset)
      apply hbase.subset
      intro w hw
      simpa [base, List.mem_permutations] using hw.1
    letI : Fintype (NonnestingDefs.avoiders n Λ) :=
      (hfinite n).fintype
    letI : Fintype {j : ℕ // j ∈ Finset.Icc 1 n} :=
      Finset.Subtype.fintype (Finset.Icc 1 n)
    letI : (k : {j : ℕ // j ∈ Finset.Icc 1 n}) →
        Fintype
          ({u : List ℕ // u ∈ NonnestingDefs.avoiders k.1 Λ ∧ primitive u k.1} ×
            {v : List ℕ // v ∈ NonnestingDefs.avoiders (n - k.1) Λ}) := fun k => by
      letI : Fintype
          {u : List ℕ // u ∈ NonnestingDefs.avoiders k.1 Λ ∧ primitive u k.1} :=
        ((hfinite k.1).subset (by
          intro u hu
          exact hu.1)).fintype
      letI : Fintype {v : List ℕ // v ∈ NonnestingDefs.avoiders (n - k.1) Λ} :=
        (hfinite (n - k.1)).fintype
      infer_instance
    letI : Fintype (firstFactorData Λ n) := by
      unfold firstFactorData
      infer_instance
    calc
      (NonnestingDefs.avoiders n Λ).ncard = Fintype.card (NonnestingDefs.avoiders n Λ) := by
        simpa using
          (Set.fintypeCard_eq_ncard (s := NonnestingDefs.avoiders n Λ)).symm
      _ = Fintype.card (firstFactorData Λ n) :=
        (Fintype.card_congr (firstFactorEquiv Λ n hΛ hn)).symm
      _ = ∑ j ∈ Finset.Icc 1 n,
            ({w : List ℕ | w ∈ NonnestingDefs.avoiders j Λ ∧ primitive w j}.ncard) *
              (NonnestingDefs.avoiders (n - j) Λ).ncard := by
        simp [firstFactorData, Fintype.card_sigma, Fintype.card_prod,
          Set.fintypeCard_eq_ncard]
        simp_rw [← Nat.card_eq_fintype_card]
        change (∑ i ∈ (Finset.Icc 1 n).attach,
            ({w : List ℕ | w ∈ NonnestingDefs.avoiders i.1 Λ ∧
              primitive w i.1}.ncard) *
              (NonnestingDefs.avoiders (n - i.1) Λ).ncard) =
          ∑ j ∈ Finset.Icc 1 n,
            ({w : List ℕ | w ∈ NonnestingDefs.avoiders j Λ ∧ primitive w j}.ncard) *
              (NonnestingDefs.avoiders (n - j) Λ).ncard
        exact Finset.sum_attach (Finset.Icc 1 n)
          (fun j =>
            ({w : List ℕ | w ∈ NonnestingDefs.avoiders j Λ ∧ primitive w j}.ncard) *
              (NonnestingDefs.avoiders (n - j) Λ).ncard)
  have primitiveCount_large (n : ℕ) (hn : 3 ≤ n) :
      ({w : List ℕ | w ∈ NonnestingDefs.avoiders n Λ ∧ primitive w n}.ncard) =
        2 ^ (n - 2) + 2 := by
    classical
    let Λ := [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]
    have hfinite (j : ℕ) : (NonnestingDefs.avoiders j Λ).Finite := by
      let base : List ℕ := (List.range' 1 j).flatMap (fun i => [i, i])
      have hbase : {w : List ℕ | w ∈ base.permutations}.Finite := by
        simpa using (Set.finite_mem_finset base.permutations.toFinset)
      apply hbase.subset
      intro w hw
      simpa [base, List.mem_permutations] using hw.1
    let P : Type := {w : List ℕ // w ∈ NonnestingDefs.avoiders n Λ ∧ primitive w n}
    letI : Fintype
        ↑({w : List ℕ | w ∈ NonnestingDefs.avoiders n Λ ∧
          primitive w n} : Set (List ℕ)) :=
      ((hfinite n).subset
        (by intro w hw; exact hw.1)).fintype
    letI : Fintype P := ((hfinite n).subset
      (by intro w hw; exact hw.1)).fintype
    letI : Fintype (increasingWords (n - 1)) :=
      ((hfinite (n - 1)).subset
        (by intro w hw; exact hw.1)).fintype
    have hsmall : 1 ≤ n - 2 := by omega
    obtain ⟨pN, hpN⟩ := primitive_increasing_exists n (by omega)
    obtain ⟨pM, hpM⟩ := primitive_increasing_exists (n - 2) hsmall
    have hheadInc (m : ℕ) (hm : 1 ≤ m) (v : increasingWords m) :
        v.1 = 1 :: v.1.tail := by
      have hlen : v.1.length = 2 * m := by
        simpa [Nat.mul_comm] using v.2.1.1.length_eq
      cases heq : v.1 with
      | nil => simp [heq] at hlen; omega
      | cons x r =>
        have hxb : 1 ≤ x ∧ x ≤ m := by
          have hxbase := v.2.1.1.mem_iff.mp (by rw [heq]; simp : x ∈ v.1)
          obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
          have hx : x = i := by simpa using hxi
          subst x
          rw [List.mem_range'_1] at hi
          omega
        have hx : x = 1 := by
          by_contra hne
          have hlt := v.2.2 1 x (by omega) (by omega) hxb.2
          rw [heq] at hlt
          have hf : ((x :: r)).idxOf x = 0 := by simp []
          omega
        simp [hx]
    have hheadM := hheadInc (n - 2) hsmall pM
    have hheadN := hheadInc n (by omega) pN
    let f : increasingWords (n - 1) ⊕ Bool → P := fun t => by
      cases t with
      | inl v =>
        exact ⟨n :: n :: v.1,
          large_prefix_construct n (by omega) v,
          primitive_large_prefix n v.1⟩
      | inr b =>
        cases b with
        | false => exact ⟨pN.1, pN.2.1, hpN⟩
        | true =>
          have hnn : n - 2 + 2 = n := by omega
          exact ⟨2 :: 1 :: 3 :: 2 :: 1 :: shift 2 pM.1.tail,
            by simpa [Λ, hnn] using
              two_insert pM.1.tail (n - 2) (hheadM ▸ pM.2.1),
            by simpa [show n - 2 + 2 = n by omega] using
              two_insert_primitive pM.1.tail (n - 2) (hheadM ▸ pM.2.1)
                (hheadM ▸ hpM)⟩
    have hheadF (t : increasingWords (n - 1) ⊕ Bool) :
        (f t).1.head? =
          match t with
          | Sum.inl _ => some n
          | Sum.inr false => some 1
          | Sum.inr true => some 2 := by
      cases t with
      | inl v => rfl
      | inr b =>
        cases b with
        | false =>
          change pN.1.head? = some 1
          rw [hheadN]
          rfl
        | true => rfl
    have hbij : Function.Bijective f := by
      constructor
      · intro a b hab
        cases a with
        | inl v =>
          cases b with
          | inl u =>
            have heq := congrArg Subtype.val hab
            change n :: n :: v.1 = n :: n :: u.1 at heq
            have hv : v = u := Subtype.ext (by simpa using heq)
            simp [hv]
          | inr b =>
            cases b with
            | false =>
              have heq := congrArg (fun x : P => x.1.head?) hab
              simp only [hheadF] at heq
              simp only [Option.some.injEq] at heq
              omega
            | true =>
              have heq := congrArg (fun x : P => x.1.head?) hab
              simp only [hheadF] at heq
              simp only [Option.some.injEq] at heq
              omega
        | inr ba =>
          cases ba with
          | false =>
            cases b with
            | inl v =>
              have heq := congrArg (fun x : P => x.1.head?) hab
              simp only [hheadF] at heq
              simp only [Option.some.injEq] at heq
              omega
            | inr bb =>
              cases bb with
              | false => rfl
              | true =>
                have heq := congrArg (fun x : P => x.1.head?) hab
                simp only [hheadF] at heq
                simp at heq
          | true =>
            cases b with
            | inl v =>
              have heq := congrArg (fun x : P => x.1.head?) hab
              simp only [hheadF] at heq
              simp only [Option.some.injEq] at heq
              omega
            | inr bb =>
              cases bb with
              | false =>
                have heq := congrArg (fun x : P => x.1.head?) hab
                simp only [hheadF] at heq
                simp at heq
              | true => rfl
      · intro w
        rcases primitive_classification w.1 n w.2.1 hn w.2.2 with
          ⟨v, hv⟩ | ⟨v, hvprim, hv⟩ | ⟨v, hvprim, hv⟩
        · exact ⟨Sum.inl v, Subtype.ext hv.symm⟩
        · have huniq := primitive_increasing_unique n (by omega) v pN hvprim hpN
          exact ⟨Sum.inr false, Subtype.ext
            (hv.trans (congrArg Subtype.val huniq)).symm⟩
        · have huniq := primitive_increasing_unique (n - 2) hsmall
            v pM hvprim hpM
          refine ⟨Sum.inr true, Subtype.ext ?_⟩
          have hv' : w.1 = [2, 1, 3, 2, 1] ++ (shift 2 pM.1).tail := by
            simpa only [congrArg Subtype.val huniq] using hv
          change 2 :: 1 :: 3 :: 2 :: 1 :: shift 2 pM.1.tail = w.1
          rw [hv']
          conv_rhs => rw [hheadM]
          rfl
    have hcard : Fintype.card P = Fintype.card (increasingWords (n - 1)) + 2 := by
      calc
        Fintype.card P = Fintype.card (increasingWords (n - 1) ⊕ Bool) :=
          (Fintype.card_congr (Equiv.ofBijective f hbij)).symm
        _ = Fintype.card (increasingWords (n - 1)) + 2 := by simp
    calc
      ({w : List ℕ | w ∈ NonnestingDefs.avoiders n Λ ∧
        primitive w n}.ncard) = Fintype.card P := by
        exact (Set.fintypeCard_eq_ncard
          (s := {w : List ℕ | w ∈ NonnestingDefs.avoiders n Λ ∧ primitive w n})).symm
      _ = Fintype.card (increasingWords (n - 1)) + 2 := hcard
      _ = 2 ^ (n - 2) + 2 := by
        rw [← Nat.card_eq_fintype_card,
          increasingWords_card (n - 1) (by omega)]
        simp only [Nat.sub_sub, Nat.reduceAdd]
  let C : PowerSeries ℤ := NonnestingDefs.gf Λ
  let D : PowerSeries ℤ := mk fun n =>
    if n = 0 then 0 else
      (({w : List ℕ | w ∈ NonnestingDefs.avoiders n Λ ∧ primitive w n}.ncard) : ℤ)
  have hprimitiveCount_one :
      ({w : List ℕ | w ∈ NonnestingDefs.avoiders 1 Λ ∧ primitive w 1}.ncard) = 1 := by
    have hset : {w : List ℕ | w ∈ NonnestingDefs.avoiders 1
        [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] ∧
        primitive w 1} = {([1, 1] : List ℕ)} := by
      ext w
      constructor
      · intro hw
        have hlen : w.length = 2 := by
          simpa using hw.1.1.length_eq
        obtain ⟨a, b, heq⟩ := List.length_eq_two.mp hlen
        have hvalue (x : ℕ) (hx : x ∈ w) : x = 1 := by
          have hbase := hw.1.1.mem_iff.mp hx
          simpa using hbase
        have ha := hvalue a (by rw [heq]; simp)
        have hb := hvalue b (by rw [heq]; simp)
        have heq : w = [1, 1] := by simp [heq, ha, hb]
        simpa [heq]
      · intro hw
        have heq : w = [1, 1] := by simpa using hw
        subst w
        have hno (σ : List ℕ) (hlen : σ.length = 4) :
            ¬ NonnestingDefs.Occurs σ [1, 1] := by
          intro hocc
          obtain ⟨x, _, _, hsub, _⟩ := hocc
          have hle := hsub.length_le
          simp [hlen] at hle
        have havoid : [1, 1] ∈ NonnestingDefs.avoiders 1
            [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] := by
          refine ⟨by simp, hno _ (by decide), hno _ (by decide), ?_⟩
          intro σ hσ
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
          rcases hσ with hσ | hσ | hσ | hσ <;>
            subst σ <;> exact hno _ (by decide)
        exact ⟨havoid, by intro k hk hkn; omega⟩
    rw [hset, Set.ncard_singleton]
  
  have hprimitiveCount_two :
      ({w : List ℕ | w ∈ NonnestingDefs.avoiders 2 Λ ∧ primitive w 2}.ncard) = 3 := by
    let Λ := [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]
    let S : Set (List ℕ) := {w | w ∈ NonnestingDefs.avoiders 2 Λ ∧ primitive w 2}
    have hno3 (w : List ℕ) (hp : w.Perm [1, 1, 2, 2])
        (σ : List ℕ) (hσ : NonnestingDefs.letters σ = 3) :
        ¬ NonnestingDefs.Occurs σ w := by
      intro hocc
      obtain ⟨x, hxmono, hxmem, _, _⟩ := hocc
      have h12 : x 1 < x 2 := by
        simpa using hxmono 1 (by omega) (by omega : 1 < NonnestingDefs.letters σ)
      have h23 : x 2 < x 3 := by
        simpa using hxmono 2 (by omega) (by omega : 2 < NonnestingDefs.letters σ)
      have h3 : x 3 ∈ w := hxmem 3 (by omega) (by omega : 3 ≤ NonnestingDefs.letters σ)
      have hxbase := hp.mem_iff.mp h3
      simp at hxbase
      have h1 : x 1 ∈ w := hxmem 1 (by omega) (by omega)
      have hxb1 := hp.mem_iff.mp h1
      simp at hxb1
      omega
    have hall (w : List ℕ) (hp : w.Perm [1, 1, 2, 2])
        (hnn : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] w ∧
          ¬ NonnestingDefs.Occurs [2, 1, 1, 2] w) :
        w ∈ NonnestingDefs.avoiders 2 Λ := by
      refine ⟨?_, hnn.1, hnn.2, ?_⟩
      · change w.Perm [1, 1, 2, 2]
        exact hp
      intro σ hσ
      simp only [Λ, List.mem_cons, List.not_mem_nil, or_false] at hσ
      rcases hσ with hσ | hσ | hσ | hσ <;>
        subst σ <;> exact hno3 w hp _ (by decide)
    have hprimitive (w : List ℕ) (hp : w.Perm [1, 1, 2, 2])
        (hne : w ≠ [1, 1, 2, 2]) : primitive w 2 := by
      intro k hk hkn hcut
      have hk1 : k = 1 := by omega
      subst k
      obtain ⟨u, v, heq, hulen, hu, hv⟩ := hcut
      have hule : ∀ x ∈ u, x = 1 := by
        intro x hx
        have := hu x hx
        omega
      have hvle : ∀ x ∈ v, x = 2 := by
        intro x hx
        have hxb := hp.mem_iff.mp (by rw [heq]; simp [hx] : x ∈ w)
        simp at hxb
        have := hv x hx
        omega
      have huword : u = [1, 1] := by
        obtain ⟨a, b, huword⟩ := List.length_eq_two.mp (by omega : u.length = 2)
        have ha := hule a (by rw [huword]; simp)
        have hb := hule b (by rw [huword]; simp)
        simp [huword, ha, hb]
      have hvlen : v.length = 2 := by
        have hlen := hp.length_eq
        rw [heq] at hlen
        simp at hlen
        omega
      obtain ⟨a, b, hvword⟩ := List.length_eq_two.mp hvlen
      have ha := hvle a (by rw [hvword]; simp)
      have hb := hvle b (by rw [hvword]; simp)
      exact hne (by simpa [huword, hvword, ha, hb] using heq)
    have hset : S = {([1, 2, 1, 2] : List ℕ), [2, 1, 2, 1], [2, 2, 1, 1]} := by
      ext w
      constructor
      · intro hw
        have hp : w.Perm [1, 1, 2, 2] := by
          have h := hw.1.1
          change w.Perm [1, 1, 2, 2] at h
          exact h
        have hcases : w = [1, 1, 2, 2] ∨ w = [1, 2, 1, 2] ∨
            w = [1, 2, 2, 1] ∨ w = [2, 1, 1, 2] ∨
            w = [2, 1, 2, 1] ∨ w = [2, 2, 1, 1] := by
          have hlen : w.length = 4 := by simpa using hp.length_eq
          obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp hlen
          have hval (x : ℕ) (hx : x ∈ [a, b, c, d]) : x = 1 ∨ x = 2 := by
            have hx' := hp.mem_iff.mp hx
            simpa using hx'
          have ha := hval a (by simp)
          have hb := hval b (by simp)
          have hc := hval c (by simp)
          have hd := hval d (by simp)
          have hcount := hp.count_eq 1
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
            rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
            simp_all [List.count]
        rcases hcases with h | h | h | h | h | h
        · subst w
          exact False.elim (hw.2 1 (by omega) (by omega)
            ⟨[1, 1], [2, 2], rfl, rfl, by simp, by simp⟩)
        · simp [h]
        · subst w
          exfalso
          apply hw.1.2.1
          refine ⟨fun i => i, ?_, ?_, ?_, by simp⟩
          · intro i hi hlt
            change i < i + 1
            omega
          · intro i hi hle
            have hcase : i = 1 ∨ i = 2 := by
              simp [NonnestingDefs.letters] at hle
              omega
            rcases hcase with rfl | rfl <;> simp
          · simp [NonnestingDefs.letters]
        · subst w
          exfalso
          apply hw.1.2.2.1
          refine ⟨fun i => i, ?_, ?_, ?_, by simp⟩
          · intro i hi hlt
            change i < i + 1
            omega
          · intro i hi hle
            have hcase : i = 1 ∨ i = 2 := by
              simp [NonnestingDefs.letters] at hle
              omega
            rcases hcase with rfl | rfl <;> simp
          · simp [NonnestingDefs.letters]
        · simp [h]
        · simp [h]
      · intro hw
        have hmember (v : List ℕ) (hp : v.Perm [1, 1, 2, 2])
            (hcount : ∀ x ∈ v, v.count x = 2)
            (hsame : ∀ a ∈ v, ∀ b ∈ v,
              (v).idxOf a < (v).idxOf b → secondPos a v < secondPos b v)
            (hne : v ≠ [1, 1, 2, 2]) : v ∈ S := by
          exact ⟨hall v hp ((nonnesting_iff_equal_orders v hcount).mpr hsame),
            hprimitive v hp hne⟩
        have hcases : w = [1, 2, 1, 2] ∨ w = [2, 1, 2, 1] ∨
            w = [2, 2, 1, 1] := by simpa using hw
        rcases hcases with h | h | h <;> subst w <;>
          apply hmember <;> decide
    have hncard : S.ncard = 3 := by
      rw [hset]
      norm_num
    exact hncard
  have hΛ : ∀ σ ∈ Λ, sumIndecomposable σ ∧
      (∀ a ∈ σ, 1 ≤ a) ∧
      (∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → i ∈ σ) := by
    intro σ hσ
    simp only [Λ, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with hσ | hσ | hσ | hσ <;> subst σ
    all_goals
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        fin_cases k
        · simp at hk
        all_goals decide
      · intro a ha
        simp at ha
        omega
      · intro i hi hle
        have hcase : i = 1 ∨ i = 2 ∨ i = 3 := by
          simp [NonnestingDefs.letters] at hle
          omega
        rcases hcase with rfl | rfl | rfl <;> simp
  have hC0 : coeff 0 C = 1 := by
    simp only [C, NonnestingDefs.gf, coeff_mk]
    rw [classCount_zero Λ (by intro σ hσ; simp [Λ] at hσ; aesop)]
    norm_num
  have hCD : C * D = C - 1 := by
    apply PowerSeries.ext
    intro n
    by_cases hn : n = 0
    · subst n
      rw [coeff_zero_eq_constantCoeff_apply] at hC0
      simp [coeff_mul, D, hC0]
    have hnpos : 0 < n := by omega
    have hconv := classCount_convolution Λ n hΛ hnpos
    have hsum : (∑ j ∈ Finset.range (n + 1),
          (if j = 0 then (0 : ℤ) else
            (({w : List ℕ | w ∈ NonnestingDefs.avoiders j Λ ∧ primitive w j}.ncard) : ℤ)) *
            ((NonnestingDefs.avoiders (n - j) Λ).ncard : ℤ)) =
        ∑ j ∈ Finset.Icc 1 n,
          (({w : List ℕ | w ∈ NonnestingDefs.avoiders j Λ ∧ primitive w j}.ncard) : ℤ) *
            ((NonnestingDefs.avoiders (n - j) Λ).ncard : ℤ) := by
      rw [Nat.range_succ_eq_Icc_zero]
      rw [← Finset.insert_Icc_succ_left_eq_Icc (by omega : 0 ≤ n)]
      rw [Finset.sum_insert (by simp)]
      simp only [↓reduceIte, zero_mul, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      have hj1 : 1 ≤ j := by simpa using (Finset.mem_Icc.mp hj).1
      simp only [if_neg (show j ≠ 0 by omega)]
    have hconvZ : ((NonnestingDefs.avoiders n Λ).ncard : ℤ) =
        ∑ j ∈ Finset.Icc 1 n,
          (({w : List ℕ | w ∈ NonnestingDefs.avoiders j Λ ∧ primitive w j}.ncard) : ℤ) *
            ((NonnestingDefs.avoiders (n - j) Λ).ncard : ℤ) := by
      exact_mod_cast hconv
    rw [mul_comm C D, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [map_sub, coeff_one]
    simp only [D, C, NonnestingDefs.gf, coeff_mk]
    change (∑ j ∈ Finset.range (n + 1),
        (if j = 0 then (0 : ℤ) else
          (({w : List ℕ | w ∈ NonnestingDefs.avoiders j Λ ∧ primitive w j}.ncard) : ℤ)) *
          ((NonnestingDefs.avoiders (n - j) Λ).ncard : ℤ)) =
      ((NonnestingDefs.avoiders n Λ).ncard : ℤ) - (if n = 0 then 1 else 0)
    rw [hsum, ← hconvZ]
    simp [hn]
  have hD : D * (1 - 3 * X + 2 * X ^ 2) = X - 3 * X ^ 3 := by
    apply PowerSeries.ext
    intro n
    have hrewrite : D * (1 - 3 * X + 2 * X ^ 2) =
        D - ((D * X) + (D * X) + (D * X)) +
          ((D * X ^ 2) + (D * X ^ 2)) := by ring
    rw [hrewrite]
    have hrhs : (X : PowerSeries ℤ) - 3 * X ^ 3 =
        X - (X ^ 3 + X ^ 3 + X ^ 3) := by ring
    rw [hrhs]
    have hcoeffX : coeff n (D * X) =
        if 1 ≤ n then coeff (n - 1) D else 0 := by
      simpa only [pow_one] using coeff_mul_X_pow' D 1 n
    simp only [map_add, map_sub, coeff_mul_X_pow',
      coeff_X, coeff_X_pow]
    rw [hcoeffX]
    simp only [D, coeff_mk]
    by_cases hsmalln : n < 5
    · have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
      rcases hcases with h | h | h | h | h <;> subst n <;>
        norm_num [Λ, hprimitiveCount_one, hprimitiveCount_two,
          primitiveCount_large 3 (by decide), primitiveCount_large 4 (by decide)]
    have hn5 : 5 ≤ n := by omega
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hn3 : n ≠ 3 := by omega
    have hnsub1 : n - 1 ≠ 0 := by omega
    have hnsub2 : n - 2 ≠ 0 := by omega
    have hge1 : 1 ≤ n := by omega
    have hge2 : 2 ≤ n := by omega
    simp only [if_neg hn0, if_neg hn1, if_neg hn3,
      if_neg hnsub1, if_neg hnsub2, if_pos hge1, if_pos hge2]
    rw [primitiveCount_large n (by omega),
      primitiveCount_large (n - 1) (by omega),
      primitiveCount_large (n - 2) (by omega)]
    have hp1 : 2 ^ (n - 2) = 4 * 2 ^ (n - 4) := by
      have heq : n - 2 = (n - 4) + 2 := by omega
      rw [heq, pow_add]
      ring
    have hp2 : 2 ^ (n - 3) = 2 * 2 ^ (n - 4) := by
      have heq : n - 3 = (n - 4) + 1 := by omega
      rw [heq, pow_add]
      ring
    simp only [Nat.sub_sub, Nat.reduceAdd] at ⊢
    rw [hp1, hp2]
    push_cast
    ring
  have halgebra : (1 - D) * (1 - 3 * X + 2 * X ^ 2) =
      (1 - 3 * X) * (1 - X - X ^ 2) := by
    rw [sub_mul, one_mul, hD]
    ring
  have hfinal : C * ((1 - 3 * X) * (1 - X - X ^ 2)) =
      1 - 3 * X + 2 * X ^ 2 := by
    calc
      C * ((1 - 3 * X) * (1 - X - X ^ 2)) =
          (C * (1 - D)) * (1 - 3 * X + 2 * X ^ 2) := by
            rw [← halgebra]
            ring
      _ = 1 - 3 * X + 2 * X ^ 2 := by rw [mul_sub, mul_one, hCD]; ring
  simpa only [NonnestingDefs.claimFour, C, Λ] using hfinal

end D5.S3.Combinatorics.Nonnesting.NonnestingFour

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFour.result
