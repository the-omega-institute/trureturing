/- GID: D5/S3/Arith/FibonacciAtomic/FirstRejectionProfileMass
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FirstRejectionProfileMass
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual uniform cut-profile masses equal the chronological two-state operators. -/

import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import D5.S3.ConceptDynamics.PartialIdentification.FiniteIndependentSourceGrouping
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.FirstRejectionProfileMass

open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.FiniteIndependentSourceGrouping
open D5.S3.ConceptDynamics.PartialIdentification.CanonicalResponseSignature
open scoped BigOperators

noncomputable instance profileFintype (k : ℕ) (A : Finset (Fin (k + 1))) :
    Fintype (Profile k A) := by
  classical
  unfold Profile
  infer_instance

noncomputable def profileLaw (k : ℕ) (A : Finset (Fin (k + 1))) : FiniteResponseLaw (Side k A) := by
  classical
  let windowLaw : FiniteResponseLaw Window :=
    { mass := fun _ => 1 / 5
      nonnegative := by intro _; norm_num
      total := by
        have hc : Fintype.card Window = 5 := by decide
        simp [hc] }
  exact independentSourceLaw (fun _ : {r // r ∈ A} => windowLaw)

noncomputable def profileMass {k : ℕ} {A : Finset (Fin (k + 1))}
    (P : Profile k A) : ℚ := by
  classical
  exact pushforwardSignatureMass (profileLaw k A).mass (code A) (encode P)

noncomputable def filterWindow {k : ℕ} {A : Finset (Fin (k + 1))}
    (P : Profile k A) (i : Fin (k + 1)) (x : Window) : Bool :=
  by classical exact decide (∀ j : Fin k, (left j : Label k) < P.1.val →
    Cross A j →
      (left j = i → last x = (encode P).2 j) ∧
      (right j = i → first x = (encode P).2 j)) &&
    (if i = Fin.last k then
      (if P.1.val = (Fin.last k : Label k) then x = .zero
       else if P.1.val = ⊤ then x ≠ .zero else True)
     else True)

noncomputable def internalFactor {k : ℕ} {A : Finset (Fin (k + 1))}
    (P : Profile k A) (j : Fin k) (r u : Bool) : ℚ :=
  by classical exact if Internal A j ∧ (left j : Label k) < P.1.val then
    if r && u then 0 else 1
  else if Internal A j ∧ (left j : Label k) = P.1.val then
    if r && u then 1 else 0
  else 1

noncomputable def seamFactor {k : ℕ} {A : Finset (Fin (k + 1))}
    (P : Profile k A) (i : Fin (k + 1)) (r u : Bool) : ℚ :=
  if h : 0 < i.val then internalFactor P ⟨i.val - 1, by omega⟩ r u else 1

noncomputable def profileMatrix {k : ℕ} {A : Finset (Fin (k + 1))}
    (P : Profile k A) (i : Fin (k + 1)) : Matrix Bool Bool ℚ := fun r v =>
  if i ∈ A then
    (∑ x : Window,
      (if last x = v then (1 : ℚ) else 0) *
        (if filterWindow P i x then (1 : ℚ) else 0) *
        seamFactor P i r (first x)) / 5
  else if v = false then 1 else 0

noncomputable def profileMatrixProduct {k : ℕ} {A : Finset (Fin (k + 1))}
    (P : Profile k A) : Matrix Bool Bool ℚ :=
  (List.ofFn (profileMatrix P)).prod

noncomputable def profileOperatorMass {k : ℕ} {A : Finset (Fin (k + 1))}
    (P : Profile k A) : ℚ :=
  ∑ v : Bool, profileMatrixProduct P false v

set_option maxHeartbeats 4000000 in
/-- Actual profile fibers and their exact chronological two-state evaluation. -/
theorem result (k : ℕ) (A : Finset (Fin (k + 1))) :
    (∀ a : Side k A, (profileLaw k A).mass a = (5 ^ A.card : ℚ)⁻¹) ∧
    (∀ P : Profile k A, ∀ a : Side k A, code A a = encode P ↔
      (∀ i : {i // i ∈ A}, filterWindow P i (a i) = true) ∧
      (∀ j : Fin k, internalFactor P j (last (extend A a (left j)))
        (first (extend A a (right j))) = 1)) ∧
    (∀ P : Profile k A, profileMass P = profileOperatorMass P ∧ 0 < profileMass P) ∧
    (∑ P : Profile k A, profileMass P = 1) := by
  classical
  have weight (a : Side k A) : (profileLaw k A).mass a = (5 ^ A.card : ℚ)⁻¹ := by
    simp [profileLaw, independentSourceLaw, one_div, ← inv_pow]
  have mean (f : Side k A → ℚ) :
      Finset.expect Finset.univ f = ∑ a, (profileLaw k A).mass a * f a := by
    have hc : Fintype.card (Side k A) = 5 ^ A.card := by
      have hw : Fintype.card Window = 5 := by decide
      simp [Side, hw]
    rw [Fintype.expect_eq_sum_div_card, hc]
    simp_rw [weight]
    rw [← Finset.mul_sum]
    simp only [Nat.cast_pow, Nat.cast_ofNat, inv_pow]
    ring
  have mass_mean (P : Profile k A) : profileMass P =
      Finset.expect Finset.univ (fun a : Side k A => if code A a = encode P then (1 : ℚ) else 0) := by
    rw [mean]
    unfold profileMass pushforwardSignatureMass
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have event (P : Profile k A) : ∀ a : Side k A, code A a = encode P ↔
      (∀ i : {i // i ∈ A}, filterWindow P i (a i) = true) ∧
      (∀ j : Fin k, internalFactor P j (last (extend A a (left j)))
        (first (extend A a (right j))) = 1) := by
    classical
    have spec (w : Word k) (j : Fin (k + 1)) :
        task w ≤ (j : Label k) ↔ ∃ i, bad w i ∧ i ≤ j := by
      simp only [task, Finset.inf_le_iff (WithTop.coe_lt_top j), Finset.mem_univ, true_and]
      apply exists_congr
      intro i
      by_cases h : bad w i <;> simp [h]
    have cut (w : Word k) (t : Label k) : task w = t ↔
        (∀ j : Fin (k + 1), (j : Label k) < t → ¬ bad w j) ∧
        (∀ j : Fin (k + 1), t = (j : Label k) → bad w j) := by
      constructor
      · intro ht
        constructor
        · intro j hj hb
          have hle := (spec w j).mpr ⟨j, hb, le_rfl⟩
          rw [ht] at hle
          exact (not_le_of_gt hj) hle
        · intro j hj
          obtain ⟨i, hi, hij⟩ := (spec w j).mp (by rw [ht, hj])
          have hji : j ≤ i := by
            have hle := (spec w i).mpr ⟨i, hi, le_rfl⟩
            rw [ht, hj] at hle
            exact WithTop.coe_le_coe.mp hle
          simpa [le_antisymm hij hji] using hi
      · rintro ⟨hn, hh⟩
        apply le_antisymm
        · cases ht : t with
          | none => exact le_top
          | some j => exact (spec w j).mpr ⟨j, hh j ht, le_rfl⟩
        · unfold task
          apply Finset.le_inf_iff.mpr
          intro j _
          by_cases hb : bad w j
          · simp only [if_pos hb]
            exact le_of_not_gt (fun h => hn j h hb)
          · simp [hb]
    intro a
    let w := extend A a
    have bi (j : Fin k) : bad w (left j) ↔ Internal A j ∧
        last (w (left j)) = true ∧ first (w (right j)) = true := by
      simp only [bad, show (left j).val < k from j.isLt, ↓reduceDIte]
      change last (w (left j)) = true ∧ first (w (right j)) = true ↔ _
      unfold Internal
      by_cases hl : left j ∈ A <;> by_cases hr : right j ∈ A <;>
        simp [w, extend, hl, hr, last, first]
    have bt : bad w (Fin.last k) ↔ w (Fin.last k) = .zero := by simp [bad]
    have fields : code A a = encode P ↔ closed A a = P.1.val ∧
        ∀ j, Cross A j → (left j : Label k) < P.1.val → port A a j = (encode P).2 j := by
      constructor
      · intro h
        refine ⟨congrArg Prod.fst h, ?_⟩
        intro j hc hj
        have hb := congrFun (congrArg Prod.snd h) j
        simpa [code, show closed A a = P.1.val from congrArg Prod.fst h, hc, hj] using hb
      · rintro ⟨ht, hp⟩
        apply Prod.ext ht
        funext j
        by_cases hc : Cross A j ∧ (left j : Label k) < P.1.val
        · simpa [code, ht, hc] using hp j hc.1 hc.2
        · have hn : ¬ Active A P.1.val j := fun h => hc ⟨h.1, h.2.1⟩
          simp [code, ht, hc, encode, hn]
    have closed_filters : closed A a = P.1.val ↔
        (∀ j : Fin k, internalFactor P j (last (w (left j))) (first (w (right j))) = 1) ∧
        (if P.1.val = (Fin.last k : Label k) then w (Fin.last k) = .zero
         else if P.1.val = ⊤ then w (Fin.last k) ≠ .zero else True) := by
      have fi (j : Fin k) : internalFactor P j (last (w (left j))) (first (w (right j))) = 1 ↔
          ((left j : Label k) < P.1.val → ¬ bad w (left j)) ∧
          (P.1.val = (left j : Label k) → bad w (left j)) := by
        have allowed := P.1.property
        have hal : P.1.val = (left j : Label k) → Internal A j := by
          intro he
          rcases allowed with h | ⟨i, hi, he'⟩ | ⟨ha, he'⟩
          · exact (WithTop.coe_ne_top (he.symm.trans h)).elim
          · have hij : i = j := by
              apply Fin.ext
              have hx := WithTop.coe_inj.mp (he.symm.trans he')
              exact (congrArg Fin.val hx).symm
            simpa [hij] using hi
          · have hx := WithTop.coe_inj.mp (he.symm.trans he')
            have hv := congrArg Fin.val hx
            simp only [left, Fin.val_castSucc, Fin.val_last] at hv
            omega
        rw [bi]
        unfold internalFactor
        by_cases hi : Internal A j <;> by_cases hl : (left j : Label k) < P.1.val <;>
          by_cases he : (left j : Label k) = P.1.val <;>
          cases last (w (left j)) <;> cases first (w (right j)) <;>
          simp_all
        all_goals exact Ne.symm he
      rw [closed, cut]
      constructor
      · rintro ⟨hn, hh⟩
        refine ⟨fun j => (fi j).mpr ⟨hn (left j), hh (left j)⟩, ?_⟩
        split_ifs with ht htop
        · exact bt.mp (hh _ ht)
        · exact fun hz => hn _ (by rw [htop]; exact WithTop.coe_lt_top _) (bt.mpr hz)
      · rintro ⟨hf, ht⟩
        have hf' := fun j => (fi j).mp (hf j)
        constructor
        · intro j hj
          by_cases hk : j.val < k
          · let l : Fin k := ⟨j.val, hk⟩
            have he : left l = j := rfl
            exact fun hb => (hf' l).1 (by simpa [he] using hj) (by simpa [he] using hb)
          · have he : j = Fin.last k := Fin.ext (by simp; omega)
            subst j
            rcases P.1.property with htop | ⟨l, hl, he⟩ | ⟨ha, he⟩
            · simp only [htop, WithTop.top_ne_coe, ↓reduceIte, eq_self_iff_true] at ht
              exact fun hb => ht (bt.mp hb)
            · rw [he] at hj
              have hv := WithTop.coe_lt_coe.mp hj
              simp only [left, Fin.lt_def, Fin.val_last, Fin.val_castSucc] at hv
              omega
            · simpa [he] using hj
        · intro j hj
          by_cases hk : j.val < k
          · let l : Fin k := ⟨j.val, hk⟩
            have he : left l = j := rfl
            simpa [he] using (hf' l).2 (by simpa [he] using hj)
          · have he : j = Fin.last k := Fin.ext (by simp; omega)
            subst j
            exact bt.mpr (by simpa [hj] using ht)
    have windows : (∀ i : {i // i ∈ A}, filterWindow P i (a i) = true) ↔
        (∀ j, Cross A j → (left j : Label k) < P.1.val → port A a j = (encode P).2 j) ∧
        (if P.1.val = (Fin.last k : Label k) then w (Fin.last k) = .zero
         else if P.1.val = ⊤ then w (Fin.last k) ≠ .zero else True) := by
      have fw (i : {i // i ∈ A}) : filterWindow P i (a i) = true ↔
          (∀ j : Fin k, (left j : Label k) < P.1.val → Cross A j →
            (left j = i.val → last (a i) = (encode P).2 j) ∧
            (right j = i.val → first (a i) = (encode P).2 j)) ∧
          (if i.val = Fin.last k then
            (if P.1.val = (Fin.last k : Label k) then a i = .zero
             else if P.1.val = ⊤ then a i ≠ .zero else True) else True) := by
        by_cases hi : i.val = Fin.last k <;>
          by_cases ht : P.1.val = (Fin.last k : Label k) <;>
          by_cases htop : P.1.val = ⊤ <;> simp [filterWindow, hi, ht, htop]
      constructor
      · intro hf
        constructor
        · intro j hc hj
          rcases hc with ⟨hl, hr⟩ | ⟨hl, hr⟩
          · have h := ((fw ⟨left j, hl⟩).mp (hf ⟨left j, hl⟩)).1 j hj (Or.inl ⟨hl, hr⟩)
            simpa [port, w, extend, hl] using h.1 rfl
          · have h := ((fw ⟨right j, hr⟩).mp (hf ⟨right j, hr⟩)).1 j hj (Or.inr ⟨hl, hr⟩)
            simpa [port, w, extend, hl, hr] using h.2 rfl
        · by_cases ha : Fin.last k ∈ A
          · simpa [w, extend, ha] using ((fw ⟨Fin.last k, ha⟩).mp (hf ⟨Fin.last k, ha⟩)).2
          · have hn : P.1.val ≠ (Fin.last k : Label k) := by
              intro ht
              rcases P.1.property with h | ⟨j, hj, he⟩ | ⟨h, he⟩
              · exact (WithTop.coe_ne_top (ht.symm.trans h)).elim
              · have hv := congrArg Fin.val (WithTop.coe_inj.mp (ht.symm.trans he))
                simp only [Fin.val_last, left, Fin.val_castSucc] at hv
                omega
              · exact ha h
            simp [hn, w, extend, ha]
      · rintro ⟨hp, ht⟩ i
        apply (fw i).mpr
        constructor
        · intro j hj hc
          have hb := hp j hc hj
          constructor
          · intro hl
            have ha : left j ∈ A := hl.symm ▸ i.property
            simpa [port, w, extend, ha, hl] using hb
          · intro hr
            have ha : right j ∈ A := hr.symm ▸ i.property
            have hn : left j ∉ A := by rcases hc with h|h <;> aesop
            simpa [port, w, extend, hn, ha, hr] using hb
        · by_cases he : i.val = Fin.last k
          · have ha : Fin.last k ∈ A := he ▸ i.property
            have hw : w (Fin.last k) = a i := by simp [w, extend, ha, ← he]
            rw [if_pos he]
            simpa only [hw] using ht
          · simp [he]
    rw [fields, closed_filters, windows]
    change _ ↔ _ ∧ ∀ j, internalFactor P j (last (w (left j))) (first (w (right j))) = 1
    tauto
  have bridge (P : Profile k A) : profileMass P = profileOperatorMass P := by
    classical
    letI : Nonempty Window := ⟨.zero⟩
    let e (m : ℕ) (hm : m ≤ k + 1) (j : Fin m) : Fin (k + 1) := ⟨j.val, by omega⟩
    let prev (m : ℕ) (hm : m ≤ k + 1) (w : Fin m → Window) (j : Fin m) : Bool :=
      if h : 0 < j.val then
        if (⟨j.val - 1, by omega⟩ : Fin (k + 1)) ∈ A then last (w ⟨j.val - 1, by omega⟩) else false
      else false
    let q (m : ℕ) (hm : m ≤ k + 1) (w : Fin m → Window) : Bool :=
      if h : 0 < m then
        if (⟨m - 1, by omega⟩ : Fin (k + 1)) ∈ A then last (w ⟨m - 1, by omega⟩) else false
      else false
    let gamma (i : Fin (k + 1)) (r : Bool) (x : Window) : ℚ :=
      if i ∈ A then (if filterWindow P i x then 1 else 0) * seamFactor P i r (first x) else 1
    let G (m : ℕ) (hm : m ≤ k + 1) (w : Fin m → Window) : ℚ :=
      ∏ j : Fin m, gamma (e m hm j) (prev m hm w j) (w j)
    let rho (m : ℕ) (hm : m ≤ k + 1) (v : Bool) : ℚ :=
      Finset.expect Finset.univ (fun w => G m hm w * if q m hm w = v then 1 else 0)
    have oldprev (m : ℕ) (hm : m + 1 ≤ k + 1) (w : Fin m → Window) (x : Window) (j : Fin m) :
        prev (m + 1) hm (Fin.snoc w x) j.castSucc = prev m (by omega) w j := by
      dsimp [prev]
      split_ifs with h ha
      · have he : (⟨j.val - 1, by omega⟩ : Fin (m + 1)) =
            (⟨j.val - 1, by omega⟩ : Fin m).castSucc := rfl
        rw [he, Fin.snoc_castSucc]
      · rfl
      · rfl
    have newprev (m : ℕ) (hm : m + 1 ≤ k + 1) (w : Fin m → Window) (x : Window) :
        prev (m + 1) hm (Fin.snoc w x) (Fin.last m) = q m (by omega) w := by
      dsimp [prev, q]
      split_ifs with h ha
      · have he : (⟨m - 1, by omega⟩ : Fin (m + 1)) = (⟨m - 1, by omega⟩ : Fin m).castSucc := rfl
        rw [he, Fin.snoc_castSucc]
      · rfl
      · rfl
    have snocG (m : ℕ) (hm : m + 1 ≤ k + 1) (w : Fin m → Window) (x : Window) :
        G (m + 1) hm (Fin.snoc w x) =
          G m (by omega) w * gamma ⟨m, by omega⟩ (q m (by omega) w) x := by
      dsimp only [G]
      rw [Fin.prod_univ_castSucc]
      simp only [oldprev, newprev, Fin.snoc_castSucc, Fin.snoc_last]
      rfl
    have snocq (m : ℕ) (hm : m + 1 ≤ k + 1) (w : Fin m → Window) (x : Window) :
        q (m + 1) hm (Fin.snoc w x) =
          if (⟨m, by omega⟩ : Fin (k + 1)) ∈ A then last x else false := by
      have he : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
      dsimp only [q]
      simp only [show 0 < m + 1 by omega, dif_pos, Nat.add_sub_cancel, he, Fin.snoc_last]
    have step (m : ℕ) (hm : m + 1 ≤ k + 1) (v : Bool) :
        rho (m + 1) hm v = ∑ r : Bool, rho m (by omega) r * profileMatrix P ⟨m, by omega⟩ r v := by
      have inner (w : Fin m → Window) :
          Finset.expect Finset.univ (fun x => G (m + 1) hm (Fin.snoc w x) *
              if q (m + 1) hm (Fin.snoc w x) = v then 1 else 0) =
            G m (by omega) w * profileMatrix P ⟨m, by omega⟩ (q m (by omega) w) v := by
        simp only [snocG, snocq]
        by_cases ha : (⟨m, by omega⟩ : Fin (k + 1)) ∈ A
        · simp only [ha, ↓reduceIte]
          rw [Fintype.expect_eq_sum_div_card]
          have hc : Fintype.card Window = 5 := by decide
          simp only [hc, Nat.cast_ofNat, profileMatrix, ha, ↓reduceIte, gamma]
          rw [← mul_div_assoc, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          ring
        · simp only [gamma, ha, ↓reduceIte, mul_one, profileMatrix]
          rw [Fintype.expect_const]
          congr 1
          cases v <;> rfl
      have snoc_mean (f : (Fin (m + 1) → Window) → ℚ) :
          Finset.expect Finset.univ f = Finset.expect Finset.univ
            (fun w : Fin m → Window => Finset.expect Finset.univ (fun x : Window => f (Fin.snoc w x))) := by
        calc
          _ = Finset.expect Finset.univ
              (fun z : Window × (Fin m → Window) => f (Fin.snoc z.2 z.1)) :=
            (Fintype.expect_equiv (Fin.snocEquiv (fun _ => Window)) _ _ (fun _ => rfl)).symm
          _ = Finset.expect Finset.univ (fun x : Window => Finset.expect Finset.univ
              (fun w : Fin m → Window => f (Fin.snoc w x))) := by
            simpa only [Finset.univ_product_univ] using Finset.expect_product
              (Finset.univ : Finset Window) (Finset.univ : Finset (Fin m → Window))
              (fun z => f (Fin.snoc z.2 z.1))
          _ = _ := Finset.expect_comm _ _ _
      dsimp only [rho]
      rw [snoc_mean]
      simp only [inner]
      have partition (w : Fin m → Window) :
          G m (by omega) w * profileMatrix P ⟨m, by omega⟩ (q m (by omega) w) v =
            ∑ r : Bool, (G m (by omega) w * if q m (by omega) w = r then 1 else 0) *
              profileMatrix P ⟨m, by omega⟩ r v := by
        rw [Finset.sum_eq_single (q m (by omega) w)]
        · simp
        · intro r _ hr
          simp [Ne.symm hr]
        · simp
      simp_rw [partition]
      rw [Finset.expect_sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      change Finset.expect Finset.univ (fun w => (G m (by omega) w * if q m (by omega) w = r then 1 else 0) *
        profileMatrix P ⟨m, by omega⟩ r v) = _
      rw [show (fun w : Fin m → Window =>
          (G m (by omega) w * if q m (by omega) w = r then 1 else 0) *
            profileMatrix P ⟨m, by omega⟩ r v) =
        (fun w : Fin m → Window => profileMatrix P ⟨m, by omega⟩ r v *
            (G m (by omega) w * if q m (by omega) w = r then 1 else 0)) by
              funext w; ring]
      rw [← Finset.mul_expect]
      ring
    have invariant (m : ℕ) (hm : m ≤ k + 1) (v : Bool) :
        rho m hm v = Fin.partialProd (profileMatrix P) ⟨m, by omega⟩ false v := by
      induction m generalizing v with
      | zero =>
        dsimp only [rho]
        have hu : (Finset.univ : Finset (Fin 0 → Window)) = {Fin.elim0} := by
          ext w
          simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
          exact Subsingleton.elim _ _
        rw [hu, Finset.expect_singleton]
        simp [G, q, Fin.partialProd_zero, Matrix.one_apply]
      | succ m ih =>
        rw [step m hm]
        have he : (⟨m + 1, by omega⟩ : Fin (k + 2)) = (⟨m, by omega⟩ : Fin (k + 1)).succ := rfl
        rw [he, Fin.partialProd_succ, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro r _
        exact congrArg (fun z : ℚ => z * profileMatrix P ⟨m, by omega⟩ r v) (ih (by omega) r)
    let restriction (m : ℕ) (hm : m ≤ k + 1) (w : Fin m → Window) :
        {j : Fin m // e m hm j ∈ A} → Window := fun j => w j.val
    let fill (m : ℕ) (hm : m ≤ k + 1) (a : {j : Fin m // e m hm j ∈ A} → Window) :
        Fin m → Window := fun j => if h : e m hm j ∈ A then a ⟨j, h⟩ else .middle
    have maskq (m : ℕ) (hm : m ≤ k + 1) (w : Fin m → Window) :
        q m hm (fill m hm (restriction m hm w)) = q m hm w := by
      dsimp only [q]
      split_ifs with h ha
      · simp [fill, restriction, e, ha]
      · rfl
      · rfl
    have maskprev (m : ℕ) (hm : m ≤ k + 1) (w : Fin m → Window) (j : Fin m) :
        prev m hm (fill m hm (restriction m hm w)) j = prev m hm w j := by
      dsimp only [prev]
      split_ifs with h ha
      · simp [fill, restriction, e, ha]
      · rfl
      · rfl
    have maskG (m : ℕ) (hm : m ≤ k + 1) (w : Fin m → Window) :
        G m hm (fill m hm (restriction m hm w)) = G m hm w := by
      dsimp only [G]
      apply Finset.prod_congr rfl
      intro j _
      rw [maskprev m hm w j]
      by_cases hj : e m hm j ∈ A
      · simp [fill, restriction, hj]
      · simp [gamma, hj]
    have marginal (m : ℕ) (C : Fin m → Prop) [DecidablePred C]
        (f : ({i // C i} → Window) → ℚ) :
        Finset.expect Finset.univ (fun w : Fin m → Window => f (fun i => w i.val)) =
        Finset.expect Finset.univ f := by
      classical
      let E := Equiv.piEquivPiSubtypeProd C (fun _ => Window)
      calc
        _ = Finset.expect Finset.univ
            (fun z : ({i // C i} → Window) × ({i // ¬ C i} → Window) => f z.1) :=
          Fintype.expect_equiv E _ _ (fun _ => rfl)
        _ = Finset.expect Finset.univ (fun a : {i // C i} → Window =>
            Finset.expect Finset.univ (fun _b : {i // ¬ C i} → Window => f a)) := by
          simpa only [Finset.univ_product_univ] using Finset.expect_product
            (Finset.univ : Finset ({i // C i} → Window))
            (Finset.univ : Finset ({i // ¬ C i} → Window)) (fun z => f z.1)
        _ = _ := by simp only [Fintype.expect_const]
    have semantic (m : ℕ) (hm : m ≤ k + 1) (v : Bool) :
        rho m hm v = Finset.expect Finset.univ
          (fun a => G m hm (fill m hm a) * if q m hm (fill m hm a) = v then 1 else 0) := by
      calc
        rho m hm v = Finset.expect Finset.univ
            (fun w => G m hm (fill m hm (restriction m hm w)) *
              if q m hm (fill m hm (restriction m hm w)) = v then 1 else 0) := by
          apply Finset.expect_congr rfl
          intro w _
          rw [maskG m hm w, maskq m hm w]
        _ = _ := by
          simpa only [restriction] using marginal m (fun j => e m hm j ∈ A)
            (fun a => G m hm (fill m hm a) * if q m hm (fill m hm a) = v then 1 else 0)
    have binary (i : Fin (k + 1)) (r : Bool) (x : Window) :
        gamma i r x = 0 ∨ gamma i r x = 1 := by
      dsimp [gamma, seamFactor, internalFactor]
      split_ifs <;> simp
    have product_indicator (m : ℕ) (hm : m ≤ k + 1) (w : Fin m → Window) :
        G m hm w = if ∀ j : Fin m, gamma (e m hm j) (prev m hm w j) (w j) = 1 then 1 else 0 := by
      have aux (s : Finset (Fin m)) :
          (∏ j ∈ s, gamma (e m hm j) (prev m hm w j) (w j)) =
            if ∀ j ∈ s, gamma (e m hm j) (prev m hm w j) (w j) = 1 then 1 else 0 := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert j s hj ih =>
          by_cases hg : gamma (e m hm j) (prev m hm w j) (w j) = 1
          · simp [Finset.prod_insert, hj, hg, ih]
          · have hz := (binary (e m hm j) (prev m hm w j) (w j)).resolve_right hg
            simp [Finset.prod_insert, hj, hz, hg]
      simpa [G] using aux Finset.univ
    have prefix_event (m : ℕ) (hm : m ≤ k + 1) (v : Bool) :
        rho m hm v = Finset.expect Finset.univ
          (fun a : {j : Fin m // e m hm j ∈ A} → Window => if (∀ j : Fin m,
            gamma (e m hm j) (prev m hm (fill m hm a) j) (fill m hm a j) = 1) ∧
            q m hm (fill m hm a) = v then (1 : ℚ) else 0) := by
      rw [semantic m hm v]
      apply Finset.expect_congr rfl
      intro a _
      rw [product_indicator m hm (fill m hm a)]
      by_cases hg : ∀ j : Fin m,
          gamma (e m hm j) (prev m hm (fill m hm a) j) (fill m hm a j) = 1 <;>
        by_cases hq : q m hm (fill m hm a) = v <;> simp [hg, hq]
    have prev_extend (a : Side k A) (i : Fin (k + 1)) :
        prev (k + 1) (by omega) (extend A a) i =
          if h : 0 < i.val then last (extend A a ⟨i.val - 1, by omega⟩) else false := by
      dsimp only [prev]
      split_ifs with h ha
      · rfl
      · simp [extend, ha, last]
      · rfl
    have gamma_one (a : Side k A) (i : Fin (k + 1)) :
        gamma i (prev (k + 1) (by omega) (extend A a) i) (extend A a i) = 1 ↔
          (i ∈ A → filterWindow P i (extend A a i) = true ∧
            seamFactor P i (prev (k + 1) (by omega) (extend A a) i)
              (first (extend A a i)) = 1) := by
      by_cases ha : i ∈ A <;> by_cases hf : filterWindow P i (extend A a i) = true <;>
        simp [gamma, ha, hf]
    have final_filters (a : Side k A) :
        (∀ i : Fin (k + 1), gamma i (prev (k + 1) (by omega) (extend A a) i) (extend A a i) = 1) ↔
          (∀ i : {i // i ∈ A}, filterWindow P i (a i) = true) ∧
          (∀ j : Fin k, internalFactor P j (last (extend A a (left j)))
            (first (extend A a (right j))) = 1) := by
      constructor
      · intro hg
        constructor
        · intro i
          have h := ((gamma_one a i).mp (hg i)) i.property
          simpa [extend, i.property] using h.1
        · intro j
          by_cases hr : right j ∈ A
          · have h := ((gamma_one a (right j)).mp (hg (right j))) hr
            have hp : 0 < (right j).val := by simp [right]
            rw [prev_extend, seamFactor, dif_pos hp, dif_pos hp] at h
            exact h.2
          · simp [internalFactor, Internal, hr]
      · rintro ⟨hf, hs⟩ i
        apply (gamma_one a i).mpr
        intro hi
        constructor
        · simpa [extend, hi] using hf ⟨i, hi⟩
        · by_cases hp : 0 < i.val
          · let j : Fin k := ⟨i.val - 1, by omega⟩
            have hr : right j = i := Fin.ext (by dsimp [j, right]; omega)
            have hl : left j = ⟨i.val - 1, by omega⟩ := rfl
            rw [prev_extend, seamFactor, dif_pos hp, dif_pos hp]
            have he : (⟨i.val - 1, by omega⟩ : Fin k) = j := rfl
            rw [he]
            simpa only [hl, hr] using hs j
          · simp [seamFactor, hp]
    have final_indicator (a : Side k A) :
        G (k + 1) (by omega) (extend A a) = if code A a = encode P then 1 else 0 := by
      rw [product_indicator (k + 1) (by omega) (extend A a)]
      change (if ∀ i : Fin (k + 1),
        gamma i (prev (k + 1) (by omega) (extend A a) i) (extend A a i) = 1
        then 1 else 0) = _
      simp only [final_filters, ← event P a]
    have semantic_final (v : Bool) : rho (k + 1) (by omega) v =
        Finset.expect Finset.univ (fun a => G (k + 1) (by omega) (extend A a) *
          if q (k + 1) (by omega) (extend A a) = v then 1 else 0) := by
      let E : {i : Fin (k + 1) // i ∈ A} ≃ {j : Fin (k + 1) // e (k + 1) (by omega) j ∈ A} :=
        { toFun := fun i => ⟨i.val, by simpa only [e] using i.property⟩
          invFun := fun j => ⟨j.val, by simpa only [e] using j.property⟩
          left_inv := fun i => rfl
          right_inv := fun j => rfl }
      rw [prefix_event (k + 1) (by omega) v]
      rw [← Fintype.expect_equiv (Equiv.arrowCongr E (Equiv.refl Window))
        (fun a : Side k A => if (∀ j : Fin (k + 1), gamma (e (k + 1) (by omega) j)
            (prev (k + 1) (by omega) (fill (k + 1) (by omega) (fun j => a (E.symm j))) j)
            (fill (k + 1) (by omega) (fun j => a (E.symm j)) j) = 1) ∧
          q (k + 1) (by omega) (fill (k + 1) (by omega) (fun j => a (E.symm j))) = v
          then (1 : ℚ) else 0) _ (fun _ => rfl)]
      change Finset.expect Finset.univ (fun a : Side k A =>
        if (∀ j : Fin (k + 1), gamma (e (k + 1) (by omega) j)
            (prev (k + 1) (by omega) (fill (k + 1) (by omega) (fun j => a (E.symm j))) j)
            (fill (k + 1) (by omega) (fun j => a (E.symm j)) j) = 1) ∧
          q (k + 1) (by omega) (fill (k + 1) (by omega) (fun j => a (E.symm j))) = v
          then (1 : ℚ) else 0) = _
      apply Finset.expect_congr rfl
      intro a _
      have hf : fill (k + 1) (by omega) (fun j => a (E.symm j)) = extend A a := rfl
      rw [hf, product_indicator (k + 1) (by omega) (extend A a)]
      by_cases hg : ∀ j : Fin (k + 1), gamma (e (k + 1) (by omega) j)
          (prev (k + 1) (by omega) (extend A a) j) (extend A a j) = 1 <;>
        by_cases hq : q (k + 1) (by omega) (extend A a) = v <;> simp [hg, hq]
    have final_mass : (∑ v : Bool, rho (k + 1) (by omega) v) = profileMass P := by
      simp_rw [semantic_final]
      rw [← Finset.expect_sum_comm]
      change Finset.expect Finset.univ (fun a => ∑ v : Bool,
        G (k + 1) (by omega) (extend A a) *
          if q (k + 1) (by omega) (extend A a) = v then 1 else 0) = _
      rw [mass_mean]
      apply Finset.expect_congr rfl
      intro a _
      rw [Finset.sum_eq_single (q (k + 1) (by omega) (extend A a))]
      · simp [final_indicator]
      · intro v _ hv
        simp [Ne.symm hv]
      · simp
    rw [← final_mass]
    unfold profileOperatorMass profileMatrixProduct
    apply Finset.sum_congr rfl
    intro v _
    rw [invariant (k + 1) (by omega) v]
    dsimp only [Fin.partialProd]
    rw [List.take_of_length_le (by simp)]
  have encode_injective : Function.Injective (@encode k A) := by
    rintro ⟨⟨t, ht⟩, p⟩ ⟨⟨u, hu⟩, q⟩ he
    have htu : t = u := congrArg Prod.fst he
    subst u
    congr 1
    funext i
    have hb := congrFun (congrArg Prod.snd he) i.val
    simpa only [FirstRejectionCutCapacity.encode, dif_pos i.property] using hb
  have hpositive : ∀ P : Profile k A, 0 < profileMass P := by
    intro P
    letI : Nonempty Window := ⟨.zero⟩
    unfold profileMass pushforwardSignatureMass
    have hrep : code A (representative P) = encode P :=
      (FirstRejectionCutCapacity.result k A).1 P
    have hterm : 0 < (profileLaw k A).mass (representative P) := by
      rw [weight]
      positivity
    have hnonneg : ∀ a : Side k A,
        0 ≤ (profileLaw k A).mass a *
          (if code A a = encode P then (1 : ℚ) else 0) := by
      intro a
      exact mul_nonneg ((profileLaw k A).nonnegative a) (by split_ifs <;> positivity)
    simp_rw [show ∀ a : Side k A,
        (if code A a = encode P then (profileLaw k A).mass a else 0) =
          (profileLaw k A).mass a * (if code A a = encode P then (1 : ℚ) else 0) by
            intro a; split_ifs <;> simp]
    have hsum := Finset.single_le_sum (fun a _ => hnonneg a)
      (show representative P ∈ (Finset.univ : Finset (Side k A)) from Finset.mem_univ _)
    have hsimp : (profileLaw k A).mass (representative P) *
          (if code A (representative P) = encode P then (1 : ℚ) else 0) > 0 := by
      simp [hrep]
      exact hterm
    exact lt_of_lt_of_le hsimp hsum
  have normalized : (∑ P : Profile k A, profileMass P) = 1 := by
    unfold profileMass pushforwardSignatureMass
    simp_rw [show ∀ (P : Profile k A) (a : Side k A),
        (if code A a = encode P then (profileLaw k A).mass a else 0) =
          (profileLaw k A).mass a * (if code A a = encode P then (1 : ℚ) else 0) by
            intro P a; split_ifs <;> simp]
    rw [Finset.sum_comm]
    calc
      (∑ a : Side k A, ∑ P : Profile k A,
          (profileLaw k A).mass a *
            (if code A a = encode P then (1 : ℚ) else 0)) =
          ∑ a : Side k A, 1 * (profileLaw k A).mass a := by
        apply Finset.sum_congr rfl
        intro a ha
        have hex : ∃ P : Profile k A, code A a = encode P :=
          (FirstRejectionCutCapacity.result k A).2.1 a
        obtain ⟨P, hP⟩ := hex
        have huniq : ∀ Q : Profile k A, code A a = encode Q → Q = P := by
          intro Q hQ
          exact encode_injective (hQ.symm.trans hP)
        rw [Finset.sum_eq_single P]
        · simp [hP]
        · intro Q hQ hne
          have hnot : ¬ code A a = encode Q := fun h => hne (huniq Q h)
          simp [hnot]
        · intro h
          exact (h (Finset.mem_univ P)).elim
      _ = 1 := by
        simp only [one_mul]
        exact (profileLaw k A).total
  exact ⟨weight, event, fun P => ⟨bridge P, hpositive P⟩, normalized⟩

#print axioms result

end D5.S3.Arith.FibonacciAtomic.FirstRejectionProfileMass
