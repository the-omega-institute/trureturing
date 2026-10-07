/- GID: D5/S1/Words/AdmissibleWords/KBonacciActualCommonImagePlateau
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciActualCommonImagePlateau
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Two-step plateau collapse and the first common exact-length bit budget. -/

import D5.S1.Words.AdmissibleWords.KBonacciJointLegalRealization
import D5.S1.Words.AdmissibleWords.KBonacciActualTailImages
import Mathlib.Data.Set.Card

set_option autoImplicit false
noncomputable section
namespace D5.S1.Words.AdmissibleWords.KBonacciActualCommonImagePlateau

open Finset Polynomial
open D5.S0.Tower.DBonacci.Names D5.S0.Tower.DBonacci.Substitution
open D5.S0.Tower.DBonacci.Values
open D5.S1.Words.AdmissibleWords.KBonacciJointLegalRealization
open D5.S1.Words.AdmissibleWords.KBonacciActualTailImages

/-- Every two-step plateau of the raw common remainder image is full, and the
least full-image length is at most twice the common-image cardinality minus three. -/
theorem kbonacci_actual_common_image_plateau_and_budget
    (k d r : ℕ) (hk : 2 ≤ k) (hd : 2 ≤ d) (hr : 1 ≤ r)
    (a : Fin r → ℕ) (hainj : Function.Injective a) (ha : ∀ i, 2 ≤ a i) :
    let R := ZMod d
    let Phi := fun b : ℕ => (X ^ b - ∑ j ∈ range b, X ^ j : R[X])
    let Q := ∀ i : Fin r, AdjoinRoot (Phi (a i))
    let q : R[X] →+* Q := RingHom.pi (fun i => AdjoinRoot.mk (Phi (a i)))
    let H := q.range
    let O := fun P : R[X] => fun i : Fin r => P %ₘ Phi (a i)
    let Pw := fun {n : ℕ} (w : Fin n → Bool) =>
      ∑ i : Fin n, monomial i.val (if w i then 1 else 0 : R)
    let I := fun n : ℕ => {y : Fin r → R[X] | ∃ w : Fin n → Bool,
      DBonacciAdmissible k n w ∧ O (Pw w) = y}
    let M := Nat.card H
    (∀ n : ℕ, I n = I (n + 2) → I n = Set.range O) ∧
    ∃ N : ℕ, IsLeast {n : ℕ | I n = Set.range O} N ∧
      N ≤ 2 * M - 3 ∧ (∀ n : ℕ, I n = Set.range O ↔ N ≤ n) := by
  classical
  dsimp only
  let : NeZero d := ⟨by omega⟩
  let : Fact (1 < d) := ⟨by omega⟩
  let R := ZMod d
  let Phi := fun b : ℕ => (X ^ b - ∑ j ∈ range b, X ^ j : R[X])
  let Q := ∀ i : Fin r, AdjoinRoot (Phi (a i))
  let q : R[X] →+* Q := RingHom.pi (fun i => AdjoinRoot.mk (Phi (a i)))
  let H := q.range
  let OH : R[X] →+* H := q.rangeRestrict
  let x : H := OH X
  let O := fun P : R[X] => fun i : Fin r => P %ₘ Phi (a i)
  let Pw := fun {n : ℕ} (w : Fin n → Bool) =>
    ∑ i : Fin n, monomial i.val (if w i then 1 else 0 : R)
  let E := fun (n : ℕ) (w : Fin n → Bool) =>
    ∑ i : Fin n, if w i then x ^ i.val else 0
  let Iq := fun n : ℕ => {y : H | ∃ w : Fin n → Bool,
    DBonacciAdmissible k n w ∧ E n w = y}
  let I := fun n : ℕ => {y : Fin r → R[X] | ∃ w : Fin n → Bool,
    DBonacciAdmissible k n w ∧ O (Pw w) = y}
  let M := Nat.card H
  let F := ∏ i : Fin r, Phi (a i)
  let A := AdjoinRoot F
  have hdiv : ∀ i : Fin r, Phi (a i) ∣ F := fun i => dvd_prod_of_mem _ (mem_univ i)
  let Theta : A →+* Q := RingHom.pi (fun i =>
    (AdjoinRoot.algHomOfDvd R F (Phi (a i)) (hdiv i)).toRingHom)
  have hTheta : ∀ P : R[X], Theta (AdjoinRoot.mk F P) = q P := by
    intro P
    funext i
    change AdjoinRoot.algHomOfDvd R F (Phi (a i)) (hdiv i) (AdjoinRoot.mk F P) =
      AdjoinRoot.mk (Phi (a i)) P
    rw [AdjoinRoot.coe_algHomOfDvd]
    change aeval (AdjoinRoot.root (Phi (a i))) P = AdjoinRoot.mk (Phi (a i)) P
    exact AdjoinRoot.aeval_eq P
  have hmem : ∀ b : A, Theta b ∈ H := by
    intro b
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective b
    exact ⟨P, (hTheta P).symm⟩
  let phi : A →+* H := Theta.codRestrict H hmem
  have hphi : ∀ P : R[X], phi (AdjoinRoot.mk F P) = OH P := by
    intro P
    apply Subtype.ext
    exact hTheta P
  have hphisurj : Function.Surjective phi := by
    intro y
    obtain ⟨P, rfl⟩ := q.rangeRestrict_surjective y
    exact ⟨AdjoinRoot.mk F P, hphi P⟩
  have hsupply := kbonacci_joint_legal_realization k d r hk hd hr a hainj ha
  have hcardA : Nat.card A = d ^ (∑ i : Fin r, a i) := hsupply.1
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [hcardA]; exact pow_ne_zero _ (by omega))
  let : Finite H := Finite.of_surjective phi hphisurj
  have hxunit : IsUnit x := by
    have hu : IsUnit (AdjoinRoot.root F) := hsupply.2.1
    have hmap := hu.map phi
    change IsUnit (phi (AdjoinRoot.mk F X)) at hmap
    rw [hphi] at hmap
    exact hmap
  have hlow : ∀ i, (∑ j ∈ range (a i), (X : R[X]) ^ j).degree < a i := by
    intro i
    simpa only [← Fin.sum_univ_eq_sum_range, C_1, one_mul] using
      degree_sum_fin_lt (fun _ : Fin (a i) => (1 : R))
  have hmonic : ∀ i, (Phi (a i)).Monic := fun i => monic_X_pow_sub (hlow i)
  let rho : Q → (Fin r → R[X]) := fun y i => AdjoinRoot.modByMonicHom (hmonic i) (y i)
  have hrho : ∀ P : R[X], rho (q P) = O P := by intro P; funext i; rfl
  have hrhoinj : Function.Injective rho := by
    intro y z he
    funext i
    exact (AdjoinRoot.mk_leftInverse (hmonic i)).injective (congrFun he i)
  let f : H → (Fin r → R[X]) := fun y => rho y.val
  have hfOH : ∀ P : R[X], f (OH P) = O P := hrho
  have hfrange : Set.range f = Set.range O := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨P, rfl⟩ := q.rangeRestrict_surjective z
      exact ⟨P, (hfOH P).symm⟩
    · rintro ⟨P, rfl⟩; exact ⟨OH P, hfOH P⟩
  let ef : H → Set.range O := fun y => ⟨f y, hfrange ▸ Set.mem_range_self y⟩
  have hef : Function.Bijective ef := by
    constructor
    · intro y z he
      apply Subtype.ext
      exact hrhoinj (congrArg Subtype.val he)
    · intro y
      have hy : y.val ∈ Set.range f := by rw [hfrange]; exact y.property
      obtain ⟨z, hz⟩ := hy
      exact ⟨z, Subtype.ext hz⟩
  let e : H ≃ Set.range O := Equiv.ofBijective ef hef
  have hfinj : Function.Injective f := by
    intro y z he
    apply e.injective
    exact Subtype.ext he
  have hword : ∀ n (w : Fin n → Bool), OH (Pw w) = E n w := by
    intro n w
    simp only [Pw, E, map_sum, ← C_mul_X_pow_eq_monomial, map_mul, map_pow]
    apply sum_congr rfl
    intro i _
    cases w i <;> simp [x]
  have hraw : ∀ n, f '' Iq n = I n := by
    intro n
    ext y
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, by rw [← hword, hfOH]⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨E n w, ⟨w, hw, rfl⟩, by rw [← hword, hfOH]⟩
  let i0 : Fin r := ⟨0, by omega⟩
  have hs0 := kbonacci_joint_legal_realization k d 1 hk hd (by omega)
    (fun _ : Fin 1 => a i0) (fun i j _ => Subsingleton.elim i j) (fun _ => ha i0)
  have hc0 : Nat.card (AdjoinRoot (Phi (a i0))) = d ^ a i0 := by
    simpa only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] using hs0.1
  have hproj : Function.Surjective (fun y : H => y.val i0) := by
    intro y
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective y
    exact ⟨OH P, rfl⟩
  have hM : 4 ≤ M := by
    have hle := Nat.card_le_card_of_surjective (fun y : H => y.val i0) hproj
    rw [hc0] at hle
    have hp : d ^ 2 ≤ d ^ a i0 := Nat.pow_le_pow_right (by omega) (ha i0)
    have h4 : 4 ≤ d ^ 2 := by nlinarith
    exact h4.trans (hp.trans hle)
  have h01 : (0 : H) ≠ 1 := by
    intro he
    let : Subsingleton H := subsingleton_of_zero_eq_one he
    have hc : M = 1 := Nat.card_of_subsingleton (0 : H)
    omega
  let : Nontrivial H := ⟨⟨0, 1, h01⟩⟩
  have hzero : ∀ n, (0 : H) ∈ Iq n := by
    intro n
    refine ⟨fun _ => false, ?_, by simp [E]⟩
    cases k with
    | zero => omega
    | succ m => exact runAdmissible_all_false m m n
  have hstep : ∀ n, Iq n ⊆ Iq (n + 1) := by
    intro n y hy
    obtain ⟨w, hw, he⟩ := hy
    refine ⟨Fin.snoc w false, admissible_snoc_false k n w hw, ?_⟩
    rw [← he]
    dsimp only [E]
    rw [Fin.sum_univ_castSucc]
    simp
  have hmono : Monotone Iq := monotone_nat_of_le_succ hstep
  have hleft : ∀ n, (fun y : H => x * y) '' Iq n ⊆ Iq (n + 1) := by
    intro n y hy
    obtain ⟨z, ⟨w, hw, rfl⟩, rfl⟩ := hy
    refine ⟨Fin.cons false w, ?_, ?_⟩
    · cases k with
      | zero => omega
      | succ m =>
        change runAdmissible m m (n + 1) (Fin.cons false w) = true
        change runAdmissible m m n w = true at hw
        cases m <;> simpa only [runAdmissible, Fin.cons_zero, Bool.false_eq_true,
          ↓reduceIte, Fin.tail_cons] using hw
    · dsimp only [E]
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte,
        zero_add, Fin.val_succ, mul_sum]
      apply sum_congr rfl
      intro i _
      cases w i <;> simp [pow_succ, mul_comm]
  have htail : ∀ n, (fun y : H => y + x ^ (n + 1)) '' Iq n ⊆ Iq (n + 2) := by
    intro n y hy
    have ht := (actual_tail_zero_image_decomposition x k hk
      (n + 2) 1 1 (by omega) le_rfl).2.2.1 (by omega)
    change _ = (fun z : H => z + x ^ (n + 2 - 1) *
      (∑ j ∈ range 1, x ^ j)) '' Iq (n + 2 - 1 - 1) at ht
    have he : n + 2 - 1 = n + 1 := by omega
    have hlen : n + 2 - 1 - 1 = n := by omega
    rw [hlen] at ht
    simp only [he, sum_range_one, pow_zero, mul_one] at ht
    rw [← ht] at hy
    obtain ⟨w, hw, _, hwval⟩ := hy
    exact ⟨w, hw, hwval⟩
  have hI1 : Iq 1 = {0, 1} := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      cases hbit : w (⟨0, Nat.zero_lt_one⟩ : Fin 1) <;> simp [E, Fin.sum_univ_one, hbit]
    · intro hy
      rcases hy with hy | hy
      · subst y; exact hzero 1
      · subst y
        refine ⟨fun _ => true, ?_, by simp [E]⟩
        cases k with
        | zero => omega
        | succ m => exact runAdmissible_eq_true_of_length_le m m 1 _ (by omega) le_rfl
  have hc1 : (Iq 1).ncard = 2 := by rw [hI1]; exact Set.ncard_pair h01
  have hplateau : ∀ n, Iq n = Iq (n + 2) → Iq n = Set.univ := by
    intro n hp
    let S := Iq n
    have hmulsub : (fun y : H => x * y) '' S ⊆ S := by
      intro y hy
      change y ∈ Iq n
      rw [hp]
      exact hstep (n + 1) (hleft n hy)
    let mx : H ↪ H := ⟨fun y => x * y, hxunit.mul_right_injective⟩
    have hmx : (fun y : H => x * y) '' S = S :=
      Set.map_eq_of_subset (f := mx) hmulsub
    have htrsub : (fun y : H => y + x ^ (n + 1)) '' S ⊆ S := by
      intro y hy
      change y ∈ Iq n
      rw [hp]
      exact htail n hy
    let tr : H ↪ H := ⟨fun y => y + x ^ (n + 1), fun _ _ he => add_right_cancel he⟩
    have htr : (fun y : H => y + x ^ (n + 1)) '' S = S :=
      Set.map_eq_of_subset (f := tr) htrsub
    have hpow : ∀ t : ℕ, (fun y : H => x ^ t * y) '' S = S := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        calc
          (fun y : H => x ^ (t + 1) * y) '' S =
              (fun y : H => x * y) '' ((fun y : H => x ^ t * y) '' S) := by
            rw [Set.image_image]
            congr 1
            funext y
            rw [pow_succ]
            ring
          _ = S := by rw [ih, hmx]
    have hforward : ∀ t y, y ∈ S → x ^ t * y ∈ S := by
      intro t y hy
      rw [← hpow t]
      exact ⟨y, hy, rfl⟩
    have hpull : ∀ t y, y ∈ S → ∃ z ∈ S, x ^ t * z = y := by
      intro t y hy
      rw [← hpow t] at hy
      exact hy
    have hone : ∀ y ∈ S, y + 1 ∈ S := by
      intro y hy
      have ht : x ^ (n + 1) * y + x ^ (n + 1) ∈ S := by
        rw [← htr]
        exact ⟨x ^ (n + 1) * y, hforward (n + 1) y hy, rfl⟩
      obtain ⟨z, hz, he⟩ := hpull (n + 1) _ ht
      have he' : z = y + 1 := (hxunit.pow (n + 1)).mul_right_injective
        (by simpa only [mul_add, mul_one] using he)
      simpa only [he'] using hz
    have htrans : ∀ j y, y ∈ S → y + x ^ j ∈ S := by
      intro j y hy
      obtain ⟨z, hz, he⟩ := hpull j y hy
      have hh := hforward j (z + 1) (hone z hz)
      simpa only [mul_add, mul_one, he] using hh
    have hrepeat : ∀ (j t : ℕ) (y : H), y ∈ S → y + (t : H) * x ^ j ∈ S := by
      intro j t
      induction t with
      | zero => intro y hy; simpa using hy
      | succ t ih =>
        intro y hy
        have hh := htrans j _ (ih y hy)
        simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using hh
    have hpoly : ∀ P : R[X], ∀ y ∈ S, y + OH P ∈ S := by
      intro P
      induction P using Polynomial.induction_on' with
      | add P Q hP hQ =>
        intro y hy
        simpa only [map_add, add_assoc] using hQ _ (hP y hy)
      | monomial j c =>
        intro y hy
        have hc : OH (Polynomial.C c) = (c.val : H) := by
          calc
            OH (Polynomial.C c) = OH (Polynomial.C (c.val : R)) :=
              congrArg (fun t : R => OH (Polynomial.C t)) (ZMod.natCast_zmod_val c).symm
            _ = (c.val : H) := by simp only [Polynomial.C_eq_natCast, map_natCast]
        simpa only [← C_mul_X_pow_eq_monomial, map_mul, map_pow, hc] using
          hrepeat j c.val y hy
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨P, rfl⟩ := q.rangeRestrict_surjective y
    simpa only [zero_add] using hpoly P 0 (hzero n)
  have hgrowth : ∀ n, Iq n ≠ Set.univ → (Iq n).ncard < (Iq (n + 2)).ncard := by
    intro n hn
    apply Set.ncard_lt_ncard ?_ (Set.toFinite _)
    exact (hmono (show n ≤ n + 2 by omega)).ssubset_of_ne
      (fun he => hn (hplateau n he))
  have hodd : ∀ j : ℕ, min M (j + 2) ≤ (Iq (2 * j + 1)).ncard := by
    intro j
    induction j with
    | zero => simpa only [Nat.mul_zero, Nat.zero_add, hc1] using min_le_right M 2
    | succ j ih =>
      by_cases hfull : Iq (2 * j + 1) = Set.univ
      · have hfull' : Iq (2 * (j + 1) + 1) = Set.univ := by
          apply Set.eq_univ_of_univ_subset
          rw [← hfull]
          exact hmono (by omega)
        rw [hfull', Set.ncard_univ]
        exact min_le_left M _
      · have hlt : (Iq (2 * j + 1)).ncard < M := Set.ncard_lt_card hfull
        have hsmall : j + 2 < M := by
          by_contra hh
          have hm : M ≤ j + 2 := by omega
          rw [min_eq_left hm] at ih
          omega
        have hin : j + 2 ≤ (Iq (2 * j + 1)).ncard := by
          simpa only [min_eq_right hsmall.le] using ih
        have hgrow := hgrowth (2 * j + 1) hfull
        have hidx : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by omega
        rw [hidx] at hgrow
        exact (min_le_right M (j + 1 + 2)).trans (by omega)
  have hbounded : Iq (2 * M - 3) = Set.univ := by
    have hlen : 2 * (M - 2) + 1 = 2 * M - 3 := by omega
    have hmin : min M (M - 2 + 2) = M := by omega
    have hlower := hodd (M - 2)
    rw [hlen, hmin] at hlower
    apply (Set.eq_univ_iff_ncard _).mpr
    exact Nat.le_antisymm (Set.ncard_le_card _) hlower
  have hfull : ∀ n, I n = Set.range O ↔ Iq n = Set.univ := by
    intro n
    rw [← hraw n, ← hfrange, ← Set.image_univ]
    exact hfinj.image_injective.eq_iff
  have hpublic : ∀ n, I n = I (n + 2) → I n = Set.range O := by
    intro n hn
    apply (hfull n).mpr
    apply hplateau n
    apply hfinj.image_injective
    simpa only [hraw] using hn
  have hex : ∃ n, Iq n = Set.univ := ⟨2 * M - 3, hbounded⟩
  let N := Nat.find hex
  have hN : Iq N = Set.univ := Nat.find_spec hex
  have hleast : ∀ n, Iq n = Set.univ → N ≤ n := fun n hn => Nat.find_min' hex hn
  have hNbound : N ≤ 2 * M - 3 := hleast _ hbounded
  have hlater : ∀ n, Iq n = Set.univ ↔ N ≤ n := by
    intro n
    constructor
    · exact hleast n
    · intro hn
      apply Set.eq_univ_of_univ_subset
      rw [← hN]
      exact hmono hn
  refine ⟨hpublic, N, ⟨(hfull N).mpr hN, ?_⟩, hNbound, ?_⟩
  · intro n hn
    exact hleast n ((hfull n).mp hn)
  · intro n
    exact (hfull n).trans (hlater n)

end D5.S1.Words.AdmissibleWords.KBonacciActualCommonImagePlateau
