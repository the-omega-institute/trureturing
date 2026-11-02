import D5.S3.FiniteGroups.BajnokBeattyFirstCharacteristicDefect
open D5.S3.FiniteGroups.BajnokBeattyFirstCharacteristicDefect
open D5.S3.FiniteGroups.BajnokBeattyCayleyReturnMoments (graph q19 q33)
open scoped Classical
noncomputable section

example :
    let m : ℤ := 6 * 2 - 1
    let D : ℤ := (m^2-9)/2
    let H := ZMod (3 : ℤ).natAbs × ZMod (3 * D).natAbs
    letI : NeZero (3 * D).natAbs := ⟨by norm_num [D,m]⟩
    letI : Fintype H := Fintype.ofFinite H
    let C19 : SimpleGraph H := graph (q19 3 D 2)
    let C33 : SimpleGraph H := graph (q33 3 D 2)
    let A19 := C19.adjMatrix ℂ
    let A33 := C33.adjMatrix ℂ
    (Nat.card H : ℤ) = 504 ∧
    0 < (24 : ℕ) ∧ 24 ≤ Fintype.card H ∧
    (∀ j : ℕ, j < 24 →
      A19.charpoly.coeff (Fintype.card H - j) =
        A33.charpoly.coeff (Fintype.card H - j)) ∧
    (A33.charpoly.coeff 480 - A19.charpoly.coeff 480 = (-42 : ℂ)) ∧
    A19.charpoly ≠ A33.charpoly := by
  let m : ℤ := 6 * 2 - 1
  let D : ℤ := (m^2-9)/2
  let H := ZMod (3 : ℤ).natAbs × ZMod (3 * D).natAbs
  letI : NeZero (3 * D).natAbs := ⟨by norm_num [D,m]⟩
  letI : Fintype H := Fintype.ofFinite H
  let C19 : SimpleGraph H := graph (q19 3 D 2)
  let C33 : SimpleGraph H := graph (q33 3 D 2)
  let A19 := C19.adjMatrix ℂ
  let A33 := C33.adjMatrix ℂ
  have hN : (3 : ℤ)^2 * D = 504 := by norm_num [D,m]
  have hn : (3 * (m-3)).toNat = 24 := by norm_num [m]
  obtain ⟨hc,hpos,hbound,hprefix,hgap,hne⟩ := first_characteristic_defect 3 2
    (by norm_num) (by decide) (by norm_num)
  change (Nat.card H : ℤ) = (3 : ℤ)^2 * D at hc
  rw [hN] at hc
  have hcard : Fintype.card H = 504 := by
    have hz : (Fintype.card H : ℤ) = 504 := by
      simpa only [Nat.card_eq_fintype_card] using hc
    exact_mod_cast hz
  change 0 < (3 * (m-3)).toNat at hpos
  change (3 * (m-3)).toNat ≤ Fintype.card H at hbound
  change (∀ j : ℕ, j < (3 * (m-3)).toNat →
    A19.charpoly.coeff (Fintype.card H - j) =
      A33.charpoly.coeff (Fintype.card H - j)) at hprefix
  change A33.charpoly.coeff (Fintype.card H - (3 * (m-3)).toNat) -
    A19.charpoly.coeff (Fintype.card H - (3 * (m-3)).toNat) =
      ((-2 * 3 * (3 * 2 + 1) : ℤ) : ℂ) at hgap
  rw [hn] at hpos hbound hprefix hgap
  rw [hcard] at hgap
  norm_num only [show 504 - 24 = 480 by omega, Int.reduceMul,
    Int.reduceAdd, Int.cast_neg, Int.cast_ofNat] at hgap
  exact ⟨hc,hpos,hbound,hprefix,hgap,hne⟩

example :
    let m : ℤ := 6 * 2 - 1
    let D : ℤ := (m^2-9)/2
    let H := ZMod (5 : ℤ).natAbs × ZMod (5 * D).natAbs
    letI : NeZero (5 * D).natAbs := ⟨by norm_num [D,m]⟩
    letI : Fintype H := Fintype.ofFinite H
    let C19 : SimpleGraph H := graph (q19 5 D 2)
    let C33 : SimpleGraph H := graph (q33 5 D 2)
    let A19 := C19.adjMatrix ℂ
    let A33 := C33.adjMatrix ℂ
    (Nat.card H : ℤ) = 1400 ∧
    0 < (40 : ℕ) ∧ 40 ≤ Fintype.card H ∧
    (∀ j : ℕ, j < 40 →
      A19.charpoly.coeff (Fintype.card H - j) =
        A33.charpoly.coeff (Fintype.card H - j)) ∧
    (A33.charpoly.coeff 1360 - A19.charpoly.coeff 1360 = (-70 : ℂ)) ∧
    A19.charpoly ≠ A33.charpoly := by
  let m : ℤ := 6 * 2 - 1
  let D : ℤ := (m^2-9)/2
  let H := ZMod (5 : ℤ).natAbs × ZMod (5 * D).natAbs
  letI : NeZero (5 * D).natAbs := ⟨by norm_num [D,m]⟩
  letI : Fintype H := Fintype.ofFinite H
  let C19 : SimpleGraph H := graph (q19 5 D 2)
  let C33 : SimpleGraph H := graph (q33 5 D 2)
  let A19 := C19.adjMatrix ℂ
  let A33 := C33.adjMatrix ℂ
  have hN : (5 : ℤ)^2 * D = 1400 := by norm_num [D,m]
  have hn : (5 * (m-3)).toNat = 40 := by norm_num [m]
  obtain ⟨hc,hpos,hbound,hprefix,hgap,hne⟩ := first_characteristic_defect 5 2
    (by norm_num) (by decide) (by norm_num)
  change (Nat.card H : ℤ) = (5 : ℤ)^2 * D at hc
  rw [hN] at hc
  have hcard : Fintype.card H = 1400 := by
    have hz : (Fintype.card H : ℤ) = 1400 := by
      simpa only [Nat.card_eq_fintype_card] using hc
    exact_mod_cast hz
  change 0 < (5 * (m-3)).toNat at hpos
  change (5 * (m-3)).toNat ≤ Fintype.card H at hbound
  change (∀ j : ℕ, j < (5 * (m-3)).toNat →
    A19.charpoly.coeff (Fintype.card H - j) =
      A33.charpoly.coeff (Fintype.card H - j)) at hprefix
  change A33.charpoly.coeff (Fintype.card H - (5 * (m-3)).toNat) -
    A19.charpoly.coeff (Fintype.card H - (5 * (m-3)).toNat) =
      ((-2 * 5 * (3 * 2 + 1) : ℤ) : ℂ) at hgap
  rw [hn] at hpos hbound hprefix hgap
  rw [hcard] at hgap
  norm_num only [show 1400 - 40 = 1360 by omega, Int.reduceMul,
    Int.reduceAdd, Int.cast_neg, Int.cast_ofNat] at hgap
  exact ⟨hc,hpos,hbound,hprefix,hgap,hne⟩

example :
    let m : ℤ := 6 * 2 - 1
    let D : ℤ := (m^2-9)/2
    let H := ZMod (9 : ℤ).natAbs × ZMod (9 * D).natAbs
    letI : NeZero (9 * D).natAbs := ⟨by norm_num [D,m]⟩
    letI : Fintype H := Fintype.ofFinite H
    let C19 : SimpleGraph H := graph (q19 9 D 2)
    let C33 : SimpleGraph H := graph (q33 9 D 2)
    let A19 := C19.adjMatrix ℂ
    let A33 := C33.adjMatrix ℂ
    (Nat.card H : ℤ) = 4536 ∧
    0 < (72 : ℕ) ∧ 72 ≤ Fintype.card H ∧
    (∀ j : ℕ, j < 72 →
      A19.charpoly.coeff (Fintype.card H - j) =
        A33.charpoly.coeff (Fintype.card H - j)) ∧
    (A33.charpoly.coeff 4464 - A19.charpoly.coeff 4464 = (-126 : ℂ)) ∧
    A19.charpoly ≠ A33.charpoly := by
  let m : ℤ := 6 * 2 - 1
  let D : ℤ := (m^2-9)/2
  let H := ZMod (9 : ℤ).natAbs × ZMod (9 * D).natAbs
  letI : NeZero (9 * D).natAbs := ⟨by norm_num [D,m]⟩
  letI : Fintype H := Fintype.ofFinite H
  let C19 : SimpleGraph H := graph (q19 9 D 2)
  let C33 : SimpleGraph H := graph (q33 9 D 2)
  let A19 := C19.adjMatrix ℂ
  let A33 := C33.adjMatrix ℂ
  have hN : (9 : ℤ)^2 * D = 4536 := by norm_num [D,m]
  have hn : (9 * (m-3)).toNat = 72 := by norm_num [m]
  obtain ⟨hc,hpos,hbound,hprefix,hgap,hne⟩ := first_characteristic_defect 9 2
    (by norm_num) (by decide) (by norm_num)
  change (Nat.card H : ℤ) = (9 : ℤ)^2 * D at hc
  rw [hN] at hc
  have hcard : Fintype.card H = 4536 := by
    have hz : (Fintype.card H : ℤ) = 4536 := by
      simpa only [Nat.card_eq_fintype_card] using hc
    exact_mod_cast hz
  change 0 < (9 * (m-3)).toNat at hpos
  change (9 * (m-3)).toNat ≤ Fintype.card H at hbound
  change (∀ j : ℕ, j < (9 * (m-3)).toNat →
    A19.charpoly.coeff (Fintype.card H - j) =
      A33.charpoly.coeff (Fintype.card H - j)) at hprefix
  change A33.charpoly.coeff (Fintype.card H - (9 * (m-3)).toNat) -
    A19.charpoly.coeff (Fintype.card H - (9 * (m-3)).toNat) =
      ((-2 * 9 * (3 * 2 + 1) : ℤ) : ℂ) at hgap
  rw [hn] at hpos hbound hprefix hgap
  rw [hcard] at hgap
  norm_num only [show 4536 - 72 = 4464 by omega, Int.reduceMul,
    Int.reduceAdd, Int.cast_neg, Int.cast_ofNat] at hgap
  exact ⟨hc,hpos,hbound,hprefix,hgap,hne⟩

