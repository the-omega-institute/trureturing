/- GID: D5/S3/Combinatorics/Circle/Lattice/LatticeChargePrecedence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/Lattice/LatticeChargePrecedence
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Saturated lattice returns bound the same physical suffix charge. -/
import D5.S3.Combinatorics.Circle.RunFirstEarTransport
import Batteries.Tactic.OpenPrivate

/-! Necessary physical order from lattice saturation and a literal fresh insertion. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.Lattice.LatticeChargePrecedence
open SourceWidth RunFirstEarTransport
open private ear_prefix from D5.S3.Combinatorics.Circle.RunFirstEarTransport
open private sum_linear prefix_nonneg_le from D5.S3.Combinatorics.Circle.PeriodicShortening

/-- The return, insertion cut, suffix budget, and heavy-label precedence all refer
to the same occurrence. Positions are zero based, so the fresh label precedes
`nu` precisely when `j ≤ sigma.idxOf nu`. Both complete totals are retained. -/
theorem lattice_saturation_suffix_precedence
    (m : ℕ) (sigma : List (Fin m)) (j : ℕ)
    (hperm : sigma.Perm (List.finRange m)) (hj : j ≤ m)
    (f q : Fin m → ℤ) (g : Fin (m + 1) → ℤ) (G C N A H : ℤ)
    (hG : 0 < G) (hA : 0 < A)
    (hgrid : ∀ i, G ∣ f i) (hq : ∀ i, 0 ≤ q i)
    (hcharge : (sigma.map q).sum = A)
    (hpair : ∀ i, g i.castSucc = 2 * f i - q i)
    (hfresh : g (Fin.last m) = A)
    (holdsum : (sigma.map f).sum = 0)
    (hnewsum : ((earWord m sigma j).map g).sum = 0)
    (hold : ∀ r, ((sigma.take r).map f).sum ∈ Set.Icc (0 : ℤ) C)
    (hnew : ∀ r, (((earWord m sigma j).take r).map g).sum ∈ Set.Icc (0 : ℤ) N)
    (nu : Fin m) (hnu : f nu = -H) (hH : 0 < H)
    (hHgrid : G ∣ H) (hHC : H ≤ C) (hsat : C < H + G) (hqnu : 0 < q nu) :
    let p := sigma.idxOf nu
    ((sigma.take p).map f).sum = H ∧
    ((sigma.take (p + 1)).map f).sum = 0 ∧
    j ≤ p ∧
    ((sigma.drop p).map q).sum ≤ N - 2 * H ∧
    ∀ delta : Fin m, delta ≠ nu → N - 2 * H < q delta + q nu →
      sigma.idxOf delta < p := by
  classical
  let p := sigma.idxOf nu
  have memall (i : Fin m) : i ∈ sigma := hperm.mem_iff.mpr (List.mem_finRange i)
  have hp : p < sigma.length := List.idxOf_lt_length_of_mem (memall nu)
  have hlen : sigma.length = m := by simpa using hperm.length_eq
  have hcut : j ≤ sigma.length := by omega
  have hstep (v : Fin m → ℤ) :
      ((sigma.take (p + 1)).map v).sum = ((sigma.take p).map v).sum + v nu := by
    rw [List.take_add_one, List.getElem?_idxOf (memall nu)]
    simp
  have hb := hold p
  have ha := hold (p + 1)
  rw [hstep f, hnu] at ha
  have hdvd : G ∣ ((sigma.take p).map f).sum := by
    apply List.dvd_sum
    intro z hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
    exact hgrid i
  obtain ⟨z, hz⟩ := dvd_sub hdvd hHgrid
  have hz0 : z = 0 := by
    have hprod : 0 ≤ G * z ∧ G * z < G := by
      constructor <;> linarith only [hb.2, ha.1, hsat, hz]
    have : 0 ≤ z := by nlinarith [hprod.1]
    have : z < 1 := by nlinarith [hprod.2]
    omega
  have hreturn : ((sigma.take p).map f).sum = H := by rw [hz0, mul_zero] at hz; omega
  have hzero : ((sigma.take (p + 1)).map f).sum = 0 := by rw [hstep, hreturn, hnu]; ring
  have prefix_height (r : ℕ) :
      (((earWord m sigma j).take r).map g).sum =
      2 * ((sigma.take (if r ≤ j then r else r - 1)).map f).sum -
      ((sigma.take (if r ≤ j then r else r - 1)).map q).sum +
      (if r ≤ j then 0 else A) := by
    rw [ear_prefix m sigma j hcut]
    have he : (fun i : Fin m => g i.castSucc) = fun i => 2 * f i + (-1) * q i := by
      funext i; rw [hpair]; ring
    rw [he, hfresh, sum_linear]
    ring
  have hearly : j ≤ p := by
    by_contra hn
    have hb := (hnew (p + 1)).1
    simp only [prefix_height, ite_eq_left (by omega : p + 1 ≤ j), hzero] at hb
    have hnq := (prefix_nonneg_le sigma q (fun i _ => hq i) p).1
    rw [hstep q] at hb
    linarith
  have hbudget : ((sigma.drop p).map q).sum ≤ N - 2 * H := by
    have hb := (hnew (p + 1)).2
    simp only [prefix_height, ite_eq_right (by omega : ¬ p + 1 ≤ j), Nat.add_sub_cancel, hreturn] at hb
    have hs : ((sigma.take p).map q).sum + ((sigma.drop p).map q).sum = A := by
      rw [← List.sum_append, ← List.map_append, List.take_append_drop, hcharge]
    linarith
  refine ⟨hreturn, hzero, hearly, hbudget, ?_⟩
  intro delta hne hheavy
  by_contra hn
  have suffix_mem (i : Fin m) (hi : p ≤ sigma.idxOf i) : i ∈ sigma.drop p := by
    have hall : i ∈ sigma.take p ++ sigma.drop p := by simpa using memall i
    rcases List.mem_append.mp hall with ht | ht
    · have := (List.mem_take_iff_idxOf_lt (memall i)).mp ht
      omega
    · exact ht
  have hd := suffix_mem delta (by omega)
  have hv := suffix_mem nu le_rfl
  have hsub : ({delta, nu} : Finset (Fin m)) ⊆ (sigma.drop p).toFinset := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp [hd, hv]
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := q) hsub
    (by intro i _ _; exact hq i)
  have hnd := hperm.nodup_iff.mpr (List.nodup_finRange m)
  rw [List.sum_toFinset q (hnd.drop (i := p))] at hsum
  simp only [Finset.sum_pair hne] at hsum
  linarith

#print axioms lattice_saturation_suffix_precedence
end D5.S3.Combinatorics.Circle.Lattice.LatticeChargePrecedence
