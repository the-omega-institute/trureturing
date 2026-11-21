/- GID: D5/S3/Geometry/KozakiKakeiPreservation
   generality: G
   mirror-B: D5/B/S3/Geometry/KozakiKakeiPreservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dihedral permutations preserve the literal matching-product equality. -/
import D5.S3.Geometry.KozakiKakeiCycle

namespace D5.S3.Geometry.KozakiKakei
open scoped BigOperators

private def paritySet (m p : ℕ) : Finset (Col m) :=
  Finset.univ.filter (fun i => i.val % 2 = p)

private theorem mem_paritySet {m p : ℕ} {i : Col m} :
    i ∈ paritySet m p ↔ i.val % 2 = p := by
  simp [paritySet]

private def parityStart {m p : ℕ} (hp : p < 2) (e : Fin m) : Col m :=
  ⟨2 * e.val + p, by have := e.isLt; omega⟩

private theorem parityStart_mem {m p : ℕ} (hp : p < 2) (e : Fin m) :
    parityStart hp e ∈ paritySet m p := by
  rw [mem_paritySet]
  change (2 * e.val + p) % 2 = p
  omega

private theorem parityStart_injective {m p : ℕ} (hp : p < 2) :
    Function.Injective (parityStart (m := m) hp) := by
  intro i j hij
  apply Fin.ext
  have he := congrArg Fin.val hij
  change 2 * i.val + p = 2 * j.val + p at he
  omega

private theorem parityStart_surj {m p : ℕ} (hp : p < 2) {i : Col m} (hi : i ∈ paritySet m p) :
    ∃ e, parityStart hp e = i := by
  have h := mem_paritySet.mp hi
  have his := i.isLt
  refine ⟨⟨i.val / 2, by omega⟩, Fin.ext ?_⟩
  change 2 * (i.val / 2) + p = i.val
  omega

private theorem paritySet_card {m p : ℕ} (hp : p < 2) : (paritySet m p).card = m := by
  suffices (Finset.univ : Finset (Fin m)).card = (paritySet m p).card by simpa using this.symm
  refine Finset.card_bij (fun e _ => parityStart hp e) (fun e _ => parityStart_mem hp e) ?_ ?_
  · intro a _ b _ h
    exact parityStart_injective hp h
  · intro i hi
    obtain ⟨e, h⟩ := parityStart_surj hp hi
    exact ⟨e, Finset.mem_univ _, h⟩

private def cycleProduct {m : ℕ} {R : Type*} [CommRing R] (hm : 2 ≤ m)
    (p : ℕ) (Z : Chart R m) : R :=
  ∏ i ∈ paritySet m p, minor Z i (step hm i)

private theorem oddProduct_cycle {m : ℕ} {R : Type*} [CommRing R] (hm : 2 ≤ m)
    (Z : Chart R m) : oddProduct Z = cycleProduct hm 0 Z := by
  unfold oddProduct cycleProduct
  let hp : (0 : ℕ) < 2 := by decide
  refine Finset.prod_nbij (parityStart hp) (fun e _ => parityStart_mem hp e)
    ((parityStart_injective hp).injOn) ?_ ?_
  · intro i hi
    obtain ⟨e, he⟩ := parityStart_surj hp hi
    exact ⟨e, Finset.mem_univ e, he⟩
  · intro e _
    change minor Z (oddVertex (e, false)) (oddVertex (e, true)) =
      minor Z (oddVertex (e, false)) (step hm (oddVertex (e, false)))
    rw [odd_forward hm]

private def evenStart {m : ℕ} (e : Fin m) : Col m :=
  if e.val = 0 then evenVertex (e, true) else evenVertex (e, false)

private theorem evenStart_val {m : ℕ} (e : Fin m) :
    (evenStart e).val = if e.val = 0 then 2*m-1 else 2*e.val-1 := by
  by_cases h : e.val = 0 <;> simp [evenStart, evenVertex, h]

private theorem evenProduct_cycle {m : ℕ} {R : Type*} [CommRing R] (hm : 2 ≤ m)
    (Z : Chart R m) : evenProduct Z = -cycleProduct hm 1 Z := by
  have horient (e : Fin m) :
      minor Z (evenVertex (e, false)) (evenVertex (e, true)) =
        (if e.val = 0 then (-1 : R) else 1) * minor Z (evenStart e) (step hm (evenStart e)) := by
    by_cases h : e.val = 0
    · simp [evenStart, h, even_closing hm e h]
      exact minor_swap Z _ _
    · simp [evenStart, h, even_forward hm e h]
  have hreindex : (∏ e : Fin m, minor Z (evenStart e) (step hm (evenStart e))) =
      cycleProduct hm 1 Z := by
    unfold cycleProduct
    refine Finset.prod_nbij evenStart ?_ ?_ ?_ (fun _ _ => rfl)
    · intro e _
      have h := e.isLt
      rw [mem_paritySet, evenStart_val]
      split <;> omega
    · intro a _ b _ he
      have ha := a.isLt
      have hb := b.isLt
      have h := congrArg Fin.val he
      rw [evenStart_val, evenStart_val] at h
      apply Fin.ext
      split at h <;> split at h <;> omega
    · intro i hi
      have hpar := mem_paritySet.mp hi
      have h := i.isLt
      by_cases hz : i.val + 1 = 2*m
      · let e : Fin m := ⟨0, by omega⟩
        refine ⟨e, Finset.mem_univ e, Fin.ext ?_⟩
        rw [evenStart_val, ite_eq_left rfl]
        omega
      · let e : Fin m := ⟨(i.val+1)/2, by omega⟩
        have he : e.val ≠ 0 := by dsimp [e]; omega
        refine ⟨e, Finset.mem_univ e, Fin.ext ?_⟩
        rw [evenStart_val, ite_eq_right he]
        dsimp [e]
        omega
  have hsign : (∏ e : Fin m, if e.val = 0 then (-1 : R) else 1) = -1 := by
    let e : Fin m := ⟨0, by omega⟩
    rw [Finset.prod_eq_single e]
    · rfl
    · intro x _ hx
      exact ite_eq_right (fun he => hx (Fin.ext he))
    · simp
  simp only [evenProduct, horient, Finset.prod_mul_distrib, hsign, hreindex, neg_one_mul]

private theorem val_add_parity {m : ℕ} (a b : Col m) :
    (a + b).val % 2 = (a.val + b.val) % 2 := by
  have ha := a.isLt
  have hb := b.isLt
  rw [Fin.val_add_eq_ite]
  split <;> omega

private theorem val_sub_parity {m : ℕ} (a b : Col m) :
    (a - b).val % 2 = (a.val + b.val) % 2 := by
  have h := Fin.intCast_val_sub_eq_sub_add_ite a b
  have ha := a.isLt
  have hb := b.isLt
  split at h <;> omega

private theorem cycleProduct_transport {m : ℕ} {R : Type*} [CommRing R] (hm : 2 ≤ m)
    (Z W : Chart R m) (τ : Col m → Col m) (hτ : Function.Bijective τ)
    (ε : ℕ) (s : R)
    (hpar : ∀ i, (τ i).val % 2 = (i.val % 2 + ε) % 2)
    (hedge : ∀ i, minor W i (step hm i) = s * minor Z (τ i) (step hm (τ i)))
    (p : ℕ) (hp : p < 2) :
    cycleProduct hm p W = s ^ m * cycleProduct hm ((p + ε) % 2) Z := by
  unfold cycleProduct
  simp only [hedge, Finset.prod_mul_distrib, Finset.prod_const, paritySet_card hp]
  congr 1
  refine Finset.prod_nbij τ ?_ hτ.1.injOn ?_ (fun _ _ => rfl)
  · intro i hi
    rw [mem_paritySet, hpar, mem_paritySet.mp hi]
  · intro j hj
    obtain ⟨i, rfl⟩ := hτ.2 j
    have h := mem_paritySet.mp hj
    rw [hpar i] at h
    exact ⟨i, mem_paritySet.mpr (by omega), rfl⟩

private theorem level_iff_cycle_sum {m : ℕ} {R : Type*} [CommRing R] (hm : 2 ≤ m)
    (Z : Chart R m) :
    evenProduct Z = oddProduct Z ↔ cycleProduct hm 0 Z + cycleProduct hm 1 Z = 0 := by
  rw [evenProduct_cycle hm, oddProduct_cycle hm, eq_comm, ← add_eq_zero_iff_eq_neg]

theorem dihedral_preservesLevel {m : ℕ} (hm : 2 ≤ m) (σ : Equiv.Perm (Col m))
    (h : Dihedral σ) : PreservesLevel σ := by
  have : NeZero (2*m) := ⟨by omega⟩
  intro Z _ hZ
  have hsum := (level_iff_cycle_sum hm Z).mp hZ
  apply (level_iff_cycle_sum hm (reorder σ Z)).mpr
  obtain ⟨a, ha | ha⟩ := h
  · have hτ (i : Col m) : (σ i).val % 2 = (i.val % 2 + a.val % 2) % 2 := by
      rw [ha, val_add_parity]
      omega
    have hedge (i : Col m) :
        minor (reorder σ Z) i (step hm i) = 1 * minor Z (σ i) (step hm (σ i)) := by
      have hnext : σ (step hm i) = step hm (σ i) := by
        simp [ha, step, add_assoc]
      change minor Z (σ i) (σ (step hm i)) = _
      rw [hnext, one_mul]
    have he := cycleProduct_transport hm Z (reorder σ Z) σ σ.bijective (a.val % 2) 1 hτ hedge
    rw [he 0 (by decide), he 1 (by decide), one_pow, one_mul, one_mul]
    have hp : a.val % 2 = 0 ∨ a.val % 2 = 1 := by omega
    rcases hp with hp | hp
    · simpa [hp] using hsum
    · simpa [hp, add_comm] using hsum
  · let τ : Col m → Col m := fun i => σ (step hm i)
    have hb : Function.Bijective τ := by
      refine ⟨?_, ?_⟩
      · intro i j hij
        exact add_right_cancel (σ.injective hij)
      · intro j
        obtain ⟨i, rfl⟩ := σ.surjective j
        refine ⟨i - second hm, ?_⟩
        simp [τ, step]
    let ε := (a - second hm).val % 2
    have hpar (i : Col m) : (τ i).val % 2 = (i.val % 2 + ε) % 2 := by
      have hτ : τ i = (a - second hm) - i := by simp [τ, ha, step, sub_eq_add_neg]; abel
      rw [hτ, val_sub_parity]
      dsimp [ε]
      omega
    have hedge (i : Col m) :
        minor (reorder σ Z) i (step hm i) = -1 * minor Z (τ i) (step hm (τ i)) := by
      have hnext : σ i = step hm (τ i) := by simp [τ, ha, step, sub_eq_add_neg]; abel
      change minor Z (σ i) (τ i) = _
      rw [minor_swap Z (σ i), hnext, neg_one_mul]
    have he := cycleProduct_transport hm Z (reorder σ Z) τ hb ε (-1) hpar hedge
    rw [he 0 (by decide), he 1 (by decide), ← mul_add]
    suffices hz : cycleProduct hm ((0 + ε) % 2) Z +
        cycleProduct hm ((1 + ε) % 2) Z = 0 by rw [hz, mul_zero]
    have hp : ε = 0 ∨ ε = 1 := by dsimp [ε]; omega
    rcases hp with hp | hp
    · simpa [hp] using hsum
    · simpa [hp, add_comm] using hsum

end D5.S3.Geometry.KozakiKakei
