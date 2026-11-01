/- GID: D5/S1/Recurrence/KRegularInterleaving
   generality: I
   mirror-B: D5/B/S1/Recurrence/KRegularInterleaving
   mirror-E: none(waiver:noncomputational-general-theorem)
   anchors: []
   utility: none
   digest: Every finite interleaving of integer-valued k-regular residue streams is k-regular. -/

import D5.S1.Recurrence.KRegularAffineSubsequence
import Mathlib.Data.Nat.ModEq

/-!
# Finite interleavings of integer k-regular sequences

The full, unbounded kernel and integer finite-generation predicate are the
native definitions in `SobolewskiUlasParityPositions`. The construction uses
one finite envelope of linear insertion images for all exponents at once.
Affine-subsequence closure is supplied by `KRegularAffineSubsequence`.

Shallit, *Corrected proof of Theorem 2.7 in Allouche and Shallit (1992)*,
Theorem 1, first proof, PDF pages 1–2, treats every width a ≥ 1 and arbitrary
gcd(a,k). Only the integer-coefficient statement is asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.KRegularInterleaving

open D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions (kKernel IsKRegular)
open D5.S1.Recurrence.KRegularAffineSubsequence (is_k_regular_affine_subsequence)

private def zeroInsert (a i : ℕ) : (ℕ → ℤ) →ₗ[ℤ] (ℕ → ℤ) where
  toFun f n := if n % a = i then f (n / a) else 0
  map_add' f g := by
    funext n
    by_cases h : n % a = i <;> simp [h]
  map_smul' c f := by
    funext n
    by_cases h : n % a = i <;> simp [h]

private theorem masked_kernel_form (K a i c : ℕ) (f : ℕ → ℤ)
    (hK : 0 < K) (ha : 0 < a) (hc : c < K) :
    (fun n => zeroInsert a i f (K * n + c)) = 0 ∨
      ∃ r < a / Nat.gcd K a, ∃ m < K / Nat.gcd K a,
        (fun n => zeroInsert a i f (K * n + c)) =
          zeroInsert (a / Nat.gcd K a) r (fun n => f (K / Nat.gcd K a * n + m)) := by
  let g := Nat.gcd K a
  let N := a / g
  let M := K / g
  have hga : g ∣ a := Nat.gcd_dvd_right K a
  have hgK : g ∣ K := Nat.gcd_dvd_left K a
  have hN : 0 < N := Nat.div_pos (Nat.le_of_dvd ha hga) (Nat.gcd_pos_of_pos_left a hK)
  have hKN : K * N = a * M := by
    dsimp [N, M]
    calc
      K * (a / g) = ((K / g) * g) * (a / g) := by rw [Nat.div_mul_cancel hgK]
      _ = a * (K / g) := by rw [mul_assoc, Nat.mul_div_cancel' hga, mul_comm]
  have hperiod (n : ℕ) : (K * n + c) % a = (K * (n % N) + c) % a := by
    have hn := Nat.div_add_mod n N
    have heq : K * n + c = a * (M * (n / N)) + (K * (n % N) + c) := by
      calc
        K * n + c = K * (N * (n / N) + n % N) + c := by rw [hn]
        _ = (K * N) * (n / N) + (K * (n % N) + c) := by ring
        _ = _ := by rw [hKN]; ring
    rw [heq]
    simp [Nat.add_mod]
  by_cases hs : ∃ n, (K * n + c) % a = i
  · obtain ⟨n₁, hn₁⟩ := hs
    let r := n₁ % N
    have hr : r < N := Nat.mod_lt _ hN
    have hsr : (K * r + c) % a = i := by
      simpa [r] using (hperiod n₁).symm.trans hn₁
    let m := (K * r + c) / a
    have hm : m < M := by
      apply (Nat.div_lt_iff_lt_mul ha).2
      have hle := Nat.mul_le_mul_left K (Nat.succ_le_iff.mpr hr)
      nlinarith
    have hsupport (n : ℕ) : (K * n + c) % a = i ↔ n % N = r := by
      constructor
      · intro hn
        have heq : K * n + c ≡ K * r + c [MOD a] := hn.trans hsr.symm
        have hmul := Nat.ModEq.add_right_cancel' c heq
        have hcan := hmul.cancel_left_div_gcd ha
        change n % (a / Nat.gcd a K) = r % (a / Nat.gcd a K) at hcan
        have hcan' : n % N = r % N := by
          simpa only [N, g, Nat.gcd_comm a K] using hcan
        simpa only [Nat.mod_eq_of_lt hr] using hcan'
      · intro hn
        rw [hperiod n, hn, hsr]
    right
    refine ⟨r, hr, m, hm, ?_⟩
    funext n
    change (if (K * n + c) % a = i then f ((K * n + c) / a) else 0) =
      if n % N = r then f (M * (n / N) + m) else 0
    by_cases hn : n % N = r
    · rw [ite_eq_left hn, ite_eq_left ((hsupport n).2 hn)]
      congr 1
      have hbase : K * r + c = a * m + i := by
        have hb := Nat.div_add_mod (K * r + c) a
        dsimp [m]
        omega
      have hidx : K * n + c = a * (M * (n / N) + m) + i := by
        have hd := Nat.div_add_mod n N
        rw [hn] at hd
        calc
          K * n + c = K * (N * (n / N) + r) + c := by rw [hd]
          _ = (K * N) * (n / N) + (K * r + c) := by ring
          _ = _ := by rw [hKN, hbase]; ring
      have hi : i < a := hsr ▸ Nat.mod_lt (K * r + c) ha
      rw [hidx, Nat.mul_add_div ha, Nat.div_eq_of_lt hi, Nat.add_zero]
    · rw [ite_eq_right hn, ite_eq_right (mt ((hsupport n).1) hn)]
  · left
    funext n
    have hn : (K * n + c) % a ≠ i := fun h => hs ⟨n, h⟩
    simp [zeroInsert, hn]

private theorem masked_kernel_envelope (k a i : ℕ) (f : ℕ → ℤ)
    (hk : 2 ≤ k) (ha : 1 ≤ a) (hf : IsKRegular k f) :
    ∃ W : Submodule ℤ (ℕ → ℤ), W.FG ∧
      Submodule.span ℤ (kKernel k (zeroInsert a i f)) ≤ W := by
  classical
  let C := {g : ℕ // ∃ e : ℕ, Nat.gcd (k ^ e) a = g}
  have hfinite : {g : ℕ | ∃ e : ℕ, Nat.gcd (k ^ e) a = g}.Finite := by
    apply (Set.finite_Iic a).subset
    rintro g ⟨e, rfl⟩
    exact Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right (k ^ e) a)
  have : Finite C := hfinite.to_subtype
  let t (g : C) : ℕ := Nat.find g.property
  let u (g : C) : ℕ := k ^ t g / g.val
  let N (g : C) : ℕ := a / g.val
  have hreal (g : C) : Nat.gcd (k ^ t g) a = g.val := Nat.find_spec g.property
  have hu (g : C) : 1 ≤ u g := by
    have hg : g.val ∣ k ^ t g := hreal g ▸ Nat.gcd_dvd_left (k ^ t g) a
    have hpos : 0 < k ^ t g := pow_pos (by omega) _
    have hgpos : 0 < g.val := hreal g ▸ Nat.gcd_pos_of_pos_left a hpos
    exact Nat.div_pos (Nat.le_of_dvd hpos hg) hgpos
  let H (g : C) (d : Fin (u g)) : Submodule ℤ (ℕ → ℤ) :=
    Submodule.span ℤ (kKernel k (fun n => f (u g * n + d.val)))
  let W : Submodule ℤ (ℕ → ℤ) :=
    ⨆ g : C, ⨆ d : Fin (u g), ⨆ r : Fin (N g),
      (H g d).map (zeroInsert (N g) r.val)
  have hW : W.FG := by
    apply Submodule.fg_iSup
    intro g
    apply Submodule.fg_iSup
    intro d
    apply Submodule.fg_iSup
    intro r
    exact (is_k_regular_affine_subsequence k (u g) d.val f hk (hu g) hf).map _
  refine ⟨W, hW, ?_⟩
  apply Submodule.span_le.mpr
  rintro w ⟨e, c, hc, rfl⟩
  have hke : 0 < k ^ e := pow_pos (by omega) _
  rcases masked_kernel_form (k ^ e) a i c f hke (by omega) hc with hz | ⟨r, hr, m, hm, heq⟩
  · rw [hz]
    exact Submodule.zero_mem _
  · let g : C := ⟨Nat.gcd (k ^ e) a, e, rfl⟩
    have ht : t g ≤ e := Nat.find_min' g.property rfl
    have hg : g.val ∣ k ^ t g := hreal g ▸ Nat.gcd_dvd_left (k ^ t g) a
    have hfactor : k ^ e / g.val = k ^ (e - t g) * u g := by
      have he : k ^ e = k ^ (e - t g) * k ^ t g := by
        rw [← pow_add, Nat.sub_add_cancel ht]
      rw [he, Nat.mul_div_assoc _ hg]
    have hum : 0 < u g := by have := hu g; omega
    let d : Fin (u g) := ⟨m % u g, Nat.mod_lt _ hum⟩
    let q := m / u g
    have hq : q < k ^ (e - t g) := by
      apply (Nat.div_lt_iff_lt_mul hum).2
      change m < k ^ e / g.val at hm
      rwa [hfactor] at hm
    let v : ℕ → ℤ := fun n => f (k ^ e / g.val * n + m)
    have hv : v ∈ H g d := by
      apply Submodule.subset_span
      refine ⟨e - t g, q, hq, ?_⟩
      funext n
      have hd := Nat.div_add_mod m (u g)
      dsimp [v, d, q]
      congr 1
      rw [hfactor]
      nlinarith only [hd]
    have hmapped : zeroInsert (N g) r v ∈ (H g d).map (zeroInsert (N g) r) :=
      ⟨v, hv, rfl⟩
    rw [heq]
    exact Submodule.mem_iSup_of_mem g
      (Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem (⟨r, hr⟩ : Fin (N g)) hmapped))

/-- Every finite interleaving of integer-valued k-regular residue streams is
k-regular, without a coprimality or finite-kernel hypothesis. -/
theorem is_k_regular_interleaving (k a : ℕ) (s : ℕ → ℤ)
    (hk : 2 ≤ k) (ha : 1 ≤ a)
    (hs : ∀ i : ℕ, i < a → IsKRegular k (fun n => s (a * n + i))) :
    IsKRegular k s := by
  classical
  let f (i : Fin a) : ℕ → ℤ := fun n => s (a * n + i.val)
  let T (i : Fin a) : ℕ → ℤ := zeroInsert a i.val (f i)
  have hT (i : Fin a) : ∃ W : Submodule ℤ (ℕ → ℤ), W.FG ∧
      Submodule.span ℤ (kKernel k (T i)) ≤ W :=
    masked_kernel_envelope k a i.val (f i) hk ha (hs i.val i.isLt)
  choose W hW hTW using hT
  have hsum (n : ℕ) : (∑ i : Fin a, T i n) = s n := by
    let j : Fin a := ⟨n % a, Nat.mod_lt n (by omega)⟩
    rw [Finset.sum_eq_single j]
    · simp [T, f, zeroInsert, j, Nat.div_add_mod]
    · intro b _ hbj
      have hb : n % a ≠ b.val := by
        intro heq
        apply hbj
        apply Fin.ext
        exact heq.symm
      simp [T, zeroInsert, hb]
    · simp
  let V : Submodule ℤ (ℕ → ℤ) := ⨆ i : Fin a, W i
  have hV : V.FG := Submodule.fg_iSup _ hW
  apply hV.of_le
  apply Submodule.span_le.mpr
  rintro w ⟨e, c, hc, rfl⟩
  have heq : (fun n => s (k ^ e * n + c)) =
      ∑ i : Fin a, (fun n => T i (k ^ e * n + c)) := by
    funext n
    simpa only [Finset.sum_apply] using (hsum (k ^ e * n + c)).symm
  rw [heq]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.mem_iSup_of_mem i
  exact hTW i (Submodule.subset_span ⟨e, c, hc, rfl⟩)

end D5.S1.Recurrence.KRegularInterleaving
