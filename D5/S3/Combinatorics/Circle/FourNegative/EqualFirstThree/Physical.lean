/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstThree/Physical
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-physical-realization)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical realization and exact packet facts consumed by the equal-first-three schedules. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Source
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
import D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventual

/-! All values are actual centered source values, and labels are retained with multiplicity. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
open SourceWidth PeriodicShortening RunFirstEarTransport
open private seed_bounds from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source
open private seed eta vcoef wcoef xcoef Table paired_table
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Source
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private four_strip from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private chainMask chainMask_sum chainMask_partition four_mask_inventory
  from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventual
open private mask_labels mask_labels_mem
  from D5.S3.Combinatorics.Circle.ThreeBitSource

private def rank (s d : ℕ) : ℕ := 3 * s + d
private def amplitude (s : ℕ) : ℕ := 1 + 2 ^ s + 2 ^ (2 * s) + 2 ^ (3 * s)
private def oldRow (s d : ℕ) (i : ℕ) : ℤ :=
  centered (modulus (rank s d)) ((2 : ℤ) ^ i * amplitude s)
private def newRow (s d : ℕ) (i : ℕ) : ℤ :=
  centered (modulus (rank s d + 1)) ((2 : ℤ) ^ i * (2 * (amplitude s : ℤ)))

private theorem source_data (s d : ℕ) (hs : 2 ≤ s) (hd : 2 ≤ d) :
    let R : ℤ := 2 ^ s
    let D : ℤ := 2 ^ d
    let N := modulus (rank s d)
    Table s d R D N (oldRow s d) (newRow s d) ∧
    (4 ≤ R ∧ 4 ≤ D) ∧
    (amplitude s : ℤ) = seed R ∧
    N = D * R * R * R - 1 ∧
    modulus (rank s d + 1) = 2 * N + 1 ∧
    0 < seed R ∧ seed R < N ∧ newRow s d (rank s d) = seed R := by
  dsimp only
  let R : ℤ := 2 ^ s
  let D : ℤ := 2 ^ d
  let N := modulus (rank s d)
  have hR : (4 : ℤ) ≤ R := by
    simpa [R] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hs
  have hD : (4 : ℤ) ≤ D := by
    simpa [D] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hd
  have hA : (amplitude s : ℤ) = seed R := by
    simp only [amplitude, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
    rw [show 2 * s = s + s by omega, show 3 * s = s + s + s by omega]
    simp only [pow_add, seed, R]
  have hN : N = D * R * R * R - 1 := by
    dsimp [N, modulus, rank, D, R]
    rw [show 3 * s + d = d + s + s + s by omega]
    simp only [pow_add]
  have hM : modulus (rank s d + 1) = 2 * N + 1 := by
    dsimp [N, modulus]; rw [pow_succ]; ring
  have hb : 0 < seed R ∧ seed R < N := by
    have h := seed_bounds R R R D hR hR hR hD
    change 1 ≤ seed R ∧ seed R < R * R * R * D - 1 at h
    have he : R * R * R * D - 1 = N := by rw [hN]; ring
    rw [he] at h
    exact ⟨by omega, h.2⟩
  have tab := paired_table s d hs hd
  have htab : Table s d R D N (oldRow s d) (newRow s d) := by
    change Table s d R D N
      (fun i => centered N ((2 : ℤ) ^ i * amplitude s))
      (fun i => centered (modulus (rank s d + 1)) ((2 : ℤ) ^ i * (2 * (amplitude s : ℤ))))
    have ht : (amplitude s : ℤ) =
        1 + (2 : ℤ) ^ s + 2 ^ (2*s) + 2 ^ (3*s) := by
      simp only [amplitude, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
    rw [ht]
    exact tab
  refine ⟨htab, ⟨hR, hD⟩, hA, hN, hM, hb.1, hb.2, ?_⟩
  unfold newRow
  rw [show (2 : ℤ) ^ rank s d * (2 * (amplitude s : ℤ)) =
    2 ^ (rank s d + 1) * amplitude s by rw [pow_succ]; ring,
    centered_full_period (rank s d + 1) (amplitude s), hA]
  change centered (modulus (rank s d + 1)) (seed R) = seed R
  unfold centered
  rw [hM]
  have hh : (2 * N + 1) / 2 = N := by omega
  rw [hh, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

private theorem coeff_positive (R D : ℤ) (hR : 4 ≤ R) (hD : 4 ≤ D) :
    0 ≤ seed R ∧ 0 ≤ 2 * seed R ∧
    0 ≤ vcoef R D ∧ 0 ≤ 2 * vcoef R D - 1 ∧
    0 ≤ wcoef R D ∧ 0 ≤ 2 * wcoef R D - R - 1 ∧
    0 ≤ xcoef R D ∧ 0 ≤ 2 * xcoef R D - eta R := by
  have heW : 2 * wcoef R D - R - 1 =
      2 * D * R * R + (2 * D + 1) * R + 1 := by dsimp [wcoef]; ring
  have heX : 2 * xcoef R D - eta R =
      (2 * D + 1) * R * R + R + 1 := by dsimp [xcoef, eta]; ring
  rw [heW, heX]
  dsimp [seed, vcoef, wcoef, xcoef]
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · have he : 2 * (D * R * R + D * R + D + 1) - 1 =
        2 * D * R * R + 2 * D * R + 2 * D + 1 := by ring
    rw [he]; positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

private theorem range_positive (f : ℕ → ℤ) (off len : ℕ) (F : ℤ)
    (hF : 0 ≤ F) (hf : ∀ e < len, f (off + e) = (2 : ℤ) ^ e * F) :
    ∀ i ∈ List.range' off len, 0 ≤ f i := by
  intro i hi
  have hb := List.mem_range'_1.mp hi
  have he : off + (i - off) = i := by omega
  rw [←he, hf (i - off) (by omega)]
  positivity

private theorem mask_data (len off m : ℕ) (hm : m < 2 ^ len)
    (f : ℕ → ℤ) (F : ℤ) (hF : 0 ≤ F)
    (hf : ∀ e < len, f (off + e) = (2 : ℤ) ^ e * F) :
    ((chainMask len off m).map f).sum = (m : ℤ) * F ∧
      ∀ i ∈ chainMask len off m, 0 ≤ f i := by
  refine ⟨chainMask_sum len off m hm f F hf, ?_⟩
  intro i hi
  simp only [chainMask, dite_eq_left hm, Finset.mem_toList] at hi
  obtain ⟨e, he, _, rfl⟩ := (mask_labels_mem len off m i hm).mp hi
  rw [hf e he]
  positivity

private theorem old_total (s d : ℕ) (hs : 2 ≤ s) (hd : 2 ≤ d)
    (word : List ℕ) (hp : word.Perm (List.range (rank s d))) :
    (word.map (oldRow s d)).sum = 0 :=
  (hp.map _).sum_eq.trans (ThreeNegativeEqualOuterSourceBridge.source_zero
    (rank s d) (amplitude s) (by dsimp [rank]; omega))

private theorem inserted_perm (k : ℕ) (P T : List ℕ)
    (hp : (P ++ T).Perm (List.range k)) :
    (P ++ k :: T).Perm (List.range (k + 1)) := by
  apply Multiset.coe_eq_coe.mp
  rw [List.range_succ]
  have h := Multiset.coe_eq_coe.mpr hp
  simp only [← Multiset.coe_add] at h
  change (P : Multiset ℕ) + ({k} + (T : Multiset ℕ)) =
    (List.range k : Multiset ℕ) + {k}
  rw [show (P : Multiset ℕ) + ({k} + (T : Multiset ℕ)) =
      (P : Multiset ℕ) + (T : Multiset ℕ) + {k} by ac_rfl, h]

private theorem new_total (s d : ℕ) (hs : 2 ≤ s) (hd : 2 ≤ d)
    (word : List ℕ) (hp : word.Perm (List.range (rank s d + 1))) :
    (word.map (newRow s d)).sum = 0 := by
  have h := (hp.map _).sum_eq.trans (ThreeNegativeEqualOuterSourceBridge.source_zero
    (rank s d + 1) (2 * amplitude s) (by dsimp [rank]; omega))
  change (List.map (fun i : ℕ => centered (modulus (rank s d + 1))
    ((2 : ℤ) ^ i * (2 * (amplitude s : ℤ)))) word).sum = 0
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

private theorem finish (s d : ℕ) (hs : 2 ≤ s) (hd : 2 ≤ d)
    (P T : List ℕ) (hp : (P ++ T).Perm (List.range (rank s d)))
    (hold : InStrip (oldRow s d) (modulus (rank s d) / 2) 0 (P ++ T))
    (hnew : InStrip (newRow s d) (modulus (rank s d + 1) / 2) 0 (P ++ rank s d :: T)) :
    ∃ sigma : List (Fin (rank s d)), ∃ cut : ℕ, cut ≤ rank s d ∧
      OriginalOrder (rank s d) (amplitude s) sigma ∧
      OriginalOrder (rank s d + 1) (2 * amplitude s) (earWord (rank s d) sigma cut) := by
  have hk : 0 < rank s d := by dsimp [rank]; omega
  refine ⟨(P ++ T).map (label (rank s d) hk), P.length, ?_, ?_, ?_⟩
  · have hl := hp.length_eq
    simp only [List.length_append, List.length_range] at hl
    omega
  · exact lift_order (rank s d) (amplitude s) hk (P ++ T) hp hold
      (ThreeNegativeEqualOuterSourceBridge.source_zero _ _ (by dsimp [rank]; omega))
  · rw [marked_word (rank s d) P.length hk P T rfl hp]
    apply lift_order (rank s d + 1) (2 * amplitude s) (by omega)
      (P ++ rank s d :: T) (inserted_perm _ _ _ hp)
    · change InStrip (fun i => centered (modulus (rank s d + 1))
        ((2 : ℤ) ^ i * (2 * (amplitude s : ℤ)))) _ _ _ at hnew
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnew
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero _ _ (by dsimp [rank]; omega)

end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
