/- GID: D5/S1/Phase/Interference/DedekindReciprocityLattice
   generality: I
   mirror-B: D5/B/S1/Phase/Interference/DedekindReciprocityLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A coprime lattice exchange evaluates the weighted floor sums. -/

/- Library-search audit trail (2026-08-14):
   * The elementary residue sums are imported from `DedekindReciprocityFiniteSums`.
   * Pinned Gauss-Eisenstein lemmas cover prime half-ranges, not this general rectangle.
   * The weighted identity is proved by an explicit filtered-product double count.
-/

import D5.S1.Phase.Interference.DedekindReciprocityFiniteSums

namespace D5.S1.Phase.Interference.DedekindReciprocityLattice

open D5.S1.Phase.Interference.DedekindReciprocityFiniteSums

/-- The weighted floor sum that appears after applying Euclidean division to
the residue cross term. -/
def weightedFloorSum (d c : Nat) : Rat :=
  ∑ k ∈ Finset.Ico 1 c,
    (k : Rat) * (((k * d) / c : Nat) : Rat)

/-- The residue cross term in the expanded finite Dedekind sum. -/
def residueCrossTerm (d c : Nat) : Rat :=
  ∑ k ∈ Finset.Ico 1 c,
    (k : Rat) * (((k * d) % c : Nat) : Rat)

/-- The positive difference below the diagonal in the coprime
`(c - 1) × (d - 1)` lattice rectangle. -/
def latticeDifference (d c : Nat) : Rat :=
  (Finset.Ico 1 c).sum fun k ↦
    ((Finset.Ico 1 d).filter (fun j ↦ j * c < k * d)).sum fun j ↦
      ((k * d : Nat) : Rat) - ((j * c : Nat) : Rat)

/-- Sum of the first coordinate over the lattice points below the diagonal. -/
def belowFirstWeight (d c : Nat) : Rat :=
  (Finset.Ico 1 c).sum fun k ↦
    ((Finset.Ico 1 d).filter (fun j ↦ j * c < k * d)).sum fun _ ↦
      (k : Rat)

/-- Sum of the second coordinate over the lattice points below the diagonal. -/
def belowSecondWeight (d c : Nat) : Rat :=
  (Finset.Ico 1 c).sum fun k ↦
    ((Finset.Ico 1 d).filter (fun j ↦ j * c < k * d)).sum fun j ↦
      (j : Rat)

/-- A coprime lattice rectangle has no point on the diagonal `j*c = k*d`
away from its boundary. -/
theorem coprime_rectangle_no_diagonal {c d k j : Nat} (hcd : c.Coprime d)
    (hj0 : 0 < j) (hjd : j < d) :
    j * c ≠ k * d := by
  intro heq
  have hdvd : d ∣ j * c := by
    rw [heq]
    exact ⟨k, Nat.mul_comm k d⟩
  have hdvdj : d ∣ j := (hcd.symm.dvd_mul_right).mp hdvd
  exact (not_le_of_gt hjd) (Nat.le_of_dvd hj0 hdvdj)

/-- In a coprime rectangle, the entries below a fixed row are exactly
`1, ..., (k*d)/c`. -/
theorem filter_below_eq_Ico {c d k : Nat} (hc : 0 < c) (hd : 0 < d)
    (hcd : c.Coprime d) (hk : k ∈ Finset.Ico 1 c) :
    (Finset.Ico 1 d).filter (fun j ↦ j * c < k * d) =
      Finset.Ico 1 ((k * d) / c + 1) := by
  ext j
  have hkBounds := Finset.mem_Ico.mp hk
  have hquotLt : (k * d) / c < d := by
    rw [Nat.div_lt_iff_lt_mul hc]
    simpa [Nat.mul_comm] using (Nat.mul_lt_mul_right hd).mpr hkBounds.2
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hj0, hjd⟩, hjlt⟩
    refine ⟨hj0, Nat.lt_succ_iff.mpr ?_⟩
    exact (Nat.le_div_iff_mul_le hc).mpr hjlt.le
  · rintro ⟨hj0, hjq⟩
    have hjle : j ≤ (k * d) / c := Nat.lt_succ_iff.mp hjq
    have hjd : j < d := lt_of_le_of_lt hjle hquotLt
    have hjcle : j * c ≤ k * d := (Nat.le_div_iff_mul_le hc).mp hjle
    refine ⟨⟨hj0, hjd⟩, lt_of_le_of_ne hjcle ?_⟩
    exact coprime_rectangle_no_diagonal hcd hj0 hjd

/-- The sum of the positive differences in one row, expressed through its
quotient and remainder. -/
theorem row_lattice_sum (w c : Nat) (hc : 0 < c) :
    (Finset.Ico 1 (w / c + 1)).sum (fun j ↦
        (w : Rat) - ((j * c : Nat) : Rat)) =
      ((w : Rat) ^ 2 - ((w % c : Nat) : Rat) ^ 2) /
          (2 * (c : Rat)) -
        ((w : Rat) - ((w % c : Nat) : Rat)) / 2 := by
  have hcRat : (c : Rat) ≠ 0 := by exact_mod_cast hc.ne'
  have hdecomp :
      (w : Rat) = ((w % c : Nat) : Rat) +
        (c : Rat) * (((w / c : Nat) : Rat)) := by
    exact_mod_cast (Nat.mod_add_div w c).symm
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul]
  simp_rw [Nat.cast_mul]
  rw [← Finset.sum_mul, sum_Ico_cast]
  rw [hdecomp]
  field_simp
  push_cast
  ring

/-- A weighted floor sum counts the first coordinate of every lattice point
strictly below the diagonal. -/
theorem weightedFloorSum_eq_lattice_count {d c : Nat} (hc : 0 < c)
    (hd : 0 < d) (hcd : c.Coprime d) :
    weightedFloorSum d c = belowFirstWeight d c := by
  unfold weightedFloorSum belowFirstWeight
  apply Finset.sum_congr rfl
  intro k hk
  rw [filter_below_eq_Ico hc hd hcd hk]
  simp [Nat.card_Ico]
  ring

/-- The unweighted Gauss floor count over a coprime rectangle. -/
theorem sum_div_gauss {d c : Nat} (hc : 0 < c) (hcd : d.Coprime c) :
    ∑ k ∈ Finset.Ico 1 c, (((k * d) / c : Nat) : Rat) =
      ((c : Rat) - 1) * ((d : Rat) - 1) / 2 := by
  have hcRat : (c : Rat) ≠ 0 := by exact_mod_cast hc.ne'
  have hscaled :
      (c : Rat) *
          (∑ k ∈ Finset.Ico 1 c, (((k * d) / c : Nat) : Rat)) =
        (d : Rat) * ((c : Rat) * ((c : Rat) - 1) / 2) -
          (c : Rat) * ((c : Rat) - 1) / 2 := by
    rw [Finset.mul_sum]
    have hterm :
        (Finset.Ico 1 c).sum (fun k ↦
            (c : Rat) * (((k * d) / c : Nat) : Rat)) =
          (Finset.Ico 1 c).sum (fun k ↦
            ((k * d : Nat) : Rat) - (((k * d) % c : Nat) : Rat)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hdecomp :
          (((k * d) % c : Nat) : Rat) +
              (c : Rat) * (((k * d) / c : Nat) : Rat) =
            ((k * d : Nat) : Rat) := by
        exact_mod_cast Nat.mod_add_div (k * d) c
      linarith
    rw [hterm]
    rw [Finset.sum_sub_distrib]
    simp_rw [Nat.cast_mul]
    rw [← Finset.sum_mul, sum_Ico_cast, sum_mul_mod hc hcd]
    ring
  apply mul_left_cancel₀ hcRat
  rw [hscaled]
  ring

/-- The filtered lattice-difference sum can be evaluated row by row. -/
theorem latticeDifference_eq_row_sum {d c : Nat} (hc : 0 < c)
    (hd : 0 < d) (hcd : c.Coprime d) :
    latticeDifference d c =
      (Finset.Ico 1 c).sum (fun k ↦
        (Finset.Ico 1 ((k * d) / c + 1)).sum (fun j ↦
          ((k * d : Nat) : Rat) - ((j * c : Nat) : Rat))) := by
  unfold latticeDifference
  apply Finset.sum_congr rfl
  intro k hk
  rw [filter_below_eq_Ico hc hd hcd hk]

/-- The row evaluation and the elementary residue sums give a closed form
for the positive lattice difference. -/
theorem latticeDifference_closed {d c : Nat} (hc : 0 < c) (hd : 0 < d)
    (hcd : c.Coprime d) :
    latticeDifference d c =
      ((c : Rat) - 1) * ((d : Rat) - 1) *
        (2 * (c : Rat) * (d : Rat) - (c : Rat) - (d : Rat) - 1) / 12 := by
  have hcRat : (c : Rat) ≠ 0 := by exact_mod_cast hc.ne'
  rw [latticeDifference_eq_row_sum hc hd hcd]
  have hrows :
      (Finset.Ico 1 c).sum (fun k ↦
          (Finset.Ico 1 ((k * d) / c + 1)).sum (fun j ↦
            ((k * d : Nat) : Rat) - ((j * c : Nat) : Rat))) =
        (Finset.Ico 1 c).sum (fun k ↦
          (((k * d : Nat) : Rat) ^ 2 -
              (((k * d) % c : Nat) : Rat) ^ 2) /
                (2 * (c : Rat)) -
            (((k * d : Nat) : Rat) -
              (((k * d) % c : Nat) : Rat)) / 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact row_lattice_sum (k * d) c hc
  rw [hrows]
  have hsumW :
      (Finset.Ico 1 c).sum (fun k ↦ ((k * d : Nat) : Rat)) =
        (d : Rat) * ((c : Rat) * ((c : Rat) - 1) / 2) := by
    simp_rw [Nat.cast_mul]
    rw [← Finset.sum_mul, sum_Ico_cast]
    ring
  have hsumWsq :
      (Finset.Ico 1 c).sum (fun k ↦ ((k * d : Nat) : Rat) ^ 2) =
        (d : Rat) ^ 2 *
          (((c : Rat) - 1) * (c : Rat) * (2 * (c : Rat) - 1) / 6) := by
    calc
      (Finset.Ico 1 c).sum (fun k ↦ ((k * d : Nat) : Rat) ^ 2) =
          (Finset.Ico 1 c).sum (fun k ↦
            (d : Rat) ^ 2 * (k : Rat) ^ 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        push_cast
        ring
      _ = (d : Rat) ^ 2 *
          ((Finset.Ico 1 c).sum (fun k ↦ (k : Rat) ^ 2)) := by
        rw [Finset.mul_sum]
      _ = _ := by rw [sum_Ico_cast_sq]
  have hsumFormula :
      (Finset.Ico 1 c).sum (fun k ↦
          (((k * d : Nat) : Rat) ^ 2 -
              (((k * d) % c : Nat) : Rat) ^ 2) /
                (2 * (c : Rat)) -
            (((k * d : Nat) : Rat) -
              (((k * d) % c : Nat) : Rat)) / 2) =
        ((Finset.Ico 1 c).sum (fun k ↦ ((k * d : Nat) : Rat) ^ 2) -
            (Finset.Ico 1 c).sum (fun k ↦
              (((k * d) % c : Nat) : Rat) ^ 2)) /
              (2 * (c : Rat)) -
          ((Finset.Ico 1 c).sum (fun k ↦ ((k * d : Nat) : Rat)) -
            (Finset.Ico 1 c).sum (fun k ↦
              (((k * d) % c : Nat) : Rat))) / 2 := by
    rw [Finset.sum_sub_distrib]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [hsumFormula, hsumWsq, sum_mul_mod_sq hc hcd.symm, hsumW,
    sum_mul_mod hc hcd.symm]
  field_simp
  ring

/-- Splitting every positive lattice difference separates the two coordinate
weights. -/
theorem latticeDifference_eq_weights (d c : Nat) :
    latticeDifference d c =
      (d : Rat) * belowFirstWeight d c -
        (c : Rat) * belowSecondWeight d c := by
  unfold latticeDifference belowFirstWeight belowSecondWeight
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

/-- The two strict triangles partition a coprime lattice rectangle; the
second-coordinate weight below one diagonal is the first-coordinate weight
below the transposed diagonal. -/
theorem below_weights_partition {d c : Nat} (hc : 0 < c)
    (hcd : c.Coprime d) :
    belowSecondWeight d c + belowFirstWeight c d =
      ((c : Rat) - 1) * ((d : Rat) * ((d : Rat) - 1) / 2) := by
  have hswap :
      belowFirstWeight c d =
        (Finset.Ico 1 c).sum (fun k ↦
          ((Finset.Ico 1 d).filter (fun j ↦ k * d < j * c)).sum
            (fun j ↦ (j : Rat))) := by
    unfold belowFirstWeight
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  unfold belowSecondWeight
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  have hpointwise :
      (Finset.Ico 1 c).sum (fun k ↦
          (Finset.Ico 1 d).sum (fun j ↦
            if j * c < k * d then (j : Rat) else 0) +
          (Finset.Ico 1 d).sum (fun j ↦
            if k * d < j * c then (j : Rat) else 0)) =
        (Finset.Ico 1 c).sum (fun _ ↦
          (Finset.Ico 1 d).sum (fun j ↦ (j : Rat))) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hkBounds := Finset.mem_Ico.mp hk
    have hjBounds := Finset.mem_Ico.mp hj
    have hne := coprime_rectangle_no_diagonal (k := k) hcd
      hjBounds.1 hjBounds.2
    by_cases hlt : j * c < k * d
    · have hnlt : ¬k * d < j * c := by omega
      simp [hlt, hnlt]
    · have hgt : k * d < j * c := by omega
      simp [hlt, hgt]
  rw [hpointwise, sum_Ico_cast, Finset.sum_const, Nat.card_Ico]
  simp only [nsmul_eq_mul]
  have hcOne : 1 ≤ c := hc
  push_cast [Nat.cast_sub hcOne]
  ring

/-- Symmetric weighted-floor exchange obtained by double-counting the
coprime lattice rectangle. -/
theorem weightedFloorSum_exchange {d c : Nat} (hc : 0 < c) (hd : 0 < d)
    (hcd : c.Coprime d) :
    (d : Rat) * weightedFloorSum d c +
        (c : Rat) * weightedFloorSum c d =
      latticeDifference d c +
        (c : Rat) * ((c : Rat) - 1) *
          ((d : Rat) * ((d : Rat) - 1) / 2) := by
  rw [weightedFloorSum_eq_lattice_count hc hd hcd,
    weightedFloorSum_eq_lattice_count hd hc hcd.symm,
    latticeDifference_eq_weights]
  have hpartition := below_weights_partition hc hcd
  calc
    (d : Rat) * belowFirstWeight d c +
        (c : Rat) * belowFirstWeight c d =
      (d : Rat) * belowFirstWeight d c -
          (c : Rat) * belowSecondWeight d c +
        (c : Rat) *
          (belowSecondWeight d c + belowFirstWeight c d) := by ring
    _ = _ := by
      rw [hpartition]
      ring

end D5.S1.Phase.Interference.DedekindReciprocityLattice
