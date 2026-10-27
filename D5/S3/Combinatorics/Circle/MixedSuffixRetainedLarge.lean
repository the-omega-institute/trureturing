/- GID: D5/S3/Combinatorics/Circle/MixedSuffixRetainedLarge
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/MixedSuffixRetainedLarge
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic, mathlib/module/Mathlib.Order.Prod.Lex.Basic]
   utility: none
   digest: A moved same-sign LARGE gate preserves G and strictly lowers H with exact mixed-suffix inventory. -/
module
public import D5.S3.Combinatorics.Circle.MixedSuffixEnergy

/-! Native source candidate extending ExpandingSourcePath and MixedSuffixEnergy.
The explicit word keeps exactly one physical suffix label; no gate, replacement
legality, energy estimate, or endpoint is a premise. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MixedSuffixRetainedLarge
open SourceWidth ExpandingSourcePath MixedSuffixEnergy
open scoped BigOperators

/-- The native unsigned potential telescopes along every physical source path,
including a seam crossing. No LARGE or numerical-period hypothesis is needed. -/
private theorem unsigned_path_sum
    {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (p : Fin k) (m : ℕ) :
    mass (actualSource k t) (path (by omega) p m) =
      (actualSource k t (phase (by omega) p m) +
        if actualSource k t (phase (by omega) p m) < 0 then modulus k else 0) -
      (actualSource k t p + if actualSource k t p < 0 then modulus k else 0) := by
  obtain ⟨_, _, _, hN, hodd⟩ := source_geometry hk
  let f := actualSource k t
  let u : Fin k → ℤ := fun q => f q + if f q < 0 then modulus k else 0
  have hbound (q : Fin k) : -(modulus k / 2) ≤ f q ∧ f q ≤ modulus k / 2 :=
    centered_bounds hN hodd _
  have hstep (j : ℕ) : f (phase (by omega) p (j + 1)) =
      doubleStep (modulus k) (f (phase (by omega) p j)) := phase_step hk t p j
  have hpot (j : ℕ) : u (phase (by omega) p (j + 1)) -
      u (phase (by omega) p j) = f (phase (by omega) p j) := by
    dsimp only [u]
    rw [hstep j]
    exact unsigned_step hN hodd (hbound _)
  have hp := path_range (phase (by omega) p) m
    (fun j _ => hpot j) (fun j _ => hstep j)
  simpa [mass, path, u, f] using path_sum hp

private theorem largeUsed_of_all {k : ℕ} (t : ℕ) (L : List (Fin k))
    (h : ∀ q ∈ L, Large k t q) : largeUsed k t L = L.length := by
  revert h
  induction L with
  | nil => intro _; simp [largeUsed, mass]
  | cons q L ih =>
    intro h
    have hq := h q (by simp)
    have hL := ih (fun r hr => h r (by simp [hr]))
    change largeWeight k t q + largeUsed k t L = L.length + 1
    simp [largeWeight, hq, hL, Nat.add_comm]

/-- E_keep_one for the literal original source and physical mixed suffix.
The endpoint identity and singleton gate below are conclusions. The retained z
may have arbitrary SMALL and LARGE labels before it in B. Only its actual sign,
magnitude, membership and LARGE status are assumed, and every other suffix label
is returned. All complements are in Fin k, with multiplicities protected by Nodup. -/
theorem mixed_suffix_retained_large_exchange
    {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (p x : Fin k) (m : ℕ)
    (hm : 2 ≤ m) (heven : m % 2 = 0)
    (A B : List (Fin k)) (z : Fin k)
    (hW : (A ++ x :: B).Nodup)
    (hlegal : InStrip (actualSource k t) (half k) 0 (A ++ x :: B))
    (hhit : phase (by omega) p m = x)
    (hunused : ∀ j < m, phase (by omega) p j ∉ A ++ x :: B)
    (hlarge : ∀ j < m, Large k t (phase (by omega) p j))
    (hexpanding : 0 < 3 * |actualSource k t p| - modulus k)
    (hsuffix : largeUsed k t B = m)
    (hz : z ∈ B) (hzlarge : Large k t z)
    (hzsign : 0 < actualSource k t p * actualSource k t z)
    (hzbound : |actualSource k t z| ≤ |actualSource k t p|) :
    let W := A ++ x :: B
    let P := path (by omega) p m
    let V := (A ++ P) ++ [z]
    let b := mass (actualSource k t) (A ++ P)
    let R := insert x (B.toFinset \ {z})
    m < k ∧ P.Nodup ∧ List.Disjoint P W ∧ V.Nodup ∧
    mass (actualSource k t) P = actualSource k t x - actualSource k t p ∧
    InStrip (actualSource k t) (half k) b [z] ∧
    (0 ≤ b + actualSource k t z ∧ b + actualSource k t z ≤ half k) ∧
    InStrip (actualSource k t) (half k) 0 V ∧
    (∀ n : ℕ, 0 ≤ mass (actualSource k t) (V.take n) ∧
      mass (actualSource k t) (V.take n) ≤ half k) ∧
    V.toFinset = (W.toFinset \ R) ∪ P.toFinset ∧
    Disjoint (W.toFinset \ R) P.toFinset ∧
    V.toFinsetᶜ = (W.toFinsetᶜ \ P.toFinset) ∪ R ∧
    Disjoint (W.toFinsetᶜ \ P.toFinset) R ∧
    G k t V = G k t W ∧
    H k t V + (3 : ℕ) ^ (actualSource k t x).natAbs + H k t (B.erase z) =
      H k t W + H k t P ∧
    H k t V < H k t W ∧
    U V + m = U W + B.length ∧
    U V = U W + smallUsed k t B ∧
    remainingMass (actualSource k t) V = -mass (actualSource k t) V ∧
    J k t V < J k t W := by
  classical
  dsimp only
  let W := A ++ x :: B
  let P := path (by omega) p m
  let V0 := A ++ P
  let V := (A ++ P) ++ [z]
  let R := insert x (B.toFinset \ {z})
  let a := mass (actualSource k t) A
  let b := mass (actualSource k t) V0
  have hk0 : 0 < k := by omega
  obtain ⟨hAnod, htailnod, hAB⟩ := List.nodup_append'.mp hW
  have hxB : x ∉ B := (List.nodup_cons.mp htailnod).1
  have hxz : x ≠ z := by
    intro he
    apply hxB
    simpa [he] using hz
  have hArest (q : Fin k) : q ∈ A → q ∉ x :: B :=
    fun hq => List.disjoint_left.mp hAB hq
  have hW0nod : (A ++ [x]).Nodup := by
    apply hAnod.append (by simp)
    apply List.disjoint_left.mpr
    intro q hqA hqx
    exact hArest q hqA (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hqx)))
  obtain ⟨hAlegal, htail⟩ := strip_split A (x :: B) hlegal
  have hax : 0 ≤ a + actualSource k t x ∧ a + actualSource k t x ≤ half k := by
    simpa [a, mass] using inStrip_prefix htail 1
  have hW0legal : InStrip (actualSource k t) (half k) 0 (A ++ [x]) := by
    apply inStrip_append hAlegal
    have ha : 0 ≤ a ∧ a ≤ half k := by
      simpa [mass, a] using inStrip_prefix htail 0
    have hsingle : InStrip (actualSource k t) (half k) a [x] := ⟨ha.1, ha.2, hax⟩
    simpa [a, mass] using hsingle
  have hunused0 : ∀ j < m, phase (by omega) p j ∉ A ++ x :: [] := by
    intro j hj hq
    apply hunused j hj
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq
    · exact List.mem_append_left _ hq
    · simp [hq]
  -- E_mix is used on A++[x], not on the ineligible m-LARGE suffix B.
  have hbase := mixed_suffix_energy_exchange hk t p x m hm heven A []
    hW0nod hW0legal hhit hunused0 hlarge hexpanding
    (by simp [largeUsed, mass])
  dsimp only at hbase
  obtain ⟨hmk, hPnod, _, hV0nod, hV0legal, _, _, _, _, _, _, _,
    hH0, _, _, _, _⟩ := hbase
  change V0.Nodup at hV0nod
  change InStrip (actualSource k t) (half k) 0 V0 at hV0legal
  change H k t V0 < H k t (A ++ [x]) at hH0
  have hPW : List.Disjoint P W := by
    apply List.disjoint_left.mpr
    intro q hq hqW
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    exact hunused j (List.mem_range.mp hj) hqW
  have hzW : z ∈ W := by simp [W, hz]
  have hzA : z ∉ A := by
    intro h
    exact hArest z h (by simp [hz])
  have hzP : z ∉ P := fun h => List.disjoint_left.mp hPW h hzW
  have hzV0 : z ∉ V0 := by simpa only [V0, List.mem_append, not_or] using And.intro hzA hzP
  have hVnod : V.Nodup := by
    change (V0 ++ [z]).Nodup
    apply hV0nod.append (by simp)
    apply List.disjoint_left.mpr
    intro q hq hqz
    have he : q = z := List.mem_singleton.mp hqz
    subst q
    exact hzV0 hq
  let negative : Bool := decide (actualSource k t p < 0)
  have hd : 0 < 3 * orient negative (actualSource k t p) - modulus k := by
    simpa only [negative, orient_choose] using hexpanding
  have hprofile := expanding_path_estimates hk t p m hm heven negative hlarge hd
  dsimp only at hprofile
  rw [hhit] at hprofile
  obtain ⟨hxpos, hxlarge, _, _, _, _⟩ := hprofile
  -- Even orientation makes the unsigned start and end corrections identical.
  have hend : mass (actualSource k t) P = actualSource k t x - actualSource k t p := by
    have hu := unsigned_path_sum hk t p m
    rw [hhit] at hu
    by_cases hp : actualSource k t p < 0
    · have hx : actualSource k t x < 0 := by
        simpa [negative, orient, hp] using hxpos
      simpa [P, hp, hx] using hu
    · have hx : ¬ actualSource k t x < 0 := by
        have hx' : 0 < actualSource k t x := by
          simpa [negative, orient, hp] using hxpos
        omega
      simpa [P, hp, hx] using hu
  have hb : 0 ≤ b ∧ b ≤ half k := by
    simpa [b, mass] using inStrip_prefix hV0legal V0.length
  have hseam : b + actualSource k t p = a + actualSource k t x := by
    have hsum : b = a + mass (actualSource k t) P := by simp [b, V0, a, mass]
    omega
  -- This is the new LARGE gate. No old position or viable suffix is reused.
  have hgate : 0 ≤ b + actualSource k t z ∧ b + actualSource k t z ≤ half k := by
    rcases mul_pos_iff.mp hzsign with ⟨hp, hzpos⟩ | ⟨hp, hzneg⟩
    · have hmag : actualSource k t z ≤ actualSource k t p := by
        simpa only [abs_of_pos hp, abs_of_pos hzpos] using hzbound
      constructor <;> omega
    · have hmag : actualSource k t p ≤ actualSource k t z := by
        have h := hzbound
        rw [abs_of_neg hp, abs_of_neg hzneg] at h
        omega
      constructor <;> omega
  have hsingleton : InStrip (actualSource k t) (half k) b [z] :=
    ⟨hb.1, hb.2, hgate⟩
  have hVlegal : InStrip (actualSource k t) (half k) 0 V := by
    apply inStrip_append hV0legal
    simpa [b, mass] using hsingleton
  have hprefix : ∀ n : ℕ, 0 ≤ mass (actualSource k t) (V.take n) ∧
      mass (actualSource k t) (V.take n) ≤ half k := by
    intro n
    simpa [mass] using inStrip_prefix hVlegal n
  have hUsed : V.toFinset = (W.toFinset \ R) ∪ P.toFinset := by
    ext q
    have hAR := hArest q
    have hZB : q = z → q ∈ B := by intro he; simpa [he] using hz
    have hXZ : ¬ (q = x ∧ q = z) := by rintro ⟨rfl, he⟩; exact hxz he
    simp only [List.mem_cons] at hAR
    simp only [V, W, R, List.mem_toFinset, List.mem_append, List.mem_singleton,
      List.mem_cons, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, List.not_mem_nil, or_false]
    constructor
    · rintro ((hA | hP) | hqz)
      · refine Or.inl ⟨Or.inl hA, ?_⟩
        rintro (he | ⟨hB, _⟩)
        · exact hAR hA (Or.inl he)
        · exact hAR hA (Or.inr hB)
      · exact Or.inr hP
      · refine Or.inl ⟨Or.inr (Or.inr (hZB hqz)), ?_⟩
        rintro (he | ⟨_, hnz⟩)
        · exact hXZ ⟨he, hqz⟩
        · exact hnz hqz
    · rintro (⟨hqW, hNR⟩ | hP)
      · rcases hqW with hA | hqx | hB
        · exact Or.inl (Or.inl hA)
        · exact (hNR (Or.inl hqx)).elim
        · by_cases hqz : q = z
          · exact Or.inr hqz
          · exact (hNR (Or.inr ⟨hB, hqz⟩)).elim
      · exact Or.inl (Or.inr hP)
  have hUsedDis : Disjoint (W.toFinset \ R) P.toFinset := by
    apply Finset.disjoint_left.mpr
    intro q hq hqP
    exact List.disjoint_left.mp hPW (List.mem_toFinset.mp hqP)
      (List.mem_toFinset.mp (Finset.mem_sdiff.mp hq).1)
  have hUnused : V.toFinsetᶜ = (W.toFinsetᶜ \ P.toFinset) ∪ R := by
    ext q
    have hAR := hArest q
    have hPR : q ∈ P → q ∉ W := fun hq => List.disjoint_left.mp hPW hq
    have hZB : q = z → q ∈ B := by intro he; simpa [he] using hz
    have hXZ : ¬ (q = x ∧ q = z) := by rintro ⟨rfl, he⟩; exact hxz he
    simp only [W, List.mem_append, List.mem_cons] at hAR hPR
    simp only [V, W, R, Finset.mem_compl, List.mem_toFinset, List.mem_append,
      List.mem_singleton, List.mem_cons, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton, List.not_mem_nil, or_false]
    constructor
    · intro hV
      by_cases hqW : q ∈ A ∨ q = x ∨ q ∈ B
      · apply Or.inr
        rcases hqW with hA | hqx | hB
        · exact (hV (Or.inl (Or.inl hA))).elim
        · exact Or.inl hqx
        · exact Or.inr ⟨hB, fun hqz => hV (Or.inr hqz)⟩
      · exact Or.inl ⟨hqW, fun hP => hV (Or.inl (Or.inr hP))⟩
    · rintro (⟨hW, hP⟩ | hR)
      · rintro ((hA | hqP) | hqz)
        · exact hW (Or.inl hA)
        · exact hP hqP
        · exact hW (Or.inr (Or.inr (hZB hqz)))
      · rcases hR with hqx | ⟨hB, hnz⟩
        · rintro ((hA | hqP) | hqz)
          · exact hAR hA (Or.inl hqx)
          · exact hPR hqP (Or.inr (Or.inl hqx))
          · exact hXZ ⟨hqx, hqz⟩
        · rintro ((hA | hqP) | hqz)
          · exact hAR hA (Or.inr hB)
          · exact hPR hqP (Or.inr (Or.inr hB))
          · exact hnz hqz
  have hUnusedDis : Disjoint (W.toFinsetᶜ \ P.toFinset) R := by
    apply Finset.disjoint_left.mpr
    intro q hq hqR
    have hqW : q ∈ W := by
      simp only [R, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton,
        List.mem_toFinset] at hqR
      rcases hqR with he | ⟨hB, _⟩
      · simp [W, he]
      · simp [W, hB]
    exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hq).1) (List.mem_toFinset.mpr hqW)
  have hPLarge : ∀ q ∈ P, Large k t q := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    exact hlarge j (List.mem_range.mp hj)
  have hPcount : largeUsed k t P = m := by
    simpa [P] using largeUsed_of_all t P hPLarge
  have hCountsW : largeUsed k t W = largeUsed k t A + 1 + largeUsed k t B := by
    simp [W, largeUsed, mass, largeWeight, hxlarge, Nat.add_assoc]
  have hCountsV : largeUsed k t V = largeUsed k t A + m + 1 := by
    have hsum : largeUsed k t V = largeUsed k t A + largeUsed k t P + 1 := by
      simp [V, largeUsed, mass, largeWeight, hzlarge, Nat.add_assoc]
    omega
  have hG : G k t V = G k t W := by
    have hw : G k t W + largeUsed k t W = ∑ q : Fin k, largeWeight k t q :=
      physical_balance (largeWeight k t) W hW
    have hv : G k t V + largeUsed k t V = ∑ q : Fin k, largeWeight k t q :=
      physical_balance (largeWeight k t) V hVnod
    omega
  have hUbalance : U V + m = U W + B.length := by
    have hw : U W + W.length = k := by
      simpa [U, mass, List.map_const'] using
        physical_balance (fun _ : Fin k => (1 : ℕ)) W hW
    have hv : U V + V.length = k := by
      simpa [U, mass, List.map_const'] using
        physical_balance (fun _ : Fin k => (1 : ℕ)) V hVnod
    have hwlen : W.length = A.length + (1 + B.length) := by simp [W]; omega
    have hvlen : V.length = A.length + m + 1 := by simp [V, P, Nat.add_assoc]
    rw [hwlen] at hw
    rw [hvlen] at hv
    omega
  have hU : U V = U W + smallUsed k t B := by
    have hc := counts_partition t B
    omega
  have hBenergy : H k t B = energyWeight k t z + H k t (B.erase z) := by
    have he := ((List.perm_cons_erase hz).map (energyWeight k t)).sum_eq
    simp only [List.map_cons, List.sum_cons] at he
    change (B.map (energyWeight k t)).sum = energyWeight k t z +
      ((B.erase z).map (energyWeight k t)).sum
    omega
  have hHV : H k t V = H k t V0 + energyWeight k t z := by
    simp [V, V0, H, mass, Nat.add_assoc]
  have hHW : H k t W = H k t (A ++ [x]) + H k t B := by
    simp [W, H, mass, Nat.add_assoc]
  have hHx : H k t (A ++ [x]) = H k t A + (3 : ℕ) ^ (actualSource k t x).natAbs := by
    simp [H, mass, energyWeight, hxlarge]
  have hH0expand : H k t V0 = H k t A + H k t P := by simp [V0, H, mass]
  have hHbalance : H k t V + (3 : ℕ) ^ (actualSource k t x).natAbs +
      H k t (B.erase z) = H k t W + H k t P := by omega
  have hH : H k t V < H k t W := by omega
  have hComplement : remainingMass (actualSource k t) V = -mass (actualSource k t) V := by
    have h := physical_balance (actualSource k t) V hVnod
    rw [(ZeroSumSubsets.source_cycle hk0 t).2.1] at h
    omega
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    exact Or.inr ⟨hG, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hH)⟩
  exact ⟨hmk, hPnod, hPW, hVnod, hend, hsingleton, hgate, hVlegal, hprefix,
    hUsed, hUsedDis, hUnused, hUnusedDis, hG, hHbalance, hH, hUbalance, hU,
    hComplement, hJ⟩

end D5.S3.Combinatorics.Circle.MixedSuffixRetainedLarge
