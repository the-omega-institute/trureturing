/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/TwoAdjacentLowTailLabels
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Adjacent low-tail labels and the threshold-three first-tour obstruction. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection

/-! Threshold-three immutable labels on the original complete-block reader. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacci.Names
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge
open WindowChargeInverse PhysicalWindowDecoder OriginalAcquiredTrace
open GlobalPresetObstruction DonorCorrection
open scoped BigOperators

/-- Labels zero through three are A, B, C and R. All tests use the INITIAL record. -/
def initialLabel {Y : Type u} (Q m : ℕ) (labels : Fin 4 → Y) (bottom : Y) : Option (LiveRecord (Q * m)) → Y
  | none => bottom
  | some q => if Q * m - 3 ≤ q.tail then labels 3 else if (-q.phase).val = 1 then labels 1 else
      if (-q.phase).val = 2 then labels 2 else labels 0

theorem first_zero_form (bits : List Bool) : bits = List.replicate bits.length true ∨
      ∃ a rest, bits = List.replicate a true ++ false :: rest := by
  induction bits with
  | nil => exact Or.inl rfl
  | cons bit bits ih =>
    cases bit
    · exact Or.inr ⟨0, bits, rfl⟩
    · rcases ih with all | ⟨a, rest, cut⟩
      · exact Or.inl (by
          simpa only [List.length_cons, List.replicate_succ] using congrArg (List.cons true) all)
      · exact Or.inr ⟨a + 1, rest, by simp [List.replicate_succ, cut]⟩

private theorem root_merge (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (short : m < k) (B : Fin m → Bool)
    (noCut : ¬ ∃ rest, List.ofFn B = List.replicate 3 true ++ false :: rest) (v : ZMod 2) (phase : ZMod (k + 1)) :
    runBits k B (some ⟨v, phase, k - 4⟩) = runBits k B (some ⟨v, phase, k - 3⟩) := by
  rcases first_zero_form (List.ofFn B) with all | ⟨a, rest, cut⟩
  · have eq : B = allOneBlock m := by
      funext i; have e := congrArg (fun bs : List Bool => bs[i.val]?) all
      simpa [i.isLt, allOneBlock] using e
    rw [eq]; have ex (s : ℕ) (hs : s < k) := (all_one_archive_exact k m hk (by omega) 1 v phase s hs (fun _ => 0)).2.2
    have orbit (s : ℕ) : allOneOrbit k m 1 (some ⟨v, phase, s⟩) = runBits k (allOneBlock m) (some ⟨v, phase, s⟩) := rfl
    rw [←orbit, ex _ (by omega), ←orbit, ex _ (by omega)]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · have a3 : a ≠ 3 := by intro eq; subst a; exact noCut ⟨rest, cut⟩
    have low := first_zero_block_exact k hk m a B rest cut (short_legal k m hk short B) v phase (k - 4) (by omega)
    have high := first_zero_block_exact k hk m a B rest cut (short_legal k m hk short B) v phase (k - 3) (by omega)
    rw [low, high]; by_cases before : a < 3
    · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem forced_root {Y : Type u} (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (labels : Fin 4 → Y) (distinct : Function.Injective labels) (bottom : Y)
    (v : ZMod 2) (pi : NarrowWindowCost.Selector m Y) (d : ℕ)
    (native : ∀ phase s, s < Q * m → ∃ c, NativeExecute pi d (some ⟨v, phase, s⟩) (some v) [] =
        some (initialLabel Q m labels bottom (some ⟨v, phase, s⟩), c)) :
    ∃ b B rest, d = b + 1 ∧ pi (some v) [] = .inr B ∧ List.ofFn B = List.replicate 3 true ++ false :: rest := by
  have short : m < Q * m := by nlinarith
  obtain ⟨c, lo⟩ := native 0 (Q * m - 4) (by omega)
  obtain ⟨c', hi⟩ := native 0 (Q * m - 3) (by omega)
  have lowTarget : initialLabel Q m labels bottom (some ⟨v, 0, Q * m - 4⟩) = labels 0 := by
    simp [initialLabel, show ¬ Q * m - 3 ≤ Q * m - 4 by omega]
  have highTarget : initialLabel Q m labels bottom (some ⟨v, 0, Q * m - 3⟩) = labels 3 := by simp [initialLabel]
  rw [lowTarget] at lo; rw [highTarget] at hi
  have different : labels 0 ≠ labels 3 := by
    intro eq; have := distinct eq
    norm_num at this
  cases d with
  | zero =>
    have eq : NativeExecute (k := Q * m) pi 0 (some ⟨v, 0, Q * m - 4⟩) (some v) [] =
        NativeExecute (k := Q * m) pi 0 (some ⟨v, 0, Q * m - 3⟩) (some v) [] := rfl
    rw [lo, hi] at eq; exact False.elim (different (congrArg Prod.fst (Option.some.inj eq)))
  | succ b =>
    cases chosen : pi (some v) [] with
    | inl y =>
      simp only [NativeExecute, chosen, Option.some.injEq, Prod.mk.injEq] at lo hi
      exact False.elim (different (lo.1.symm.trans hi.1))
    | inr B =>
      have cut : ∃ rest, List.ofFn B = List.replicate 3 true ++ false :: rest := by
        by_contra noCut
        have merge := root_merge (Q * m) m (by omega) hm short B noCut v 0
        have eq : NativeExecute (k := Q * m) pi (b + 1) (some ⟨v, 0, Q * m - 4⟩) (some v) [] =
            NativeExecute (k := Q * m) pi (b + 1) (some ⟨v, 0, Q * m - 3⟩) (some v) [] := by
          simp only [NativeExecute, chosen, merge]
        rw [lo, hi] at eq; exact different (congrArg Prod.fst (Option.some.inj eq))
      obtain ⟨rest, cut⟩ := cut
      exact ⟨b, B, rest, rfl, rfl, cut⟩

private theorem derivative_at (Q m j : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m) (hj : j < Q * m + 1) (B : Fin m → Bool) :
    wordIncrement (Q * m) (-((j : ℕ) : ZMod (Q * m + 1))) B =
      extendedBit B j + if j = 0 then 0 else extendedBit B (j - 1) := by
  rw [increment_derivative (Q * m) (by nlinarith) m (by nlinarith)]; rw [ZMod.val_natCast, Nat.mod_eq_of_lt hj]

private theorem response_at (Q m t i : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m) (hi : i ≤ m) (B : Fin m → Bool) :
    wordIncrement (Q * m) (-((t * m + i : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1))) B =
        extendedBit B i + if i = 0 then 0 else extendedBit B (i - 1) := by
  have phase : -((t * m + i : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1)) =
      -((i : ℕ) : ZMod (Q * m + 1)) := by push_cast; ring
  rw [phase, derivative_at Q m i hQ hm (by nlinarith)]

theorem response_off (Q m t j : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (ht : t < Q) (hj : j ≤ Q * m) (off : j < t * m ∨ (t + 1) * m < j) (B : Fin m → Bool) :
    wordIncrement (Q * m) (-((j : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1))) B = 0 := by
  have short : m < Q * m := by nlinarith
  rcases off with left | right
  · let n := Q * m + 1 + j - t * m
    have hn : n < Q * m + 1 := by dsimp [n]; omega
    have large : m < n := by
      have htm : t * m + m ≤ Q * m := by
        have h := Nat.mul_le_mul_right m (show t + 1 ≤ Q by omega)
        nlinarith
      dsimp [n]; omega
    have phase : -((j : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1)) = -((n : ℕ) : ZMod (Q * m + 1)) := by
      dsimp [n]; rw [Nat.cast_sub (by nlinarith : t * m ≤ Q * m + 1 + j)]
      rw [Nat.cast_add, ZMod.natCast_self]; simp only [zero_add]
      ring
    rw [phase, derivative_at Q m n hQ hm hn]
    simp [extendedBit, show ¬ n < m by omega, show n ≠ 0 by omega, show ¬ n - 1 < m by omega]
  · let n := j - t * m
    have hn : n < Q * m + 1 := by dsimp [n]; omega
    have large : m < n := by
      have le : t * m ≤ j := by nlinarith
      have eq : n + t * m = j := by dsimp [n]; exact Nat.sub_add_cancel le
      nlinarith
    have phase : -((j : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1)) = -((n : ℕ) : ZMod (Q * m + 1)) := by
      dsimp [n]; rw [Nat.cast_sub (by nlinarith : t * m ≤ j)]
      ring
    rw [phase, derivative_at Q m n hQ hm hn]
    simp [extendedBit, show ¬ n < m by omega, show n ≠ 0 by omega, show ¬ n - 1 < m by omega]

private theorem root_bits (m : ℕ) (hm : 4 ≤ m) (B : Fin m → Bool)
    (rest : List Bool) (cut : List.ofFn B = List.replicate 3 true ++ false :: rest) :
    extendedBit B 0 = 1 ∧ extendedBit B 1 = 1 ∧ extendedBit B 2 = 1 ∧ extendedBit B 3 = 0 := by
  have chargeAt (i : ℕ) (hi : i < m) : (List.ofFn B)[i]? = some (B ⟨i, hi⟩) := by simp [hi]
  have e0 := congrArg (fun bs : List Bool => bs[0]?) cut
  have e1 := congrArg (fun bs : List Bool => bs[1]?) cut
  have e2 := congrArg (fun bs : List Bool => bs[2]?) cut
  have e3 := congrArg (fun bs : List Bool => bs[3]?) cut
  rw [chargeAt 0 (by omega)] at e0; rw [chargeAt 1 (by omega)] at e1
  rw [chargeAt 2 (by omega)] at e2; rw [chargeAt 3 (by omega)] at e3
  norm_num [List.replicate_succ] at e0 e1 e2 e3
  simp [extendedBit, bitScalar, show 0 < m by omega, show 1 < m by omega,
    show 2 < m by omega, show 3 < m by omega, e0, e1, e2, e3]

private theorem band_response (Q m t j : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (ht : t < Q) (hj : j = 1 ∨ j = 2) (B : Fin m → Bool)
    (root : t = 0 → ∃ rest, List.ofFn B = List.replicate 3 true ++ false :: rest) :
    wordIncrement (Q * m) (-((j : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1))) B = 0 := by
  by_cases first : t = 0
  · subst t; obtain ⟨rest, cut⟩ := root rfl
    have bits := root_bits m hm B rest cut
    simp only [Nat.zero_mul, Nat.cast_zero, add_zero]; rcases hj with rfl | rfl
    · rw [derivative_at Q m 1 hQ hm (by nlinarith)]; norm_num only [Nat.reduceSub, Nat.reduceEqDiff, ite_false]
      rw [bits.1, bits.2.1]; exact CharTwo.add_self_eq_zero _
    · rw [derivative_at Q m 2 hQ hm (by nlinarith)]; norm_num only [Nat.reduceSub, Nat.reduceEqDiff, ite_false]
      rw [bits.2.1, bits.2.2.1]; exact CharTwo.add_self_eq_zero _
  · apply response_off Q m t j hQ hm ht (by rcases hj with rfl | rfl <;> nlinarith)
    have pos : 1 ≤ t := by omega
    have large : m ≤ t * m := by simpa using Nat.mul_le_mul_right m pos
    exact Or.inl (by rcases hj with rfl | rfl <;> omega)

private theorem alternating_segment (b : ℕ → ZMod 2) (a n : ℕ) (edges : ∀ i, a < i → i ≤ a + n → b i + b (i - 1) = 1) :
    b (a + n) = b a + (n : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have prev := ih (fun i lo hi => edges i lo (by omega))
    have last := edges (a + (n + 1)) (by omega) (by omega)
    rw [show a + (n + 1) - 1 = a + n by omega, prev] at last; push_cast
    calc
      b (a + (n + 1)) = (b (a + (n + 1)) + (b a + (n : ℕ))) + (b a + (n : ℕ)) := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = 1 + (b a + (n : ℕ)) := by rw [last]
      _ = b a + ((n : ℕ) + 1) := by ring

/-- One fixed first-tour stream, with its literal root suffix unrestricted,
cannot screen every outside phase when its width is even. -/
private theorem even_tour_survivor (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m) (even : Even m) (words : ℕ → Fin m → Bool)
    (root : ∃ rest, List.ofFn (words 0) = List.replicate 3 true ++ false :: rest) :
    ∃ j, j ≤ Q * m ∧ j ≠ 1 ∧ j ≠ 2 ∧ ∀ t, t < Q → wordIncrement (Q * m)
        (-((j : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1))) (words t) = 0 := by
  classical
  let q (t j : ℕ) : ZMod 2 := wordIncrement (Q * m)
    (-((j : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1))) (words t)
  change ∃ j, j ≤ Q * m ∧ j ≠ 1 ∧ j ≠ 2 ∧ ∀ t, t < Q → q t j = 0
  by_contra noSurvivor
  have cover (j : ℕ) (bound : j ≤ Q * m) (n1 : j ≠ 1) (n2 : j ≠ 2) : ∃ t, t < Q ∧ q t j ≠ 0 := by
    by_contra none
    push Not at none
    exact noSurvivor ⟨j, bound, n1, n2, none⟩
  have off (t j : ℕ) (ht : t < Q) (hj : j ≤ Q * m) (outside : j < t * m ∨ (t + 1) * m < j) : q t j = 0 :=
    response_off Q m t j hQ hm ht hj outside (words t)
  have chargeAt (t i : ℕ) (hi : i ≤ m) : q t (t * m + i) =
      extendedBit (words t) i + if i = 0 then 0 else extendedBit (words t) (i - 1) :=
    response_at Q m t i hQ hm hi (words t)
  have one (x : ZMod 2) (nonzero : x ≠ 0) : x = 1 := by
    have bound := ZMod.val_lt x
    have nz : x.val ≠ 0 := by intro eq; apply nonzero; exact ZMod.val_injective 2 eq
    apply ZMod.val_injective 2
    rw [show (1 : ZMod 2).val = 1 by decide]; omega
  have interior (t i : ℕ) (ht : t < Q) (hi : 0 < i) (him : i < m) (n1 : t * m + i ≠ 1) (n2 : t * m + i ≠ 2) :
      extendedBit (words t) i + extendedBit (words t) (i - 1) = 1 := by
    obtain ⟨r, hr, hit⟩ := cover (t * m + i) (by nlinarith) n1 n2
    have rt : r = t := by
      by_contra ne
      have outside : t * m + i < r * m ∨ (r + 1) * m < t * m + i := by
        rcases lt_or_gt_of_ne ne with less | greater
        · exact Or.inr (by nlinarith)
        · exact Or.inl (by nlinarith)
      exact hit (off r _ hr (by nlinarith) outside)
    subst r; rw [chargeAt t i (by omega), ite_eq_right (by omega)] at hit
    exact one _ hit
  obtain ⟨rest, cut⟩ := root
  have rootBits := root_bits m hm (words 0) rest cut
  have rootEnd : extendedBit (words 0) (m - 1) = 0 := by
    have alt := alternating_segment (extendedBit (words 0)) 3 (m - 4) (by
        intro i lo hi; have h := interior 0 i (by omega) (by omega) (by omega) (by omega) (by omega)
        simpa only [Nat.zero_mul, Nat.zero_add] using h)
    have parity : ((m - 4 : ℕ) : ZMod 2) = 0 := by
      have e : Even (m - 4) := by
        rw [Nat.even_iff] at even ⊢; omega
      exact e.natCast_zmod_two
    rw [show 3 + (m - 4) = m - 1 by omega, rootBits.2.2.2, parity, zero_add] at alt; exact alt
  have ends (t : ℕ) (ht : t < Q) : extendedBit (words t) (m - 1) = 0 := by
    induction t with
    | zero => exact rootEnd
    | succ t ih =>
      have previous := ih (by omega)
      obtain ⟨r, hr, hit⟩ := cover ((t + 1) * m) (by nlinarith) (by nlinarith) (by nlinarith)
      have candidates : r = t ∨ r = t + 1 := by
        by_contra neither
        have ne0 : r ≠ t := by omega
        have ne1 : r ≠ t + 1 := by omega
        have outside : (t + 1) * m < r * m ∨ (r + 1) * m < (t + 1) * m := by
          by_cases less : r < t
          · have h := Nat.mul_le_mul_right m (show r + 1 ≤ t by omega)
            exact Or.inr (by nlinarith)
          · have h := Nat.mul_le_mul_right m (show t + 2 ≤ r by omega)
            exact Or.inl (by nlinarith)
        exact hit (off r _ hr (by nlinarith) outside)
      have head : extendedBit (words (t + 1)) 0 = 1 := by
        rcases candidates with eqr | eqr
        · rw [eqr] at hit; have eq : (t + 1) * m = t * m + m := by ring
          rw [eq, chargeAt t m le_rfl, ite_eq_right (by omega),
            show extendedBit (words t) m = 0 by simp [extendedBit], previous, zero_add] at hit
          exact False.elim (hit rfl)
        · rw [eqr] at hit; have eq : (t + 1) * m = (t + 1) * m + 0 := by omega
          rw [eq, chargeAt (t + 1) 0 (by omega)] at hit; simp only [ite_true, add_zero] at hit
          exact one _ hit
      have alt := alternating_segment (extendedBit (words (t + 1))) 0 (m - 1) (by
          intro i lo hi; exact interior (t + 1) i ht (by omega) (by omega) (by nlinarith) (by nlinarith))
      have parity : ((m - 1 : ℕ) : ZMod 2) = 1 := by
        apply Odd.natCast_zmod_two
        rw [Nat.even_iff] at even; rw [Nat.odd_iff]
        omega
      simpa only [Nat.zero_add, head, parity, show (1 : ZMod 2) + 1 = 0 by decide] using alt
  obtain ⟨r, hr, hit⟩ := cover (Q * m) le_rfl (by nlinarith) (by nlinarith)
  have last : r + 1 = Q := by
    by_contra ne
    have h := Nat.mul_le_mul_right m (show r + 2 ≤ Q by omega)
    exact hit (off r _ hr le_rfl (Or.inr (by nlinarith)))
  have eq : Q * m = r * m + m := by rw [←last]; ring
  rw [eq, chargeAt r m le_rfl, ite_eq_right (by omega)] at hit
  rw [show extendedBit (words r) m = 0 by simp [extendedBit], ends r hr, zero_add] at hit; exact hit rfl

private def bandArchive {Y : Type u} {m : ℕ} (pi : NarrowWindowCost.Selector m Y)
    (v : ZMod 2) : ℕ → NarrowWindowCost.Archive m
  | 0 => []
  | t + 1 => let ar := bandArchive pi v t
      let B := match pi (some v) ar with
        | .inl _ => fun _ => false
        | .inr B => B
      ar ++ [(B, some v)]

private def bandWord {Y : Type u} {m : ℕ} (pi : NarrowWindowCost.Selector m Y) (v : ZMod 2) (t : ℕ) : Fin m → Bool :=
  match pi (some v) (bandArchive pi v t) with
  | .inl _ => fun _ => false
  | .inr B => B

private theorem low_label {Y : Type u} (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (labels : Fin 4 → Y) (bottom : Y) (v : ZMod 2) (j : ℕ) (hj : j ≤ Q * m) :
    initialLabel Q m labels bottom (some ⟨v, -((j : ℕ) : ZMod (Q * m + 1)), 0⟩) =
      if j = 1 then labels 1 else if j = 2 then labels 2 else labels 0 := by
  have total : 8 ≤ Q * m := by simpa using Nat.mul_le_mul hQ hm
  simp [initialLabel, show ¬ Q * m - 3 ≤ 0 by omega, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : j < Q * m + 1)]

/-- The recursively selected zero archive is actually traversed by every
surviving INITIAL source. The two different band labels prevent both early
stopping and uniform rejection; all survivors have one scalar and one tail. -/
private theorem band_walk {Y : Type u} (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (labels : Fin 4 → Y) (distinct : Function.Injective labels) (bottom : Y)
    (v : ZMod 2) (pi : NarrowWindowCost.Selector m Y) (d : ℕ)
    (native : ∀ phase s, s < Q * m → ∃ c, NativeExecute pi d (some ⟨v, phase, s⟩) (some v) [] =
        some (initialLabel Q m labels bottom (some ⟨v, phase, s⟩), c))
    (root : ∃ rest, List.ofFn (bandWord pi v 0) = List.replicate 3 true ++ false :: rest) :
    ∀ t, t ≤ Q → ∃ b tail, d = t + b ∧ tail < Q * m ∧
      (∀ i, i < t → pi (some v) (bandArchive pi v i) = .inr (bandWord pi v i)) ∧
      ∀ j : ZMod (Q * m + 1), (∀ i, i < t → wordIncrement (Q * m)
          (-j + ((i * m : ℕ) : ZMod (Q * m + 1))) (bandWord pi v i) = 0) →
        ∃ c, NativeExecute pi b (some ⟨v, -j + ((t * m : ℕ) : ZMod (Q * m + 1)), tail⟩) (some v) (bandArchive pi v t) =
          some (initialLabel Q m labels bottom (some ⟨v, -j, 0⟩), c) := by
  have different : labels 1 ≠ labels 2 := by
    intro eq; have := distinct eq
    norm_num at this
  have bandzero (j t : ℕ) (hj : j = 1 ∨ j = 2) (ht : t < Q) :
      wordIncrement (Q * m) (-((j : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1)))
        (bandWord pi v t) = 0 := by
    apply band_response Q m t j hQ hm ht hj
    intro eq; subst t
    exact root
  intro t
  induction t with
  | zero =>
    intro _; refine ⟨d, 0, by omega, by nlinarith, ?_, ?_⟩
    · intro i hi; omega
    · intro j _; simpa only [Nat.zero_mul, Nat.cast_zero, add_zero, bandArchive] using native (-j) 0 (by nlinarith)
  | succ t ih =>
    intro ht; obtain ⟨b, tail, budget, tailBound, chosenBefore, success⟩ := ih (by omega)
    have bandSuccess (j : ℕ) (hj : j = 1 ∨ j = 2) : ∃ c, NativeExecute pi b
          (some ⟨v, -((j : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1)), tail⟩)
          (some v) (bandArchive pi v t) =
          some ((if j = 1 then labels 1 else labels 2), c) := by
      obtain ⟨c, ex⟩ := success (j : ZMod (Q * m + 1)) (fun i hi => bandzero j i hj (by omega))
      rw [low_label Q m hQ hm labels bottom v j (by rcases hj with rfl | rfl <;> nlinarith)] at ex
      rcases hj with rfl | rfl <;> refine ⟨c, ?_⟩ <;> simpa using ex
    obtain ⟨c1, ex1⟩ := bandSuccess 1 (Or.inl rfl)
    obtain ⟨c2, ex2⟩ := bandSuccess 2 (Or.inr rfl)
    simp only [ite_true, show (2 : ℕ) ≠ 1 by omega, ite_false] at ex1 ex2
    cases b with
    | zero =>
      have eq : NativeExecute (k := Q * m) pi 0
          (some ⟨v, -((1 : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1)), tail⟩)
          (some v) (bandArchive pi v t) =
          NativeExecute (k := Q * m) pi 0
          (some ⟨v, -((2 : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1)), tail⟩)
          (some v) (bandArchive pi v t) := rfl
      rw [ex1, ex2] at eq; exact False.elim (different (congrArg Prod.fst (Option.some.inj eq)))
    | succ b =>
      cases chosen : pi (some v) (bandArchive pi v t) with
      | inl y =>
        simp only [NativeExecute, chosen, Option.some.injEq, Prod.mk.injEq] at ex1 ex2
        exact False.elim (different (ex1.1.symm.trans ex2.1))
      | inr B =>
        have safe : runAdmissible (Q * m - 1) (Q * m - 1 - tail) m B = true := by
          by_contra illegal
          have record (phase : ZMod (Q * m + 1)) : runBits (Q * m) B (some ⟨v, phase, tail⟩) = none := by
            rw [(literal_block_execution (Q * m) (by nlinarith) m B v phase tail tailBound).1, ite_eq_right illegal]
          have eq := ex1.symm.trans (by
            simpa only [NativeExecute, chosen, record] using ex2)
          exact different (congrArg Prod.fst (Option.some.inj eq))
        have word : bandWord pi v t = B := by simp only [bandWord, chosen]
        have nextAr : bandArchive pi v (t + 1) = bandArchive pi v t ++ [(B, some v)] := by
          simp only [bandArchive, chosen]
        refine ⟨b, tailAfter tail B, by omega,
          (literal_block_execution (Q * m) (by nlinarith) m B v 0 tail tailBound).2 safe, ?_, ?_⟩
        · intro i hi; by_cases before : i < t
          · exact chosenBefore i before
          · have eq : i = t := by omega
            subst i; rw [word]
            exact chosen
        · intro j zero; obtain ⟨c, ex⟩ := success j (fun i hi => zero i (by omega))
          have execution := (literal_block_execution (Q * m) (by nlinarith) m B v
            (-j + ((t * m : ℕ) : ZMod (Q * m + 1))) tail tailBound).1
          have charge := zero t (by omega)
          rw [word] at charge; rw [ite_eq_left safe, charge, add_zero] at execution
          simp only [NativeExecute, chosen, execution, endpointReading] at ex
          obtain ⟨r, er, eq⟩ := Option.map_eq_some_iff.mp ex
          refine ⟨r.2, ?_⟩
          rw [nextAr]; have phase : -j + ((t * m : ℕ) : ZMod (Q * m + 1)) + (m : ℕ) =
              -j + (((t + 1) * m : ℕ) : ZMod (Q * m + 1)) := by push_cast; ring
          rw [phase] at er
          change NativeExecute pi b (some ⟨v, -j + (((t + 1) * m : ℕ) : ZMod (Q * m + 1)), tailAfter tail B⟩)
            (some v) (bandArchive pi v t ++ [(B, some v)]) = some r at er
          rw [er]; exact congrArg some (Prod.ext (Prod.mk.inj eq).1 rfl)

private theorem three_need_two {Y : Type u} (k m : ℕ) (hk : 2 ≤ k)
    (pi : NarrowWindowCost.Selector m Y) (b : ℕ) (small : b ≤ 1)
    (z : ZMod 2) (phase : Fin 3 → ZMod (k + 1)) (tail : ℕ) (tailBound : tail < k)
    (free : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m)
    (labels : Fin 3 → Y) (distinct : Function.Injective labels)
    (success : ∀ j, ∃ c, NativeExecute pi b (some ⟨z, phase j, tail⟩) free archive = some (labels j, c)) : False := by
  let code (j : Fin 3) : ZMod 2 := OwnPathCharges.ownCharge pi b z (phase j) tail free archive 0
  have injective : Function.Injective code := by
    intro i j eq; apply distinct
    obtain ⟨ci, ei⟩ := success i
    obtain ⟨cj, ej⟩ := success j
    apply OwnPathCharges.charge_separates k m hk pi b z (phase i) (phase j) tail tailBound
      free archive (labels i) (labels j) ci cj ei ej
    intro t ht; have t0 : t = 0 := by omega
    subst t; exact eq
  have card := Fintype.card_le_of_injective code injective
  norm_num at card

/-- Every lawful original adaptive controller pays at least Q+2 at even width.
The outside source is selected from the same actual band archive and may
depend on the controller, including its unrestricted root suffix. -/
theorem even_adaptive_lower {Y : Type u} (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (even : Even m) (labels : Fin 4 → Y) (distinct : Function.Injective labels) (bottom : Y) (alphabet : Bool) (d : ℕ)
    (feasible : OriginalAdaptiveFeasible (Q * m) m (by nlinarith) alphabet
      (initialLabel Q m labels bottom) d) : Q + 2 ≤ d := by
  classical
  by_contra small
  have hd : d ≤ Q + 1 := by omega
  obtain ⟨pi, legal, bot, correct⟩ := feasible
  have gcd : Nat.gcd m (Q * m + 1) = 1 := by
    rw [Nat.mul_comm Q m, Nat.gcd_mul_left_add_right]; simp
  have native (phase : ZMod (Q * m + 1)) (s : ℕ) (hs : s < Q * m) : ∃ c,
      NativeExecute pi d (some ⟨0, phase, s⟩) (some 0) [] =
        some (initialLabel Q m labels bottom (some ⟨0, phase, s⟩), c) := by
    obtain ⟨c, _, ex⟩ := OwnPathCharges.native_fiber (Q * m) m (by nlinarith) (by omega)
      alphabet (initialLabel Q m labels bottom) 0 d pi
      (by
        intro history; dsimp only
        intro obs; obtain ⟨c, le, ex⟩ := correct history
        rw [obs] at ex
        exact ⟨c, le, ex⟩) phase s hs (by rw [gcd]; exact one_dvd _)
    exact ⟨c, ex⟩
  obtain ⟨b0, B, rest, budget0, chosen0, cut⟩ := forced_root Q m hQ hm labels distinct bottom 0 pi d native
  have root : ∃ rest, List.ofFn (bandWord pi 0 0) = List.replicate 3 true ++ false :: rest := by
    refine ⟨rest, ?_⟩
    simpa only [bandWord, bandArchive, chosen0] using cut
  obtain ⟨b, tail, budget, tailBound, chosen, success⟩ :=
    band_walk Q m hQ hm labels distinct bottom 0 pi d native root Q le_rfl
  obtain ⟨j, bound, n1, n2, zero⟩ := even_tour_survivor Q m hQ hm even (bandWord pi 0) root
  let index (x : Fin 3) : Fin 4 := if x = 0 then 1 else if x = 1 then 2 else 0
  have index_injective : Function.Injective index := by decide
  let phase (x : Fin 3) : ZMod (Q * m + 1) := -((if x = 0 then 1 else if x = 1 then 2 else j : ℕ) : ZMod (Q * m + 1)) +
      ((Q * m : ℕ) : ZMod (Q * m + 1))
  apply three_need_two (Q * m) m (by nlinarith) pi b (by omega) 0 phase tail tailBound (some 0) (bandArchive pi 0 Q)
    (labels ∘ index) (distinct.comp index_injective)
  intro x; have band (n : ℕ) (hn : n = 1 ∨ n = 2) : ∀ i, i < Q → wordIncrement (Q * m)
        (-((n : ℕ) : ZMod (Q * m + 1)) + ((i * m : ℕ) : ZMod (Q * m + 1)))
        (bandWord pi 0 i) = 0 := by
    intro i hi; apply band_response Q m i n hQ hm hi hn
    intro eq; subst i
    exact root
  fin_cases x
  · obtain ⟨c, ex⟩ := success (1 : ZMod (Q * m + 1)) (band 1 (Or.inl rfl))
    have lab := low_label Q m hQ hm labels bottom 0 1 (by nlinarith)
    norm_num at lab
    rw [lab] at ex; exact ⟨c, by simpa [phase, index] using ex⟩
  · obtain ⟨c, ex⟩ := success (2 : ZMod (Q * m + 1)) (band 2 (Or.inr rfl))
    have lab := low_label Q m hQ hm labels bottom 0 2 (by nlinarith)
    norm_num at lab
    rw [lab] at ex; exact ⟨c, by simpa [phase, index] using ex⟩
  · obtain ⟨c, ex⟩ := success (j : ZMod (Q * m + 1)) zero
    rw [low_label Q m hQ hm labels bottom 0 j bound, ite_eq_right n1, ite_eq_right n2] at ex
    exact ⟨c, by simpa [phase, index] using ex⟩
#print axioms even_adaptive_lower

private def rootWord (m : ℕ) : Fin m → Bool := fun i => decide (i.val < 3 ∨ i.val % 2 = 0)
private def middleWord (m : ℕ) : Fin m → Bool := fun i => decide (i.val % 2 = if m % 2 = 0 then 1 else 0)

/-- The literal word 01 followed by zeros. -/
def queryWord (m : ℕ) : Fin m → Bool := fun i => decide (i.val = 1)
/-- The literal word 1 followed by zeros. -/
def finalWord (m : ℕ) : Fin m → Bool := fun i => decide (i.val = 0)

/-- The original odd/even streams, with every literal zero and every paid block retained. -/
def attainingWords (Q m : ℕ) : List (Fin m → Bool) := rootWord m :: (List.replicate (Q - 1) (middleWord m) ++
    queryWord m :: (if m % 2 = 0 then [finalWord m] else []))

private def literalProfile (Q m : ℕ) : List (Fin m → Bool) → ZMod (Q * m + 1) → List (Option (ZMod 2))
  | [], _ => []
  | B :: rest, j => some (wordIncrement (Q * m) (-j) B) :: literalProfile Q m rest (j - (m : ℕ))

private theorem profile_index (Q m : ℕ) (words : List (Fin m → Bool)) (j : ZMod (Q * m + 1)) (t : ℕ) :
    (literalProfile Q m words j)[t]? = (words[t]?).map
      (fun B => some (wordIncrement (Q * m) (-j + ((t * m : ℕ) : ZMod (Q * m + 1))) B)) := by
  induction words generalizing j t with
  | nil => simp [literalProfile]
  | cons B rest ih =>
    cases t with
    | zero => simp [literalProfile]
    | succ t =>
      simp only [literalProfile, List.getElem?_cons_succ, ih]; congr 2
      funext C; congr 2
      push_cast; ring

private theorem suffix_profile (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m) (words : List (Fin m → Bool))
    (zeros : ∀ B ∈ words, ∃ i : Fin m, i.val ≤ 1 ∧ B i = false)
    (v : ZMod 2) (j : ZMod (Q * m + 1)) (s : ℕ) (hs : s ≤ m - 1) :
    endpointDifferences (some v) ((scriptArchive words (some ⟨v, -j, s⟩)).map Prod.snd) =
      literalProfile Q m words j := by
  induction words generalizing v j s with
  | nil => rfl
  | cons B rest ih =>
    obtain ⟨i, hi, zero⟩ := zeros B (List.mem_cons_self ..)
    have short : m + 1 ≤ Q * m := by nlinarith
    have ex := InternalZeroSafety.internal_zero_execution (Q * m) (by nlinarith) m
      (by nlinarith) B i zero v (-j) s (by omega) (Or.inl (by omega))
    simp only [scriptArchive, ex.1, endpointReading, List.map_cons, endpointDifferences]
    have phase : -j + (m : ℕ) = -(j - (m : ℕ)) := by ring
    rw [phase]; change some (v + wordIncrement (Q * m) (-j) B - v) :: _ = _
    rw [add_sub_cancel_left, ih (fun C hc => zeros C (List.mem_cons_of_mem B hc)) _ _ _ (by omega)]; rfl

private theorem root_cut (m : ℕ) (hm : 4 ≤ m) :
    ∃ rest, List.ofFn (rootWord m) = List.replicate 3 true ++ false :: rest := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 4 := ⟨m - 4, by omega⟩
  refine ⟨List.ofFn (fun i : Fin n => rootWord (n + 4) ⟨i.val + 4, by have := i.isLt; omega⟩), ?_⟩
  simp only [List.ofFn_succ, List.replicate_succ, List.replicate_zero, List.nil_append, List.cons_append]
  simp only [rootWord, Fin.val_zero, Fin.val_succ]; norm_num

private theorem root_named_execution (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (v : ZMod 2) (phase : ZMod (Q * m + 1)) (s : ℕ) (hs : s < Q * m) :
    runBits (Q * m) (rootWord m) (some ⟨v, phase, s⟩) = if s < Q * m - 3 then
        some ⟨v + wordIncrement (Q * m) phase (rootWord m), phase + (m : ℕ), tailAfter 0 (rootWord m)⟩ else none := by
  obtain ⟨rest, cut⟩ := root_cut m hm
  have ex := first_zero_block_exact (Q * m) (by nlinarith) m 3 _ rest cut
    (short_legal (Q * m) m (by nlinarith) (by nlinarith) _) v phase s hs
  simpa only [show s + 3 < Q * m ↔ s < Q * m - 3 by omega] using ex

private theorem root_named_tail (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m) : tailAfter 0 (rootWord m) ≤ m - 4 := by
  have zero : rootWord m ⟨3, by omega⟩ = false := by simp [rootWord]
  have ex := InternalZeroSafety.internal_zero_execution (Q * m) (by nlinarith) m
    (by nlinarith) (rootWord m) ⟨3, by omega⟩ zero 0 0 0 (by nlinarith) (Or.inl (by nlinarith))
  simpa only [Fin.val_mk, show m - 1 - 3 = m - 4 by omega] using ex.2

private theorem suffix_zeros (Q m : ℕ) (hm : 4 ≤ m) :
    ∀ B ∈ (attainingWords Q m).tail, ∃ i : Fin m, i.val ≤ 1 ∧ B i = false := by
  intro B mem; simp only [attainingWords, List.tail_cons, List.mem_append, List.mem_replicate, List.mem_cons] at mem
  rcases mem with ⟨_, rfl⟩ | rfl | mem
  · by_cases even : m % 2 = 0
    · exact ⟨⟨0, by omega⟩, by simp, by simp [middleWord, even]⟩
    · exact ⟨⟨1, by omega⟩, by simp, by simp [middleWord, even]⟩
  · exact ⟨⟨0, by omega⟩, by simp, by simp [queryWord]⟩
  · by_cases even : m % 2 = 0
    · simp only [even, ite_true, List.mem_singleton] at mem; subst B
      exact ⟨⟨1, by omega⟩, by simp, by simp [finalWord]⟩
    · simp [even] at mem

private theorem root_mask (Q m j : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m) (hj : j ≤ Q * m) :
    wordIncrement (Q * m) (-((j : ℕ) : ZMod (Q * m + 1))) (rootWord m) = if j < m ∧ j ≠ 1 ∧ j ≠ 2 then 1 else
        if j = m ∧ m % 2 = 1 then 1 else 0 := by
  rw [derivative_at Q m j hQ hm (by omega)]; by_cases small : j < 4
  · interval_cases j <;>
      norm_num [extendedBit, rootWord, bitScalar, show 0 < m by omega,
        show 1 < m by omega, show 2 < m by omega, show 3 < m by omega,
        show (0 : ℕ) ≠ m by omega, show (1 : ℕ) ≠ m by omega,
        show (2 : ℕ) ≠ m by omega, show (3 : ℕ) ≠ m by omega] <;> try decide
  · by_cases inside : j < m
    · have prev : j - 1 < m := by omega
      rcases Nat.mod_two_eq_zero_or_one j with parity | parity
      · have pp : (j - 1) % 2 = 1 := by omega
        simp [extendedBit, inside, prev, rootWord, bitScalar, parity, pp,
          show ¬j < 3 by omega, show ¬j - 1 < 3 by omega,
          show j ≠ 0 by omega, show j ≠ 1 by omega, show j ≠ 2 by omega]
      · have pp : (j - 1) % 2 = 0 := by omega
        simp [extendedBit, inside, prev, rootWord, bitScalar, parity, pp,
          show ¬j < 3 by omega, show ¬j - 1 < 3 by omega,
          show j ≠ 0 by omega, show j ≠ 1 by omega, show j ≠ 2 by omega]
    · by_cases endpoint : j = m
      · subst j; have prev : m - 1 < m := by omega
        rcases Nat.mod_two_eq_zero_or_one m with parity | parity
        · have pp : (m - 1) % 2 = 1 := by omega
          simp [extendedBit, rootWord, bitScalar, parity, pp, prev, show ¬m - 1 < 3 by omega, show m ≠ 0 by omega]
        · have pp : (m - 1) % 2 = 0 := by omega
          simp [extendedBit, rootWord, bitScalar, parity, pp, prev, show ¬m - 1 < 3 by omega, show m ≠ 0 by omega]
      · simp [extendedBit, inside, endpoint, show j ≠ 0 by omega, show ¬j - 1 < m by omega]

private theorem middle_mask (Q m t i : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m) (hi : i ≤ m) : wordIncrement (Q * m)
      (-((t * m + i : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1)))
      (middleWord m) = if m % 2 = 0 ∧ i = 0 then 0 else 1 := by
  rw [response_at Q m t i hQ hm hi]; by_cases start : i = 0
  · subst i
    by_cases even : m % 2 = 0 <;>
      simp [extendedBit, middleWord, bitScalar, even, show 0 < m by omega]
  · by_cases finish : i = m
    · subst i; have prev : m - 1 < m := by omega
      rcases Nat.mod_two_eq_zero_or_one m with parity | parity
      · have pp : (m - 1) % 2 = 1 := by omega
        simp [extendedBit, middleWord, bitScalar, parity, pp, prev, show m ≠ 0 by omega]
      · have pp : (m - 1) % 2 = 0 := by omega
        simp [extendedBit, middleWord, bitScalar, parity, pp, prev, show m ≠ 0 by omega]
    · have inside : i < m := by omega
      have prev : i - 1 < m := by omega
      by_cases even : m % 2 = 0
      · rcases Nat.mod_two_eq_zero_or_one i with parity | parity
        · have pp : (i - 1) % 2 = 1 := by omega
          simp [extendedBit, middleWord, bitScalar, even, parity, pp, start, inside, prev]
        · have pp : (i - 1) % 2 = 0 := by omega
          simp [extendedBit, middleWord, bitScalar, even, parity, pp, start, inside, prev]
      · rcases Nat.mod_two_eq_zero_or_one i with parity | parity
        · have pp : (i - 1) % 2 = 1 := by omega
          simp [extendedBit, middleWord, bitScalar, even, parity, pp, start, inside, prev]
        · have pp : (i - 1) % 2 = 0 := by omega
          simp [extendedBit, middleWord, bitScalar, even, parity, pp, start, inside, prev]

private def scanWord (m t : ℕ) : Fin m → Bool := if t = 0 then rootWord m else middleWord m

private theorem scan_support (Q m j : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m) (hj : j ≤ Q * m) :
    (∀ t, t < Q → wordIncrement (Q * m)
      (-((j : ℕ) : ZMod (Q * m + 1)) + ((t * m : ℕ) : ZMod (Q * m + 1))) (scanWord m t) = 0) ↔
        j = 1 ∨ j = 2 ∨ (m % 2 = 0 ∧ j = m) := by
  constructor
  · intro zero; have root := zero 0 (by omega)
    simp only [scanWord, ite_true, Nat.zero_mul, Nat.cast_zero, add_zero, root_mask Q m j hQ hm hj] at root
    have outside : j = 1 ∨ j = 2 ∨ m ≤ j := by
      by_contra no
      rw [ite_eq_left (by omega)] at root; exact one_ne_zero root
    rcases outside with rfl | rfl | large
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · have boundary : j = m := by
        by_contra ne
        have strict : m < j := by omega
        let t := (j - 1) / m
        have divmod : (j - 1) % m + t * m = j - 1 := by simpa only [t, Nat.mul_comm] using Nat.mod_add_div (j - 1) m
        have rem := Nat.mod_lt (j - 1) (show 0 < m by omega)
        have tpos : 1 ≤ t := by
          have nonneg : 0 ≤ t := Nat.zero_le t
          by_contra no
          have eq : t = 0 := by omega
          rw [eq] at divmod; omega
        have tQ : t < Q := by
          by_contra no
          have mul := Nat.mul_le_mul_right m (show Q ≤ t by omega)
          omega
        let i := j - t * m
        have ile : i ≤ m := by dsimp [i]; omega
        have ipos : 0 < i := by dsimp [i]; omega
        have jie : j = t * m + i := by dsimp [i]; omega
        have hit := zero t tQ
        rw [scanWord, ite_eq_right (by omega), jie, middle_mask Q m t i hQ hm ile, ite_eq_right (by omega)] at hit
        exact one_ne_zero hit
      subst j
      have even : m % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one m with h | h
        · exact h
        · simp [h] at root
      exact Or.inr (Or.inr ⟨even, rfl⟩)
  · intro supported t ht; rcases supported with eq | eq | ⟨even, eq⟩
    · subst j; apply band_response Q m t 1 hQ hm ht (Or.inl rfl)
      intro eq; subst t
      simpa only [scanWord, ite_true] using root_cut m hm
    · subst j; apply band_response Q m t 2 hQ hm ht (Or.inr rfl)
      intro eq; subst t
      simpa only [scanWord, ite_true] using root_cut m hm
    · subst j; by_cases first : t = 0
      · subst t; simp [scanWord, root_mask Q m m hQ hm (by nlinarith), even]
      · by_cases second : t = 1
        · subst t; have hit := middle_mask Q m 1 0 hQ hm (by omega)
          simpa [scanWord, even] using hit
        · apply response_off Q m t m hQ hm ht (by nlinarith)
          have mul := Nat.mul_le_mul_right m (show 2 ≤ t by omega)
          exact Or.inl (by nlinarith)

private theorem attaining_scan (Q m t : ℕ) (hQ : 2 ≤ Q) (ht : t < Q) :
    (attainingWords Q m)[t]? = some (scanWord m t) := by
  cases t with
  | zero => simp [attainingWords, scanWord]
  | succ t =>
    have before : t < Q - 1 := by omega
    simp [attainingWords, scanWord, List.getElem?_append, before]

private theorem attaining_query (Q m : ℕ) (hQ : 2 ≤ Q) : (attainingWords Q m)[Q]? = some (queryWord m) := by
  obtain ⟨q, eq⟩ : ∃ q, Q = q + 1 := ⟨Q - 1, by omega⟩
  subst Q; simp [attainingWords]

private theorem attaining_final (Q m : ℕ) (hQ : 2 ≤ Q) (even : m % 2 = 0) :
    (attainingWords Q m)[Q + 1]? = some (finalWord m) := by
  obtain ⟨q, eq⟩ : ∃ q, Q = q + 1 := ⟨Q - 1, by omega⟩
  subst Q; simp [attainingWords, even]

private theorem named_profile (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (v : ZMod 2) (j : ZMod (Q * m + 1)) (s : ℕ) (hs : s < Q * m - 3) :
    endpointDifferences (some v) ((scriptArchive (attainingWords Q m) (some ⟨v, -j, s⟩)).map Prod.snd) =
      literalProfile Q m (attainingWords Q m) j := by
  have ex := root_named_execution Q m hQ hm v (-j) s (by omega)
  rw [ite_eq_left hs] at ex; change endpointDifferences (some v)
    (((rootWord m, endpointReading (runBits (Q * m) (rootWord m) (some ⟨v, -j, s⟩))) ::
      scriptArchive (attainingWords Q m).tail (runBits (Q * m) (rootWord m) (some ⟨v, -j, s⟩))).map Prod.snd) = _
  rw [ex]; simp only [List.map_cons, endpointReading, endpointDifferences]
  have phase : -j + (m : ℕ) = -(j - (m : ℕ)) := by ring
  rw [phase]; change some (v + wordIncrement (Q * m) (-j) (rootWord m) - v) :: _ = _
  rw [add_sub_cancel_left, suffix_profile Q m hQ hm _ (suffix_zeros Q m hm) _ _ _
      (by have := root_named_tail Q m hQ hm; omega)]
  rfl

private theorem query_full_mask (Q m j : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m) (hj : j ≤ Q * m) : wordIncrement (Q * m)
      (-((j : ℕ) : ZMod (Q * m + 1)) + ((Q * m : ℕ) : ZMod (Q * m + 1)))
      (queryWord m) = if j = 0 ∨ j = 1 then 1 else 0 := by
  by_cases last : j = Q * m
  · subst j; have phase : -((Q * m : ℕ) : ZMod (Q * m + 1)) +
        ((Q * m : ℕ) : ZMod (Q * m + 1)) = -((0 : ℕ) : ZMod (Q * m + 1)) := by ring
    rw [phase, derivative_at Q m 0 hQ hm (by nlinarith)]; simp [extendedBit, queryWord, bitScalar, show 0 < m by omega,
      show Q * m ≠ 0 by nlinarith, show Q * m ≠ 1 by nlinarith]
  · have total := ZMod.natCast_self (Q * m + 1)
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul] at total
    have phase : -((j : ℕ) : ZMod (Q * m + 1)) + ((Q * m : ℕ) : ZMod (Q * m + 1)) =
        -((j + 1 : ℕ) : ZMod (Q * m + 1)) := by
      push_cast; linear_combination total
    rw [phase, derivative_at Q m (j + 1) hQ hm (by omega)]; by_cases j0 : j = 0
    · subst j; simp [extendedBit, queryWord, bitScalar, show 1 < m by omega]
    · by_cases j1 : j = 1
      · subst j; simp [extendedBit, queryWord, bitScalar, show 1 < m by omega, show 2 < m by omega]
      · have ne : j + 1 ≠ 1 := by omega
        simp [extendedBit, queryWord, bitScalar, j0, j1]

private theorem query_mask (Q m j : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m) (hj : j ≤ m) : wordIncrement (Q * m)
      (-((j : ℕ) : ZMod (Q * m + 1)) + ((Q * m : ℕ) : ZMod (Q * m + 1)))
      (queryWord m) = if j = 0 ∨ j = 1 then 1 else 0 :=
  query_full_mask Q m j hQ hm (by nlinarith)

private theorem final_full_mask (Q m j : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m) (hj : j ≤ Q * m) : wordIncrement (Q * m)
      (-((j : ℕ) : ZMod (Q * m + 1)) + (((Q + 1) * m : ℕ) : ZMod (Q * m + 1)))
      (finalWord m) = if j = m - 1 ∨ j = m then 1 else 0 := by
  have total := ZMod.natCast_self (Q * m + 1)
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul] at total; have product : 2 * m ≤ Q * m := by nlinarith
  by_cases after : m - 1 ≤ j
  · let n := j + 1 - m
    have hn : n < Q * m + 1 := by dsimp [n]; omega
    have phase : -((j : ℕ) : ZMod (Q * m + 1)) +
        (((Q + 1) * m : ℕ) : ZMod (Q * m + 1)) = -((n : ℕ) : ZMod (Q * m + 1)) := by
      dsimp [n]; rw [Nat.cast_sub (by omega : m ≤ j + 1)]
      push_cast; linear_combination total
    rw [phase, derivative_at Q m n hQ hm hn]
    have test : (j = m - 1 ∨ j = m) ↔ (n = 0 ∨ n = 1) := by dsimp [n]; omega
    simp only [test]; by_cases zero : n = 0
    · rw [zero]; simp [extendedBit, finalWord, bitScalar, show 0 < m by omega]
    · by_cases one : n = 1
      · rw [one]; simp [extendedBit, finalWord, bitScalar, show 0 < m by omega, show 1 < m by omega]
      · simp [extendedBit, finalWord, bitScalar, zero, one, show n - 1 ≠ 0 by omega]
  · let n := Q * m + 2 + j - m
    have hn : m < n ∧ n < Q * m + 1 := by dsimp [n]; omega
    have phase : -((j : ℕ) : ZMod (Q * m + 1)) +
        (((Q + 1) * m : ℕ) : ZMod (Q * m + 1)) = -((n : ℕ) : ZMod (Q * m + 1)) := by
      dsimp [n]; rw [Nat.cast_sub (by omega : m ≤ Q * m + 2 + j)]
      push_cast; linear_combination 2 * total
    rw [phase, derivative_at Q m n hQ hm hn.2]; simp [extendedBit, show ¬ n < m by omega, show n ≠ 0 by omega,
      show ¬ n - 1 < m by omega, show j ≠ m - 1 by omega, show j ≠ m by omega]

private theorem final_band_mask (Q m j : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m) (band : j = 1 ∨ j = 2 ∨ j = m) :
    wordIncrement (Q * m) (-((j : ℕ) : ZMod (Q * m + 1)) + (((Q + 1) * m : ℕ) : ZMod (Q * m + 1)))
      (finalWord m) = if j = m then 1 else 0 := by
  rw [final_full_mask Q m j hQ hm (by rcases band with h | h | h <;> subst j <;> nlinarith)]
  have different : j ≠ m - 1 := by rcases band with h | h | h <;> omega
  simp [different]

private theorem profile_band_identifies (Q m i j : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m) (hi : i = 1 ∨ i = 2) (hj : j ≤ Q * m)
    (same : literalProfile Q m (attainingWords Q m) (i : ZMod (Q * m + 1)) =
      literalProfile Q m (attainingWords Q m) (j : ZMod (Q * m + 1))) : i = j := by
  have readat (t : ℕ) := congrArg (fun ar => ar[t]?) same
  have supported : j = 1 ∨ j = 2 ∨ (m % 2 = 0 ∧ j = m) := by
    apply (scan_support Q m j hQ hm hj).mp
    intro t ht; have eq := readat t
    rw [profile_index, profile_index, attaining_scan Q m t hQ ht] at eq
    simp only [Option.map_some, Option.some.injEq] at eq
    have zero := (scan_support Q m i hQ hm (by rcases hi with rfl | rfl <;> nlinarith)).mpr (by
        rcases hi with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)) t ht
    exact eq.symm.trans zero
  have query := readat Q
  rw [profile_index, profile_index, attaining_query Q m hQ] at query
  simp only [Option.map_some, Option.some.injEq] at query
  rw [query_mask Q m i hQ hm (by rcases hi with rfl | rfl <;> omega),
    query_mask Q m j hQ hm (by rcases supported with rfl | rfl | ⟨_, rfl⟩ <;> omega)] at query
  rcases hi with rfl | rfl
  · rcases supported with eq | eq | ⟨even, eq⟩
    · exact eq.symm
    · subst j; norm_num at query
    · subst j; simp [show m ≠ 0 by omega, show m ≠ 1 by omega] at query
  · rcases supported with eq | eq | ⟨even, eq⟩
    · subst j; norm_num at query
    · exact eq.symm
    · subst j; have last := readat (Q + 1)
      rw [profile_index, profile_index, attaining_final Q m hQ even] at last
      simp only [Option.map_some, Option.some.injEq] at last
      rw [final_band_mask Q m 2 hQ hm (Or.inr (Or.inl rfl)), final_band_mask Q m m hQ hm (Or.inr (Or.inr rfl))] at last
      simp [show (2 : ℕ) ≠ m by omega] at last

private theorem archive_separates {Y : Type u} (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (labels : Fin 4 → Y) (bottom : Y) (v : ZMod 2) (p q : ZMod (Q * m + 1)) (s r : ℕ) (hs : s < Q * m) (hr : r < Q * m)
    (same : scriptArchive (attainingWords Q m) (some ⟨v, p, s⟩) = scriptArchive (attainingWords Q m) (some ⟨v, q, r⟩)) :
    initialLabel Q m labels bottom (some ⟨v, p, s⟩) = initialLabel Q m labels bottom (some ⟨v, q, r⟩) := by
  let i := (-p).val
  let j := (-q).val
  have ip : -((i : ℕ) : ZMod (Q * m + 1)) = p := by simp [i]
  have jq : -((j : ℕ) : ZMod (Q * m + 1)) = q := by simp [j]
  have hi : i ≤ Q * m := by have := ZMod.val_lt (-p); omega
  have hj : j ≤ Q * m := by have := ZMod.val_lt (-q); omega
  have head := congrArg List.head? same
  change some (rootWord m, endpointReading (runBits (Q * m) (rootWord m) (some ⟨v, p, s⟩))) =
    some (rootWord m, endpointReading (runBits (Q * m) (rootWord m) (some ⟨v, q, r⟩))) at head
  have reply := congrArg Prod.snd (Option.some.inj head)
  rw [root_named_execution Q m hQ hm _ _ _ hs, root_named_execution Q m hQ hm _ _ _ hr] at reply
  by_cases lowS : s < Q * m - 3
  · have lowR : r < Q * m - 3 := by
      by_contra no
      simp [lowS, no, endpointReading] at reply
    have profiles := congrArg (fun ar => endpointDifferences (some v) (ar.map Prod.snd)) same
    rw [←ip, ←jq, named_profile Q m hQ hm _ _ _ lowS, named_profile Q m hQ hm _ _ _ lowR] at profiles
    simp only [initialLabel, ite_eq_right (by omega : ¬Q * m - 3 ≤ s), ite_eq_right (by omega : ¬Q * m - 3 ≤ r)]
    change (if i = 1 then labels 1 else if i = 2 then labels 2 else labels 0) =
      (if j = 1 then labels 1 else if j = 2 then labels 2 else labels 0)
    by_cases i1 : i = 1
    · have ij := profile_band_identifies Q m i j hQ hm (Or.inl i1) hj profiles
      rw [ij]
    · by_cases i2 : i = 2
      · have ij := profile_band_identifies Q m i j hQ hm (Or.inr i2) hj profiles
        rw [ij]
      · have j1 : j ≠ 1 := by
          intro eq; have ij := profile_band_identifies Q m j i hQ hm (Or.inl eq) hi profiles.symm
          omega
        have j2 : j ≠ 2 := by
          intro eq; have ij := profile_band_identifies Q m j i hQ hm (Or.inr eq) hi profiles.symm
          omega
        simp [i1, i2, j1, j2]
  · have highR : ¬r < Q * m - 3 := by
      intro lowR; simp [lowS, lowR, endpointReading] at reply
    simp [initialLabel, show Q * m - 3 ≤ s by omega, show Q * m - 3 ≤ r by omega]

/-- The endpoint decoder returns the immutable label of any compatible
original initial record; compatibility uses the complete actual script archive. -/
def archiveDecoder {Y : Type u} (Q m : ℕ) (labels : Fin 4 → Y) (bottom : Y)
    (v : ZMod 2) (ar : NarrowWindowCost.Archive m) : Y :=
  if h : ∃ (phase : ZMod (Q * m + 1)) (s : ℕ), s < Q * m ∧
      scriptArchive (attainingWords Q m) (some ⟨v, phase, s⟩) = ar then
    initialLabel Q m labels bottom (some ⟨v, Classical.choose h, Classical.choose (Classical.choose_spec h)⟩)
  else bottom

private theorem archive_decode {Y : Type u} (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (labels : Fin 4 → Y) (bottom : Y) (v : ZMod 2) (phase : ZMod (Q * m + 1)) (s : ℕ) (hs : s < Q * m) :
    archiveDecoder Q m labels bottom v (scriptArchive (attainingWords Q m) (some ⟨v, phase, s⟩)) =
      initialLabel Q m labels bottom (some ⟨v, phase, s⟩) := by
  have h : ∃ (p : ZMod (Q * m + 1)) (r : ℕ), r < Q * m ∧ scriptArchive (attainingWords Q m) (some ⟨v, p, r⟩) =
        scriptArchive (attainingWords Q m) (some ⟨v, phase, s⟩) := ⟨phase, s, hs, rfl⟩
  rw [archiveDecoder, dite_eq_left h]; have fact := Classical.choose_spec (Classical.choose_spec h)
  exact archive_separates Q m hQ hm labels bottom v _ _ _ _ fact.1 hs fact.2

private theorem baseline_lower {Y : Type u} (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (labels : Fin 4 → Y) (distinct : Function.Injective labels) (bottom : Y) (alphabet : Bool) (d : ℕ)
    (feasible : OriginalAdaptiveFeasible (Q * m) m (by nlinarith) alphabet
      (initialLabel Q m labels bottom) d) : Q + 1 ≤ d := by
  classical
  let sample (i : Fin m) := initialLabel Q m labels bottom (some ⟨(0 : ZMod 2), -((i.val : ℕ) : ZMod (Q * m + 1)), 0⟩)
  let tri (i : Fin 3) := labels (Fin.castLE (by decide : 3 ≤ 4) i)
  have trinj : Function.Injective tri := distinct.comp (by
    intro i j h; exact Fin.ext (congrArg (fun x : Fin 4 => x.val) h))
  have range : Set.range sample = Set.range tri := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      have lab := low_label Q m hQ hm labels bottom 0 i.val (by have := i.isLt; nlinarith)
      dsimp only [sample]; rw [lab]
      by_cases one : i.val = 1
      · exact ⟨1, by simp [tri, one]⟩
      · by_cases two : i.val = 2
        · exact ⟨2, by simp [tri, two]⟩
        · exact ⟨0, by simp [tri, one, two]⟩
    · rintro ⟨c, rfl⟩; fin_cases c
      · refine ⟨⟨0, by omega⟩, ?_⟩
        dsimp only [sample]; rw [low_label Q m hQ hm labels bottom 0 0 (by nlinarith)]
        norm_num [tri]
      · refine ⟨⟨1, by omega⟩, ?_⟩
        dsimp only [sample]; rw [low_label Q m hQ hm labels bottom 0 1 (by nlinarith)]
        norm_num [tri]
      · refine ⟨⟨2, by omega⟩, ?_⟩
        dsimp only [sample]; rw [low_label Q m hQ hm labels bottom 0 2 (by nlinarith)]
        norm_num [tri]
  have card : Nat.card (Set.range sample) = 3 := by rw [range, Nat.card_range_of_injective trinj, Nat.card_fin]
  have gcd : Nat.gcd m (Q * m + 1) = 1 := by
    rw [Nat.mul_comm Q m, Nat.gcd_mul_left_add_right]; simp
  let g := Nat.gcd m (Q * m + 1)
  have g1 : g = 1 := gcd
  let originalSample (j : Fin (m / g)) := initialLabel Q m labels bottom
    (some ⟨(0 : ZMod 2), -((j.val * g : ℕ) : ZMod (Q * m + 1)), 0⟩)
  have count : Nat.card (Set.range originalSample) = 3 := by
    dsimp only [originalSample]; conv_lhs => rw [g1, Nat.div_one]
    simpa only [Nat.mul_one, sample] using card
  have lower := original_cost_lower (Q * m) m (by nlinarith) (by omega) (by nlinarith)
    (initialLabel Q m labels bottom) 0 alphabet
    (show 3 ≤ Nat.card (Set.range originalSample) by rw [count])
  have wait : (Q * m + 1) / m = Q := by apply Nat.div_eq_of_lt_le <;> nlinarith
  change (((((Q * m + 1) / g) / (m / g)) + Nat.clog 2 (Nat.card (Set.range originalSample)) - 1 : ℕ) : ℕ∞) ≤ _ at lower
  rw [count, g1] at lower; have bound : ((Q + 1 : ℕ) : ℕ∞) ≤
      OriginalFiberCost (Q * m) m (by nlinarith) alphabet (initialLabel Q m labels bottom) 0 := by
    simpa only [Nat.div_one, wait, show Nat.clog 2 3 = 2 by decide, show Q + 2 - 1 = Q + 1 by omega] using lower
  obtain ⟨pi, legal, bot, correct⟩ := feasible
  have fiber : OriginalFiberFeasible (Q * m) m (by nlinarith) alphabet (initialLabel Q m labels bottom) 0 d := by
    refine ⟨pi, legal, bot, ?_⟩
    intro history; dsimp only
    intro obs; obtain ⟨c, le, ex⟩ := correct history
    rw [obs] at ex; exact ⟨c, le, ex⟩
  have finite : OriginalFiberCost (Q * m) m (by nlinarith) alphabet (initialLabel Q m labels bottom) 0 ≤ (d : ℕ∞) :=
    iInf_le_of_le ⟨d, fiber⟩ le_rfl
  exact_mod_cast bound.trans finite

private theorem literal_end_tails (m : ℕ) (hm : 4 ≤ m) (s : ℕ) :
    tailAfter s (queryWord m) = 0 ∧ tailAfter s (finalWord m) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  constructor
  · apply last_false_tail
    simp [queryWord, show n ≠ 1 by omega]
  · apply last_false_tail
    simp [finalWord, show n ≠ 0 by omega]

/-- Both original global prices and the complete same-history attaining trace.
The initial bottom branch returns freely; every other branch retains the full
literal stream and returns its original immutable target. -/
theorem original_threshold_three {Y : Type u} (Q m : ℕ) (hQ : 2 ≤ Q) (hm : 4 ≤ m)
    (labels : Fin 4 → Y) (distinct : Function.Injective labels) (bottom : Y) (alphabet : Bool) :
    let fee := Q + 1 + (if m % 2 = 0 then 1 else 0)
    GlobalAdaptivePrice (Q * m) m (by nlinarith) alphabet (initialLabel Q m labels bottom) = (fee : ℕ∞) ∧
    GlobalPresetPrice (Q * m) m (by nlinarith) alphabet (initialLabel Q m labels bottom) = (fee : ℕ∞) ∧
    (attainingWords Q m).length = fee ∧
    (∀ s, tailAfter s (queryWord m) = 0 ∧ tailAfter s (finalWord m) = 0) ∧
    (attainingWords 2 4).map List.ofFn = [[true,true,true,false], [false,true,false,true],
        [false,true,false,false], [true,false,false,false]] ∧
    (attainingWords 2 5).map List.ofFn = [[true,true,true,false,true], [true,false,true,false,true],
        [false,true,false,false,false]] ∧
    ∀ history : List (AllowedBlock (Q * m) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let f := initialLabel Q m labels bottom
      let decode := archiveDecoder Q m labels bottom
      let pi : NarrowWindowCost.Selector m Y := fun free ar =>
        match free with
        | none => .inl bottom
        | some v => finalSelector 0 (attainingWords Q m) (decode v) free ar
      let q := OriginalRecord (Q * m) (by nlinarith) w
      let issued := if q = none then [] else scriptArchive (attainingWords Q m) q
      PaidTrace pi (NarrowWindowCost.output (Q * m) (by nlinarith) w) q [] issued (f q) ∧
      issued.map Prod.fst = (if q = none then [] else attainingWords Q m) ∧
      issued.length = (if q = none then 0 else fee) ∧
      NarrowWindowCost.execute (Q * m) (by nlinarith) pi fee w (NarrowWindowCost.output (Q * m) (by nlinarith) w) [] =
          some (f q, issued.length) := by
  classical
  dsimp only
  let fee := Q + 1 + (if m % 2 = 0 then 1 else 0)
  have len : (attainingWords Q m).length = fee := by
    dsimp [attainingWords, fee]
    split_ifs <;> simp <;> omega
  have lower (d : ℕ) (feasible : OriginalAdaptiveFeasible (Q * m) m (by nlinarith)
      alphabet (initialLabel Q m labels bottom) d) : fee ≤ d := by
    dsimp only [fee]; by_cases even : m % 2 = 0
    · rw [ite_eq_left even]; have parity : Even m := (Nat.even_iff.mpr even)
      exact even_adaptive_lower Q m hQ hm parity labels distinct bottom alphabet d feasible
    · rw [ite_eq_right even, Nat.add_zero]; exact baseline_lower Q m hQ hm labels distinct bottom alphabet d feasible
  have upper : OriginalPresetFeasible (Q * m) m (by nlinarith) alphabet (initialLabel Q m labels bottom) fee := by
    rw [←len]; exact script_global_preset (Q * m) m (by nlinarith) (by nlinarith) alphabet
      (initialLabel Q m labels bottom) (attainingWords Q m) (archiveDecoder Q m labels bottom)
      (archive_decode Q m hQ hm labels bottom)
  refine ⟨FullPositiveWindowPrice.price_exact _ _ (preset_inclusion _ _ _ _ _ _ upper) lower,
    FullPositiveWindowPrice.price_exact _ _ upper (fun d h => lower d (preset_inclusion _ _ _ _ _ _ h)), len,
      literal_end_tails m hm, by decide, by decide, ?_⟩
  intro history; let w := history.flatMap (fun a => List.ofFn a.val)
  let f := initialLabel Q m labels bottom
  let decode := archiveDecoder Q m labels bottom
  let pi : NarrowWindowCost.Selector m Y := fun free ar =>
    match free with
    | none => .inl bottom
    | some v => finalSelector 0 (attainingWords Q m) (decode v) free ar
  have output : NarrowWindowCost.output (Q * m) (by nlinarith) w =
      endpointReading (OriginalRecord (Q * m) (by nlinarith) w) := output_record _ _ _
  cases initial : OriginalRecord (Q * m) (by nlinarith) w with
  | none =>
    simp only [initial, ite_true, endpointReading] at output ⊢; rw [output]
    refine ⟨rfl, rfl, rfl, ?_⟩
    rw [execute_same _ m (by nlinarith)]
    change NativeExecute pi fee (OriginalRecord (Q * m) (by nlinarith) w) none [] = some (f none, 0)
    rw [initial]
    cases fee <;> rfl
  | some q =>
    have hs : q.tail < Q * m := by
      unfold OriginalRecord at initial
      cases scan : (NarrowWindowCost.scanner (Q * m) (by nlinarith)).eval w with
      | none => simp [scan] at initial
      | some tail =>
        simp only [scan, Option.map_some, Option.some.injEq] at initial; have eq := congrArg LiveRecord.tail initial
        simpa only [←eq] using tail.isLt
    have qe : (⟨q.value, q.phase, q.tail⟩ : LiveRecord (Q * m)) = q := by cases q; rfl
    have decoded := archive_decode Q m hQ hm labels bottom q.value q.phase q.tail hs
    rw [qe] at decoded; have script := original_final_script (Q * m) m (by nlinarith) (attainingWords Q m)
      (decode q.value) w (some q.value) []
    dsimp only at script; rw [initial] at script
    have same (ar : NarrowWindowCost.Archive m) : pi (some q.value) ar =
          finalSelector 0 (attainingWords Q m) (decode q.value) (some q.value) ar := rfl
    have trace := (FullPositiveWindowPrice.trace_congr _ _ (some q.value) same _ _ [] _).mpr script.1
    change decode q.value (scriptArchive (attainingWords Q m) (some q)) = f (some q) at decoded
    rw [decoded] at trace; simp only [initial, Option.some_ne_none, ite_false, endpointReading] at output ⊢
    rw [output]; refine ⟨trace, script.2.1, script.2.2.1.trans len, ?_⟩
    rw [execute_paid_trace _ m (by nlinarith), initial]; exact ⟨_, trace, rfl, by rw [script.2.2.1, len]⟩
#print axioms original_threshold_three

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.TwoAdjacentLowTailLabels
