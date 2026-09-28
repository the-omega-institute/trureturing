/- GID: D5/S3/Observer/Budget/FiniteCutoffProtocolRecursion
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/FiniteCutoffProtocolRecursion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Deadline identification decomposes over actual first-response fibers. -/

import D5.S3.Observer.Budget.DyadicForwardWaitingOptimality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.FiniteCutoffProtocolRecursion

open DyadicForwardWaitingOptimality

/-- The physical block readout after forward unit evolution on the finite cycle. -/
def response (p P b t r : Nat) : Nat := ((b * P + r + t) % (p * P)) / P

/-- Decode the two possible physical symbols using the known clock and initial block.
The zero bit is the uncarried block label; the one bit is its successor modulo p. -/
def responseBit (p P b t r : Nat) : Fin 2 :=
  if response p P b t r = (b + t / P) % p then 0 else 1

/-- Successful bounded execution, rather than a recursively specified feasibility test.
The controller's budget index bounds every path; waiting increments may be zero. -/
def FiniteCutoff (p P b q : Nat) (A : Finset Nat) (n D : Nat) : Prop :=
  ∃ T : Protocol q, ∀ r ∈ A,
    (execute (responseBit p P b) T n r).1 = r ∧
      (execute (responseBit p P b) T n r).2 ≤ D

/-- The original candidates compatible with one actual physical response. -/
def responseFiber (p P b : Nat) (A : Finset Nat) (t y : Nat) : Finset Nat :=
  A.filter (fun r => response p P b t r = y)

/-- Zero queries identify exactly a singleton. At positive budget, identification
by the common deadline is equivalent to one common first read followed by successful
controllers for every actual response fiber. All finite block lengths and bases occur. -/
theorem finite_cutoff_branch_recursion
    (p P : Nat) (hp : 2 ≤ p) (b : Fin p) (A : Finset Nat)
    (hne : A.Nonempty) (hA : ∀ r ∈ A, r < P) (n D : Nat) (hn : n ≤ D) (q : Nat) :
    (FiniteCutoff p P b.val 0 A n D ↔ A.card = 1) ∧
    (FiniteCutoff p P b.val (q + 1) A n D ↔
      A.card = 1 ∨ ∃ t, n ≤ t ∧ t ≤ D ∧
        ∀ y ∈ A.image (response p P b.val t),
          FiniteCutoff p P b.val q (responseFiber p P b.val A t y) t D) := by
  classical
  obtain ⟨r₀, hr₀⟩ := hne
  have hP : 0 < P := by have := hA r₀ hr₀; omega
  -- Physical symbols are a known relabelling of the existing decoded sensor.
  have labels (t r : Nat) (hr : r < P) :
      response p P b.val t r = (b.val + t / P + (sensor P 0 t r).val) % p := by
    have hsum : (r + t) / P = t / P + (threshold P t r).val := by
      have carry : (r + t % P) / P = (threshold P t r).val := by
        have ht := Nat.mod_lt t hP
        unfold threshold
        split_ifs with h
        · exact Nat.div_eq_of_lt (by omega)
        · apply Nat.div_eq_of_lt_le (by omega)
          omega
      have clock := Nat.mod_add_div t P
      rw [show r + t = r + t % P + P * (t / P) by omega,
        Nat.add_mul_div_left _ _ hP, carry]
      omega
    have decoded : sensor P 0 t r = threshold P t r := by
      apply Fin.ext
      have ht := (threshold P t r).isLt
      change ((((0 * P + r + t) / P) % 2 + 0 + t / P) % 2) = _
      simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero, hsum]
      omega
    rw [decoded]
    unfold response
    rw [Nat.mul_comm p P, Nat.mod_mul_right_div_self,
      show b.val * P + r + t = (r + t) + P * b.val by rw [Nat.mul_comm P b.val]; omega,
      Nat.add_mul_div_left _ _ hP, hsum]
    congr 1
    omega
  have injectiveLabels (t : Nat) : Function.Injective
      (fun bit : Fin 2 => (b.val + t / P + bit.val) % p) := by
    intro x z hxz
    have hc := Nat.ModEq.add_left_cancel' (b.val + t / P) hxz
    apply Fin.ext
    exact (Nat.mod_eq_of_lt (x.isLt.trans_le hp)).symm.trans
      (Eq.trans hc (Nat.mod_eq_of_lt (z.isLt.trans_le hp)))
  have decoded (t r : Nat) (hr : r < P) :
      responseBit p P b.val t r = sensor P 0 t r := by
    have hz : response p P b.val t r = (b.val + t / P) % p ↔
        sensor P 0 t r = 0 := by
      rw [labels t r hr]
      exact ⟨fun h => injectiveLabels t (by simpa only [Fin.val_zero, Nat.add_zero] using h),
        fun h => by rw [h]; rfl⟩
    unfold responseBit
    by_cases h : sensor P 0 t r = 0
    · rw [if_pos (hz.mpr h), h]
    · rw [if_neg (mt hz.mp h)]
      apply Fin.ext
      have ht := (sensor P 0 t r).isLt
      have hnz : (sensor P 0 t r).val ≠ 0 := fun he => h (Fin.ext he)
      change 1 = _
      omega
  have sameFiber (t r s : Nat) (hr : r ∈ A) (hs : s ∈ A) :
      response p P b.val t r = response p P b.val t s ↔
        responseBit p P b.val t r = responseBit p P b.val t s := by
    rw [labels t r (hA r hr), labels t s (hA s hs),
      decoded t r (hA r hr), decoded t s (hA s hs)]
    exact ⟨fun h => injectiveLabels t h,
      fun h => congrArg (fun bit : Fin 2 => (b.val + t / P + bit.val) % p) h⟩
  have mono : ∀ {d} (T : Protocol d) t r,
      t ≤ (execute (responseBit p P b.val) T t r).2 := by
    intro d T
    induction T with
    | stop answer => intros; exact le_rfl
    | query wait next ih =>
      intro t r
      exact (Nat.le_add_right t wait).trans (ih _ _ _)
  have singleton (d : Nat) (h : A.card = 1) : FiniteCutoff p P b.val d A n D := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    refine ⟨.stop a, ?_⟩
    intro r hr
    have he : r = a := by simpa only [ha, Finset.mem_singleton] using hr
    subst r
    exact ⟨rfl, hn⟩
  have stopped (d a : Nat)
      (h : ∀ r ∈ A, (execute (responseBit p P b.val) (Protocol.stop (d := d) a) n r).1 = r) :
      A.card = 1 := by
    apply Nat.le_antisymm (Finset.card_le_one.mpr ?_) (Finset.card_pos.mpr ⟨r₀, hr₀⟩)
    intro r hr s hs
    exact (h r hr).symm.trans (h s hs)
  constructor
  · constructor
    · rintro ⟨T, hT⟩
      cases T with
      | stop a => exact stopped 0 a (fun r hr => (hT r hr).1)
    · exact singleton 0
  · constructor
    · rintro ⟨T, hT⟩
      cases T with
      | stop a => exact Or.inl (stopped (q + 1) a (fun r hr => (hT r hr).1))
      | query wait next =>
        have ht : n + wait ≤ D :=
          (mono (next (responseBit p P b.val (n + wait) r₀)) (n + wait) r₀).trans
            (hT r₀ hr₀).2
        refine Or.inr ⟨n + wait, by omega, ht, ?_⟩
        intro y hy
        obtain ⟨s, hs, hsy⟩ := Finset.mem_image.mp hy
        refine ⟨next (responseBit p P b.val (n + wait) s), ?_⟩
        intro r hr
        obtain ⟨hrA, hry⟩ := Finset.mem_filter.mp hr
        have he := (sameFiber (n + wait) r s hrA hs).mp (hry.trans hsy.symm)
        simpa only [execute, he] using hT r hrA
    · rintro (h | ⟨t, hnt, htD, branches⟩)
      · exact singleton (q + 1) h
      · have select (bit : Fin 2) : ∃ T : Protocol q, ∀ r ∈ A,
            responseBit p P b.val t r = bit →
            (execute (responseBit p P b.val) T t r).1 = r ∧
              (execute (responseBit p P b.val) T t r).2 ≤ D := by
          by_cases hx : ∃ s ∈ A, responseBit p P b.val t s = bit
          · obtain ⟨s, hs, hsb⟩ := hx
            obtain ⟨T, hT⟩ := branches (response p P b.val t s)
              (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
            refine ⟨T, ?_⟩
            intro r hr hrb
            exact hT r (Finset.mem_filter.mpr ⟨hr,
              (sameFiber t r s hr hs).mpr (hrb.trans hsb.symm)⟩)
          · refine ⟨.stop 0, ?_⟩
            intro r hr hrb
            exact False.elim (hx ⟨r, hr, hrb⟩)
        choose next correct using select
        refine ⟨.query (t - n) next, ?_⟩
        intro r hr
        simpa only [execute, Nat.add_sub_of_le hnt] using
          correct (responseBit p P b.val t r) r hr rfl

#print axioms finite_cutoff_branch_recursion

end D5.S3.Observer.Budget.FiniteCutoffProtocolRecursion
