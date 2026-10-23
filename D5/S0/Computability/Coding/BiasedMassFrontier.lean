/- GID: D5/S0/Computability/Coding/BiasedMassFrontier
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/BiasedMassFrontier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First mass crossings in a biased binary tree form a finite conservative ray partition. -/

import D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality

/-! First weak mass crossings in the actual binary product tree. -/

open scoped BigOperators

namespace D5.S0.Computability.Coding.BiasedMassFrontier

open DepthBudgetIidGreedyOptimality PrefixFreeCode

/-- Actual binary letter probabilities, with the heavier letter first. -/
def letterMass (a b : ℝ) : Bool → ℝ := fun c => if c then b else a

/-- The first weak crossing; deleting the last letter gives the parent. -/
def Crossing (a b t : ℝ) : Set (List Bool) :=
  {w | w ≠ [] ∧ wordMass (letterMass a b) w ≤ t ∧
    t < wordMass (letterMass a b) w.dropLast}

/-- The finite prefix of an infinite binary ray. -/
def rayPrefix (ω : ℕ → Bool) (n : ℕ) : List Bool := List.ofFn (fun i : Fin n => ω i)

private noncomputable def cut (p : Bool → ℝ) (t : ℝ) : ℕ → List Bool → Finset (List Bool)
  | 0, w => {w}
  | n + 1, w => if wordMass p w ≤ t then {w} else
      cut p t n (w ++ [false]) ∪ cut p t n (w ++ [true])

private theorem cut_prefix (p : Bool → ℝ) (t : ℝ) (n : ℕ) (w u : List Bool)
    (hu : u ∈ cut p t n w) : w <+: u := by
  induction n generalizing w with
  | zero =>
    have he : u = w := by simpa [cut] using hu
    simpa [he]
  | succ n ih =>
    by_cases h : wordMass p w ≤ t
    · have he : u = w := by simpa [cut, h] using hu
      simpa [he]
    · rw [cut, ite_eq_right h, Finset.mem_union] at hu
      rcases hu with hu | hu
      · exact (List.prefix_append w [false]).trans (ih _ hu)
      · exact (List.prefix_append w [true]).trans (ih _ hu)

private theorem cut_length (p : Bool → ℝ) (t : ℝ) (n : ℕ) (w u : List Bool)
    (hu : u ∈ cut p t n w) : u.length ≤ w.length + n := by
  induction n generalizing w with
  | zero =>
    have he : u = w := by simpa [cut] using hu
    simp [he]
  | succ n ih =>
    by_cases h : wordMass p w ≤ t
    · have : u = w := by simpa [cut, h] using hu
      simp [this]
    · rw [cut, ite_eq_right h, Finset.mem_union] at hu
      rcases hu with hu | hu <;> have := ih _ hu <;> simp only [List.length_append,
        List.length_singleton] at this <;> omega

private theorem cut_cover (p : Bool → ℝ) (t : ℝ) (n : ℕ) (w v : List Bool)
    (hv : v.length = n) : ∃ u ∈ cut p t n w, u <+: w ++ v := by
  induction n generalizing w v with
  | zero =>
    have : v = [] := List.length_eq_zero_iff.mp hv
    exact ⟨w, by simp [cut], by simp [this]⟩
  | succ n ih =>
    by_cases h : wordMass p w ≤ t
    · exact ⟨w, by simp [cut, h], List.prefix_append _ _⟩
    · cases v with
      | nil => simp at hv
      | cons c v =>
        have hv' : v.length = n := by simpa using hv
        obtain ⟨u, hu, hup⟩ := ih (w ++ [c]) v hv'
        refine ⟨u, ?_, by simpa [List.append_assoc] using hup⟩
        cases c <;> simp [cut, h, hu]

private theorem cut_mass (p : Bool → ℝ) (hsum : p false + p true = 1)
    (t : ℝ) (n : ℕ) (w : List Bool) :
    ∑ u ∈ cut p t n w, wordMass p u = wordMass p w := by
  classical
  induction n generalizing w with
  | zero => simp [cut]
  | succ n ih =>
    by_cases h : wordMass p w ≤ t
    · simp [cut, h]
    · have hd : Disjoint (cut p t n (w ++ [false])) (cut p t n (w ++ [true])) := by
        apply Finset.disjoint_left.mpr
        intro u hu hv
        have hf := cut_prefix p t n _ _ hu
        have ht := cut_prefix p t n _ _ hv
        have he := (List.prefix_of_prefix_length_le hf ht (by simp)).eq_of_length (by simp)
        simpa using he
      rw [cut, ite_eq_right h, Finset.sum_union hd, ih, ih]
      simp only [wordMass, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton]
      rw [← mul_add, hsum, mul_one]

private theorem cut_stops (p : Bool → ℝ) (a t : ℝ)
    (hp : ∀ c, 0 ≤ p c) (hpa : ∀ c, p c ≤ a) (ha : 0 ≤ a)
    (n : ℕ) (w : List Bool) (hw : 0 ≤ wordMass p w)
    (hbound : wordMass p w * a ^ n ≤ t) :
    ∀ u ∈ cut p t n w, wordMass p u ≤ t ∧
      (u = w ∨ t < wordMass p u.dropLast) := by
  induction n generalizing w with
  | zero =>
    intro u hu
    have he : u = w := by simpa [cut] using hu
    subst u
    exact ⟨by simpa using hbound, Or.inl rfl⟩
  | succ n ih =>
    intro u hu
    by_cases h : wordMass p w ≤ t
    · have he : u = w := by simpa [cut, h] using hu
      subst u
      exact ⟨h, Or.inl rfl⟩
    · rw [cut, ite_eq_right h, Finset.mem_union] at hu
      have step (c : Bool) (hc : u ∈ cut p t n (w ++ [c])) :
          wordMass p u ≤ t ∧ (u = w ∨ t < wordMass p u.dropLast) := by
        have hm : wordMass p (w ++ [c]) = wordMass p w * p c := by
          simp [wordMass]
        have hb : wordMass p (w ++ [c]) * a ^ n ≤ t := by
          rw [hm]
          calc
            wordMass p w * p c * a ^ n ≤ wordMass p w * a * a ^ n :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpa c) hw)
                (pow_nonneg ha n)
            _ = wordMass p w * a ^ (n + 1) := by ring
            _ ≤ t := hbound
        obtain ⟨hstop, he | he⟩ := ih _ (by rw [hm]; exact mul_nonneg hw (hp c)) hb u hc
        · exact ⟨hstop, Or.inr (by simpa [he] using lt_of_not_ge h)⟩
        · exact ⟨hstop, Or.inr he⟩
      exact hu.elim (step false) (step true)

/-- The first crossing has a uniform finite depth, partitions every binary ray,
conserves the actual product masses, and has reciprocal threshold size bounds. -/
theorem biased_first_mass_frontier (a b t : ℝ) (hb : 0 < b) (hba : b ≤ a)
    (ha : a < 1) (hab : a + b = 1) (ht : 0 < t) (htone : t < 1) :
    ∃ (N : ℕ) (A : Finset (List Bool)),
      (A : Set (List Bool)) = Crossing a b t ∧
      (∀ w ∈ A, w.length ≤ N) ∧
      IsPrefixFree (A : Set (List Bool)) ∧
      (∀ ω : ℕ → Bool, ∃! w, w ∈ A ∧ w = rayPrefix ω w.length) ∧
      (∑ w ∈ A, wordMass (letterMass a b) w) = 1 ∧
      (∀ w ∈ A, b * t < wordMass (letterMass a b) w ∧
        wordMass (letterMass a b) w ≤ t) ∧
      1 / t ≤ (A.card : ℝ) ∧ (A.card : ℝ) < 1 / (b * t) := by
  classical
  let p := letterMass a b
  have ha0 : 0 < a := hb.trans_le hba
  have hp : ∀ c, 0 < p c := by intro c; cases c <;> simp [p, letterMass, *]
  have hpa : ∀ c, p c ≤ a := by intro c; cases c <;> simp [p, letterMass, hba]
  have hpb : ∀ c, b ≤ p c := by intro c; cases c <;> simp [p, letterMass, hba]
  have pos (w : List Bool) : 0 < wordMass p w := by
    apply List.prod_pos
    simpa only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      using fun c (_ : c ∈ w) => hp c
  have bound (w : List Bool) : wordMass p w ≤ a ^ w.length := by
    induction w with
    | nil => simp [wordMass]
    | cons c w ih =>
      simp only [wordMass, List.map_cons, List.prod_cons, List.length_cons, pow_succ]
      exact (mul_le_mul_of_nonneg_left ih (hp c).le).trans
        (by nlinarith [pow_nonneg ha0.le w.length, hpa c])
  have mono {u v : List Bool} (h : u <+: v) : wordMass p v ≤ wordMass p u := by
    obtain ⟨r, rfl⟩ := h
    have hr : wordMass p r ≤ 1 := (bound r).trans (pow_le_one₀ ha0.le ha.le)
    simpa [wordMass, List.map_append, List.prod_append] using
      mul_le_of_le_one_right (pos u).le hr
  have pf : IsPrefixFree (Crossing a b t) := by
    intro u hu v hv huv
    by_contra he
    have hlen : u.length < v.length := lt_of_le_of_ne huv.length_le
      (fun hh => he (huv.eq_of_length hh))
    have hup : u <+: v.dropLast :=
      List.prefix_of_prefix_length_le huv v.dropLast_prefix (by simp; omega)
    exact (not_le_of_gt hv.2.2) ((mono hup).trans hu.2.1)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one ht ha
  let A := cut p t N []
  have stop : ∀ w ∈ A, wordMass p w ≤ t ∧ t < wordMass p w.dropLast := by
    intro w hw
    obtain ⟨hle, he | he⟩ := cut_stops p a t (fun c => (hp c).le) hpa ha0.le N []
      (by simp [wordMass]) (by simpa [wordMass] using hN.le) w hw
    · have : (1 : ℝ) ≤ t := by simpa [he, wordMass] using hle
      exact (not_le_of_gt htone this).elim
    · exact ⟨hle, he⟩
  have sub : ∀ w ∈ A, w ∈ Crossing a b t := by
    intro w hw
    exact ⟨by intro he; have := (stop w hw).1; simp [he, wordMass] at this; linarith,
      stop w hw⟩
  have cover : ∀ v : List Bool, v.length = N → ∃ w ∈ A, w <+: v := by
    intro v hv
    simpa [A] using cut_cover p t N [] v hv
  have alen : ∀ w ∈ A, w.length ≤ N := by
    intro w hw
    simpa using cut_length p t N [] w hw
  have eqA : (A : Set (List Bool)) = Crossing a b t := by
    apply Set.Subset.antisymm (by exact sub)
    intro v hv
    have vlen : v.length ≤ N := by
      by_contra hn
      have hpow : a ^ v.dropLast.length ≤ a ^ N :=
        pow_le_pow_of_le_one ha0.le ha.le (by simp; omega)
      exact (not_le_of_gt hv.2.2) (((bound _).trans hpow).trans hN.le)
    obtain ⟨w, hw, hwp⟩ := cover (v ++ List.replicate (N - v.length) false) (by simp; omega)
    rcases List.prefix_or_prefix_of_prefix hwp (List.prefix_append v _) with h | h
    · exact (pf (sub w hw) hv h) ▸ hw
    · exact (pf hv (sub w hw) h).symm ▸ hw
  have rays : ∀ ω : ℕ → Bool, ∃! w, w ∈ A ∧ w = rayPrefix ω w.length := by
    intro ω
    have pre (i j : ℕ) (hij : i ≤ j) : rayPrefix ω i <+: rayPrefix ω j := by
      apply List.prefix_iff_getElem?.mpr
      intro k hk
      have hki : k < i := by simpa [rayPrefix] using hk
      simp [rayPrefix, hki, lt_of_lt_of_le hki hij]
    obtain ⟨w, hw, hwp⟩ := cover (rayPrefix ω N) (by simp [rayPrefix])
    have he : w = rayPrefix ω w.length :=
      (List.prefix_of_prefix_length_le hwp (pre _ _ (alen w hw)) (by simp [rayPrefix])).eq_of_length
        (by simp [rayPrefix])
    refine ⟨w, ⟨hw, he⟩, ?_⟩
    rintro v ⟨hv, hve⟩
    rcases le_total v.length w.length with h | h
    · exact pf (sub v hv) (sub w hw) (by rw [hve, he]; exact pre _ _ h)
    · exact (pf (sub w hw) (sub v hv) (by rw [hve, he]; exact pre _ _ h)).symm
  have total : (∑ w ∈ A, wordMass p w) = 1 := by
    simpa [A, wordMass] using cut_mass p (by simpa [p, letterMass] using hab) t N []
  have lower : ∀ w ∈ A, b * t < wordMass p w := by
    intro w hw
    let v := w.dropLast
    let c := w.getLast (sub w hw).1
    have he : w = v ++ [c] := (List.dropLast_concat_getLast (sub w hw).1).symm
    have parent : w.dropLast = v := by simp [he]
    have hm : wordMass p w = wordMass p v * p c := by simp [he, wordMass]
    rw [hm]
    calc
      b * t < b * wordMass p v := mul_lt_mul_of_pos_left (by simpa [parent] using (stop w hw).2) hb
      _ ≤ wordMass p v * p c := by nlinarith [pos v, hpb c]
  have nonempty : A.Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at total
  have hupper : (1 : ℝ) ≤ A.card * t := by
    calc
      1 = ∑ w ∈ A, wordMass p w := total.symm
      _ ≤ ∑ _w ∈ A, t := Finset.sum_le_sum (fun w hw => (stop w hw).1)
      _ = A.card * t := by simp
  have hlower : (A.card : ℝ) * (b * t) < 1 := by
    calc
      (A.card : ℝ) * (b * t) = ∑ _w ∈ A, b * t := by simp
      _ < ∑ w ∈ A, wordMass p w := Finset.sum_lt_sum_of_nonempty nonempty lower
      _ = 1 := total
  refine ⟨N, A, eqA, alen, ?_, rays, total, ?_, (div_le_iff₀ ht).mpr hupper, ?_⟩
  · simpa [eqA] using pf
  · exact fun w hw => ⟨lower w hw, (stop w hw).1⟩
  · exact (lt_div_iff₀ (mul_pos hb ht)).mpr hlower

#print axioms biased_first_mass_frontier

end D5.S0.Computability.Coding.BiasedMassFrontier
