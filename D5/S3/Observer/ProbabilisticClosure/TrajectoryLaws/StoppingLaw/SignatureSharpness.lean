/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureSharpness
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SignatureSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Whole signatures force an exponential-radius potential path despite a radius-zero law representative. -/


import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SignatureCompression

/-! All potential nodes of the complete tree form the sharp detached slot path.
The constant paid execution admits a different representative using repeated target reads. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Classical MeasureTheory

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

universe u

/-- Preorder enumeration gives each potential node its own consecutive edge. -/
def completePathTree (φ : Bool) : ℕ → ℤ → ReadTree
  | 0, _ => .leaf (some (.a false))
  | k + 1, L => .read (2 * L + φ.toInt)
      (completePathTree φ k (L + 1)) (completePathTree φ k (L + (2 ^ k : ℕ)))

/-- Each repeated call is paid even though all replies are ignored. -/
def repeatTargetTree (j : Bool) : ℕ → ReadTree
  | 0 => .leaf (some (.a false))
  | k + 1 => .read j.toInt (repeatTargetTree j k) (repeatTargetTree j k)

private theorem complete_height (φ : Bool) (k : ℕ) (L : ℤ) :
    (completePathTree φ k L).height = k := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih => simp only [completePathTree, ReadTree.height, ih, max_self]

private theorem complete_count (φ : Bool) (k : ℕ) (L : ℤ) :
    (completePathTree φ k L).potentialReadCount = 2 ^ k - 1 := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have hpos : 0 < 2 ^ k := pow_pos (by decide) _
    simp only [completePathTree, ReadTree.potentialReadCount, ih, pow_succ]
    omega

private theorem complete_run (φ : Bool) (k : ℕ) (L : ℤ) (x : ℤ → Bool) :
    ((completePathTree φ k L).run x).output = some (.a false) ∧
      ((completePathTree φ k L).run x).paid = k := by
  have out (a : ℤ) (b : Bool) (v : Execution) : (v.prepend a b).output = v.output := rfl
  induction k generalizing L with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    simp only [completePathTree, ReadTree.run]
    split <;> simp only [out, Execution.paid_prepend, (ih _).1, (ih _).2, and_self]

private theorem repeat_run (j : Bool) (k : ℕ) (x : ℤ → Bool) :
    ((repeatTargetTree j k).run x).output = some (.a false) ∧
      ((repeatTargetTree j k).run x).paid = k := by
  have out (a : ℤ) (b : Bool) (v : Execution) : (v.prepend a b).output = v.output := rfl
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    simp only [repeatTargetTree, ReadTree.run]
    split <;> simp only [out, Execution.paid_prepend, ih.1, ih.2, and_self]

private theorem repeat_height (j : Bool) (k : ℕ) : (repeatTargetTree j k).height = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [repeatTargetTree, ReadTree.height, ih, max_self]

private theorem repeat_addresses (j : Bool) (k : ℕ) :
    ∀ t ∈ (repeatTargetTree j k).addresses, t = j.toInt := by
  induction k with
  | zero => simp [repeatTargetTree, ReadTree.addresses]
  | succ k ih =>
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · rfl
    · rcases Finset.mem_union.mp ht with ht | ht <;> exact ih t ht

private theorem complete_occurrence (φ : Bool) (k : ℕ) (L : ℤ) (i : ℕ)
    (hi : i < 2 ^ k - 1) :
    ∃ p : ReadPosition, (completePathTree φ k L).addressAt p =
      some (2 * (L + (i : ℤ)) + φ.toInt) := by
  induction k generalizing L i with
  | zero => simp at hi
  | succ k ih =>
    have hpos : 0 < 2 ^ k := pow_pos (by decide) _
    rw [pow_succ] at hi
    by_cases hzero : i = 0
    · subst i
      exact ⟨[], by simp only [completePathTree, ReadTree.addressAt, Nat.cast_zero, add_zero]⟩
    · by_cases hleft : i < 2 ^ k
      · obtain ⟨p, hp⟩ := ih (L + 1) (i - 1) (by omega)
        refine ⟨false :: p, ?_⟩
        simp only [completePathTree, ReadTree.addressAt, hp]
        congr 1
        omega
      · obtain ⟨p, hp⟩ := ih (L + (2 ^ k : ℕ)) (i - 2 ^ k) (by omega)
        refine ⟨true :: p, ?_⟩
        simp only [completePathTree, ReadTree.addressAt, hp]
        congr 1
        omega

private theorem paired_address (T T' : ReadTree) (h : T.paritySkeleton = T'.paritySkeleton)
    (p : ReadPosition) (t : ℤ) (ht : T.addressAt p = some t) :
    ∃ t' : ℤ, T'.addressAt p = some t' ∧ t' % 2 = t % 2 := by
  have he := congrArg (fun U : ReadTree => U.addressAt p) h
  rw [ReadTree.addressAt_skeleton, ReadTree.addressAt_skeleton, ht] at he
  cases ht' : T'.addressAt p with
  | none => simp only [ht', Option.map_none, Option.map_some] at he; cases he
  | some t' =>
    refine ⟨t', rfl, ?_⟩
    simp only [ht', Option.map_some] at he
    exact (Option.some.inj he).symm

private theorem complete_signature_remote (j : Bool) (k : ℕ) (hk : 1 ≤ k)
    (T' : ReadTree) (hsig : SameSignature j (completePathTree (!j) k (j.toInt + 1)) T') :
    ∃ t ∈ T'.addresses, (2 * (2 ^ k - 1 : ℕ) + 1 : ℤ) ≤ |t - j.toInt| := by
  let M := 2 ^ k - 1
  have hpw : 2 ≤ 2 ^ k := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hk
  have hM : 1 ≤ M := by dsimp only [M]; omega
  let W := completePathTree (!j) k (j.toInt + 1)
  have occurrences (i : Fin M) : ∃ p : ReadPosition,
      W.addressAt p = some (2 * (j.toInt + 1 + (i.val : ℤ)) + (!j).toInt) :=
    complete_occurrence (!j) k (j.toInt + 1) i.val i.isLt
  choose p hp using occurrences
  have paired (i : Fin M) : ∃ t : ℤ, T'.addressAt (p i) = some t ∧
      t % 2 = (2 * (j.toInt + 1 + (i.val : ℤ)) + (!j).toInt) % 2 :=
    paired_address W T' hsig.1 (p i) _ (hp i)
  choose t ht hpar using paired
  let b : Fin M → ℤ := fun i => (t i - (!j).toInt) / 2
  have active (i : Fin M) : (t i - (!j).toInt) % 2 = 0 := by
    have := hpar i
    cases j <;> simp only [Bool.not_false, Bool.not_true, Bool.toInt_false,
      Bool.toInt_true] at * <;> omega
  have address (i : Fin M) : t i = 2 * b i + (!j).toInt := by
    have := active i
    dsimp only [b]
    omega
  have old_minus (i : Fin M) :
      signatureSlotIndex j (!j) W (some (p i, false)) = j.toInt + 1 + i.val := by
    rw [signatureSlotIndex, hp]
    have h₁ : (2 * (j.toInt + 1 + (i.val : ℤ)) + (!j).toInt - (!j).toInt) % 2 = 0 := by omega
    have h₂ : (2 * (j.toInt + 1 + (i.val : ℤ)) + (!j).toInt - (!j).toInt) / 2 =
        j.toInt + 1 + i.val := by omega
    simp only [ite_eq_left h₁, h₂, Bool.toInt_false, add_zero]
  have old_plus (i : Fin M) :
      signatureSlotIndex j (!j) W (some (p i, true)) = j.toInt + 1 + i.val + 1 := by
    rw [signatureSlotIndex, hp]
    have h₁ : (2 * (j.toInt + 1 + (i.val : ℤ)) + (!j).toInt - (!j).toInt) % 2 = 0 := by omega
    have h₂ : (2 * (j.toInt + 1 + (i.val : ℤ)) + (!j).toInt - (!j).toInt) / 2 =
        j.toInt + 1 + i.val := by omega
    simp only [ite_eq_left h₁, h₂, Bool.toInt_true]
  have new_minus (i : Fin M) : signatureSlotIndex j (!j) T' (some (p i, false)) = b i := by
    simp only [signatureSlotIndex, ht, ite_eq_left (active i), Bool.toInt_false, add_zero, b]
  have new_plus (i : Fin M) : signatureSlotIndex j (!j) T' (some (p i, true)) = b i + 1 := by
    simp only [signatureSlotIndex, ht, ite_eq_left (active i), Bool.toInt_true, b]
  have chain (i : ℕ) (hi : i + 1 < M) :
      b ⟨i + 1, hi⟩ = b ⟨i, by omega⟩ + 1 := by
    have he := (hsig.2 (!j) (some (p ⟨i, by omega⟩, true))
      (some (p ⟨i + 1, hi⟩, false))).mp (by rw [old_plus, old_minus]; push_cast; omega)
    rw [new_plus, new_minus] at he
    exact he.symm
  let b₀ := b ⟨0, by omega⟩
  have sequence : ∀ (i : ℕ) (hi : i < M), b ⟨i, hi⟩ = b₀ + (i : ℤ) := by
    intro i
    induction i with
    | zero => intro _; simp only [b₀, Nat.cast_zero, add_zero]
    | succ i ih =>
      intro hi
      rw [chain i hi, ih (by omega), Nat.cast_add, Nat.cast_one]
      omega
  have target : targetIndex j (!j) = j.toInt := by cases j <;> simp [targetIndex]
  have no_minus (i : Fin M) : j.toInt ≠ b i := by
    intro he
    have h := (hsig.2 (!j) none (some (p i, false))).mpr
      (by rw [new_minus]; exact target.trans he)
    rw [show signatureSlotIndex j (!j) W none = j.toInt by exact target, old_minus] at h
    omega
  have no_plus (i : Fin M) : j.toInt ≠ b i + 1 := by
    intro he
    have h := (hsig.2 (!j) none (some (p i, true))).mpr
      (by rw [new_plus]; exact target.trans he)
    rw [show signatureSlotIndex j (!j) W none = j.toInt by exact target, old_plus] at h
    omega
  have detached : j.toInt ∉ pathVertices b₀ M := by
    intro hq
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hq
    let i := (j.toInt - b₀).toNat
    have hi : (i : ℤ) = j.toInt - b₀ := Int.toNat_of_nonneg (by omega)
    by_cases hil : i < M
    · have hn := no_minus ⟨i, hil⟩
      have hs := sequence i hil
      omega
    · have him : i = M := by omega
      have hn := no_plus ⟨M - 1, by omega⟩
      have hs := sequence (M - 1) (by omega)
      omega
  obtain ⟨e, he, hremote⟩ := detached_path_remote j hM b₀ detached
  obtain ⟨helo, hehi⟩ := Finset.mem_Icc.mp he
  let i := (e - b₀).toNat
  have hi : (i : ℤ) = e - b₀ := Int.toNat_of_nonneg (by omega)
  have him : i < M := by omega
  have hseq := sequence i him
  have haddr := address ⟨i, him⟩
  refine ⟨t ⟨i, him⟩, T'.addressAt_in_addresses (p ⟨i, him⟩) _ (ht _), ?_⟩
  have heq : t ⟨i, him⟩ = 2 * e + (!j).toInt := by omega
  simpa only [heq] using hremote

/-- A uniform radius represents every tree while preserving its full signature. -/
def SignatureRadius (j : Bool) (k R : ℕ) : Prop :=
  ∀ T : ReadTree, T.height ≤ k → ∃ T' : ReadTree,
    SameSignature j T T' ∧ T'.height ≤ k ∧
      ∀ t ∈ T'.addresses, |t - j.toInt| ≤ (R : ℤ)

private theorem signature_upper (j : Bool) (k : ℕ) :
    SignatureRadius j k (2 ^ (k + 1) - 1) := by
  intro T hT
  obtain ⟨hsig, hh, hb⟩ := bounded_signature_relabeling j T k hT
  refine ⟨compressedTree j T, hsig, by omega, ?_⟩
  intro t ht
  have hbound := hb t ht
  have hpow : 0 < 2 ^ k := pow_pos (by decide) _
  have heq : 2 * (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by rw [pow_succ]; omega
  rw [← heq]
  push_cast
  exact abs_le.mpr ⟨by omega, by omega⟩

private theorem signature_radius_exists (j : Bool) (k : ℕ) :
    ∃ R : ℕ, SignatureRadius j k R := ⟨_, signature_upper j k⟩

/-- The sufficient-radius set is nonempty before its least natural number is taken. -/
def signatureRadius (j : Bool) (k : ℕ) : ℕ := Nat.find (signature_radius_exists j k)

/-- The exact signature radius has a complete-tree witness whose full unchanged-seed
law also has a lawful representative reading only the target, with all k calls paid. -/
theorem exact_signature_radius_with_law_zero_witness (j : Bool) (k : ℕ) (hk : 1 ≤ k) :
    signatureRadius j k = 2 ^ (k + 1) - 1 ∧
    let W := completePathTree (!j) k (j.toInt + 1)
    W.height = k ∧ W.potentialReadCount = 2 ^ k - 1 ∧
    (∀ T' : ReadTree, SameSignature j W T' →
      ∃ t ∈ T'.addresses, ((2 ^ (k + 1) - 1 : ℕ) : ℤ) ≤ |t - j.toInt|) ∧
    (repeatTargetTree j k).height = k ∧
    (∀ t ∈ (repeatTargetTree j k).addresses, t = j.toInt) ∧
    (∀ (U : Type u) [MeasurableSpace U] (ν : Measure U) (β : Bias),
      let R := RawRule.realize (fun _ : U => repeatTargetTree j k)
      R.Lawful ∧ R.TotalCap k ∧ R.WithinActualRadius j 0 ∧
        R.fullLaw β j ν =
          (RawRule.realize (fun _ : U => W)).fullLaw β j ν) := by
  have hpow : 0 < 2 ^ k := pow_pos (by decide) _
  have heq : 2 * (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by rw [pow_succ]; omega
  have remote (T' : ReadTree)
      (h : SameSignature j (completePathTree (!j) k (j.toInt + 1)) T') :
      ∃ t ∈ T'.addresses, ((2 ^ (k + 1) - 1 : ℕ) : ℤ) ≤ |t - j.toInt| := by
    obtain ⟨t, ht, hb⟩ := complete_signature_remote j k hk T' h
    refine ⟨t, ht, ?_⟩
    rw [← heq]
    exact_mod_cast hb
  have lower (R : ℕ) (hR : SignatureRadius j k R) : 2 ^ (k + 1) - 1 ≤ R := by
    obtain ⟨T', hsig, _, hb⟩ := hR (completePathTree (!j) k (j.toInt + 1))
      (by rw [complete_height])
    obtain ⟨t, ht, hr⟩ := remote T' hsig
    have hu := hb t ht
    omega
  have minimum : signatureRadius j k = 2 ^ (k + 1) - 1 := by
    apply Nat.le_antisymm
    · exact Nat.find_min' (signature_radius_exists j k) (signature_upper j k)
    · exact lower _ (Nat.find_spec (signature_radius_exists j k))
  refine ⟨minimum, complete_height _ _ _, complete_count _ _ _, remote,
    repeat_height j k, repeat_addresses j k, ?_⟩
  intro U _ ν β
  have hrheight (u : U) : (repeatTargetTree j k).height ≤ k := (repeat_height j k).le
  have hwheight (u : U) : (completePathTree (!j) k (j.toInt + 1)).height ≤ k :=
    (complete_height _ _ _).le
  refine ⟨RawRule.realize_lawful _ measurable_const, RawRule.realize_cap _ k hrheight, ?_, ?_⟩
  · apply normalized_actual_radius _ k (RawRule.realize_cap _ k hrheight) j
    intro u t ht
    rw [RawRule.normalize_realize _ k u (hrheight u)] at ht
    have he := repeat_addresses j k t ht
    simp only [he, sub_self, abs_zero, Nat.cast_zero, le_refl]
  · rw [RawRule.fullLaw_realize _ k hrheight, RawRule.fullLaw_realize _ k hwheight]
    congr 1
    funext p
    have hw := complete_run (!j) k (j.toInt + 1) (visible p.1.1 p.1.2)
    have hr := repeat_run j k (visible p.1.1 p.1.2)
    simp only [selectorJoint, observation, Execution.returned, hw.1, hw.2, hr.1, hr.2]

#print axioms exact_signature_radius_with_law_zero_witness

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
