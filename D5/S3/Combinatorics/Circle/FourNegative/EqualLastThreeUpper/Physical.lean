/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Physical
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Physical
   mirror-E: none(waiver:consumed-physical-realization)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact interval masses, packet bounds and faithful physical realization. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical
/-! Physical interval and prefix bounds for the stated family. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper
open SourceWidth PeriodicShortening RunFirstEarTransport
open private rank amplitude delta heads newHeads successor newSuccessor start length f g N source source_numeric totals
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Source
open private Checks from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Arithmetic
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private range_positive inserted_perm
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private packetChecks strip_iff_packetChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private chain_signs chainLength chainStart base oldValue newValue sourceMod
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

private theorem block_data (a s : ℕ) (hs : 2 ≤ s) (ha : s ≤ a)
    (r : Fin 4) (lo len : ℕ) (hl : lo + len ≤ length a s r - 1) :
    let F := heads ((2:ℤ) ^ a) (2 ^ s) r
    let G := newHeads ((2:ℤ) ^ a) (2 ^ s) r
    let b := List.range' (start s r + lo) len
    (b.map (f a s)).sum = (2 ^ len - 1) * 2 ^ lo * F ∧
    (b.map (g a s)).sum = (2 ^ len - 1) * 2 ^ lo * G ∧
    (∀ i ∈ b, 0 ≤ f a s i) ∧ (∀ i ∈ b, 0 ≤ g a s i) := by
  dsimp only
  have tab := source a s hs ha
  have hf (i : ℕ) (hi : i < len) :
      f a s (start s r + lo + i) = (2:ℤ) ^ i * (2 ^ lo * heads ((2:ℤ) ^ a) (2 ^ s) r) := by
    rw [show start s r + lo + i = start s r + (lo + i) by omega, 
      (tab.2.2.1 r (lo + i) (by omega)).1, pow_add]
    ring
  have hg (i : ℕ) (hi : i < len) :
      g a s (start s r + lo + i) = (2:ℤ) ^ i * (2 ^ lo * newHeads ((2:ℤ) ^ a) (2 ^ s) r) := by
    rw [show start s r + lo + i = start s r + (lo + i) by omega, 
      (tab.2.2.1 r (lo + i) (by omega)).2, pow_add]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ladder_sum _ _ _ _ hf]; ring
  · rw [ladder_sum _ _ _ _ hg]; ring
  · exact range_positive _ _ _ _ (mul_nonneg (by positivity) (tab.1 r).le) hf
  · exact range_positive _ _ _ _ (mul_nonneg (by positivity) (tab.2.1 r).le) hg

private theorem terminal_signs (a s : ℕ) (hs : 2 ≤ s) (ha : s ≤ a) (r : Fin 4) :
    f a s (start s r + length a s r - 1) ≤ 0 ∧
    g a s (start s r + length a s r - 1) ≤ 0 := by
  have hr : 1 ≤ length a s r := by fin_cases r <;> simp [length] <;> omega
  have el : chainLength a s s s r = length a s r := by fin_cases r <;> rfl
  have es : chainStart s s s r = start s r := by
    fin_cases r <;> simp [chainStart, start] <;> omega
  have ht := chain_signs a s s s (by omega) hs hs hs r (length a s r - 1) (by rw [el]; omega)
  rw [el, ite_eq_right (by omega), es] at ht
  simpa only [f, g, show start s r + (length a s r - 1) = start s r + length a s r - 1 by omega] using
    And.intro ht.1.le ht.2.le

private theorem checks_strip (v : ℕ→ℤ) (C : ℤ) (bs : List (List ℕ×ℕ))
    (hC : 0 ≤ C) (hp : ∀ b ∈ bs, ∀ i ∈ b.1, 0 ≤ v i)
    (hn : ∀ b ∈ bs, v b.2 ≤ 0)
    (hc : Checks (2 * C) 0 (bs.map (fun b => (2 * (b.1.map v).sum, 2 * v b.2)))) :
    InStrip v C 0 (blocksWord bs) := by
  apply (strip_iff_packetChecks v C 0 bs ⟨le_rfl, hC⟩ hp hn).mpr
  have convert_checks (l : List (List ℕ×ℕ)) (h : ℤ) :
      Checks (2 * C) (2 * h) (l.map (fun b => (2 * (b.1.map v).sum, 2 * v b.2))) →
        packetChecks v C h l := by
    induction l generalizing h with
    | nil => simp [packetChecks]
    | cons b bs ih =>
      simp only [List.map_cons, Checks, packetChecks]
      rintro ⟨hs, hp, hrest⟩
      refine ⟨by omega, by omega, ih _ ?_⟩
      convert hrest using 1 <;> ring
  exact convert_checks bs 0 hc

private theorem range_end (off len : ℕ) :
    List.range' off len ++ [off + len] = List.range' off (len + 1) := by
  simpa using (List.range'_append_1 (s:=off) (m:=len) (n:=1))

private theorem range_join (off m n : ℕ) :
    List.range' off m ++ List.range' (off + m) n = List.range' off (m + n) :=
  List.range'_append_1

private theorem finish (a s : ℕ) (hs : 2 ≤ s) (ha : s ≤ a) (cut : ℕ)
    (P T : List ℕ) (hc : P.length = cut)
    (hp : (P++T).Perm (List.range (rank a s)))
    (hold : InStrip (f a s) (N a s/2) 0 (P++T))
    (hnew : InStrip (g a s) (N a s) 0 (P++rank a s::T)) :
    ∃ sigma : List (Fin (rank a s)), sigma.map Fin.val = P++T ∧ cut ≤ rank a s ∧
      OriginalOrder (rank a s) (amplitude a s) sigma ∧
      OriginalOrder (rank a s + 1) (2 * amplitude a s) (earWord (rank a s) sigma cut) := by
  have hk : 0 < rank a s := by dsimp [rank]; omega
  obtain ⟨_, hmod, hmodn, hamp⟩ := source_numeric a s
  have hb : base a s s s 0 = (amplitude a s:ℤ) := by
    rw [hamp]; dsimp [base, heads, delta]; ring
  have hf : f a s = fun i => centered (modulus (rank a s)) ((2:ℤ) ^ i * amplitude a s) := by
    funext i; dsimp [f, oldValue]; rw [hmod, hb]; rfl
  have hg : g a s = fun i => centered (modulus (rank a s + 1)) ((2:ℤ) ^ i * (2 * amplitude a s)) := by
    funext i; dsimp [g, newValue]; rw [hmodn, hb]; rfl
  have hz := totals a s hs ha
  have hzero : ((List.range (rank a s + 1)).map (g a s)).sum = 0 := by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, 
      hz.2, (source a s hs ha).2.2.2.2]
    ring
  refine ⟨(P++T).map (label (rank a s) hk), ?_, ?_, ?_, ?_⟩
  · rw [List.map_map]
    calc
      (P++T).map (fun i => (label (rank a s) hk i).val) = (P++T).map id := by
        apply List.map_congr_left
        intro i hi
        have hi' : i < rank a s := List.mem_range.mp (hp.mem_iff.mp hi)
        exact Nat.mod_eq_of_lt hi'
      _ = P++T := List.map_id _
  · have hl := hp.length_eq
    simp only [List.length_append, List.length_range, hc] at hl
    omega
  · apply lift_order _ _ hk _ hp
    · simpa only [hf, hmod] using hold
    · simpa only [hf] using hz.1
  · rw [marked_word (rank a s) cut hk P T hc hp]
    apply lift_order _ _ (by omega) _ (inserted_perm _ _ _ hp)
    · have hh : modulus (rank a s + 1)/2 = N a s := by rw [hmodn]; omega
      simpa only [hg, hh, Nat.cast_mul, Nat.cast_ofNat] using hnew
    · simpa only [hg, Nat.cast_mul, Nat.cast_ofNat] using hzero

end D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper
