/- GID: D5/S3/Combinatorics/Circle/AdjacentDepthThreeCycle
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/AdjacentDepthThreeCycle
   mirror-E: none(waiver:audit-open-22063)
   anchors: [D5/S3/Combinatorics/Circle/NativeSeedChains,
     D5/S3/Combinatorics/Circle/SourceWidth]
   utility: none
   digest: Native adjacent-depth long seeds carry a physical order-three cycle.
   The global mixed root-only sweep remains a later theorem. -/
module
public import D5.S3.Combinatorics.Circle.NativeSeedChains
public import Mathlib.Logic.Equiv.Defs

/-! # Native long-seed physical three-cycles

For a native chain the labels are physical occurrences in `Fin k`.  When its
first-hit length is one larger than the common lower depth, the lower seed,
its predecessor negative, and its predecessor root form the literal packet
`[root, negative, seed]`.  The packet is rotated to `[seed, root, negative]`.
The permutation below is written with its inverse rather than inferred from an
involution: this is the order-three map used by the adjacent-depth design.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle

open SourceWidth ExpandingSourcePath NativeSeedChains

def cycleForward {α : Type*} [DecidableEq α] (a b c : α) (x : α) : α :=
  if x = a then c else if x = b then a else if x = c then b else x

def cycleBackward {α : Type*} [DecidableEq α] (a b c : α) (x : α) : α :=
  if x = a then b else if x = b then c else if x = c then a else x

theorem cycleForward_backward {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : α) :
    cycleForward a b c (cycleBackward a b c x) = x := by
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  have hcb : c ≠ b := Ne.symm hbc
  by_cases hxa : x = a
  · subst x
    simp [cycleForward, cycleBackward, hab, hac, hbc, hba, hca, hcb]
  · by_cases hxb : x = b
    · subst x
      simp [cycleForward, cycleBackward, hab, hac, hbc, hba, hca, hcb]
    · by_cases hxc : x = c
      · subst x
        simp [cycleForward, cycleBackward, hab, hac, hbc, hba, hca, hcb]
      · simp [cycleForward, cycleBackward, hxa, hxb, hxc, hab, hac, hbc, hba, hca, hcb]

theorem cycleBackward_forward {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : α) :
    cycleBackward a b c (cycleForward a b c x) = x := by
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  have hcb : c ≠ b := Ne.symm hbc
  by_cases hxa : x = a
  · subst x
    simp [cycleForward, cycleBackward, hab, hac, hbc, hba, hca, hcb]
  · by_cases hxb : x = b
    · subst x
      simp [cycleForward, cycleBackward, hab, hac, hbc, hba, hca, hcb]
    · by_cases hxc : x = c
      · subst x
        simp [cycleForward, cycleBackward, hab, hac, hbc, hba, hca, hcb]
      · simp [cycleForward, cycleBackward, hxa, hxb, hxc, hab, hac, hbc, hba, hca, hcb]

/-- The physical three-cycle, with its actual inverse exposed in the API. -/
def physicalThreeCycle {α : Type*} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Equiv.Perm α :=
  { toFun := cycleForward a b c
    invFun := cycleBackward a b c
    left_inv := cycleBackward_forward hab hac hbc
    right_inv := cycleForward_backward hab hac hbc }

theorem physicalThreeCycle_apply_root {α : Type*} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    physicalThreeCycle a b c hab hac hbc a = c := by
  change cycleForward a b c a = c
  simp [cycleForward, hab, hac, Ne.symm hab, Ne.symm hac]

theorem physicalThreeCycle_apply_negative {α : Type*} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    physicalThreeCycle a b c hab hac hbc b = a := by
  change cycleForward a b c b = a
  simp [cycleForward, hab, hbc, Ne.symm hab, Ne.symm hbc]

theorem physicalThreeCycle_apply_seed {α : Type*} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    physicalThreeCycle a b c hab hac hbc c = b := by
  change cycleForward a b c c = b
  simp [cycleForward, hac, hbc, Ne.symm hac, Ne.symm hbc]

theorem physicalThreeCycle_inverse {α : Type*} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : α) :
    (physicalThreeCycle a b c hab hac hbc).symm x = cycleBackward a b c x := by
  apply Equiv.injective (physicalThreeCycle a b c hab hac hbc)
  simp only [Equiv.apply_symm_apply]
  exact (cycleForward_backward hab hac hbc x).symm

private theorem physicalThreeCycle_roles {α : Type*} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    physicalThreeCycle a b c hab hac hbc a = c ∧
      physicalThreeCycle a b c hab hac hbc b = a ∧
      physicalThreeCycle a b c hab hac hbc c = b ∧
      (physicalThreeCycle a b c hab hac hbc).symm a = b ∧
      (physicalThreeCycle a b c hab hac hbc).symm b = c ∧
      (physicalThreeCycle a b c hab hac hbc).symm c = a := by
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  have hcb : c ≠ b := Ne.symm hbc
  refine ⟨physicalThreeCycle_apply_root a b c hab hac hbc,
    physicalThreeCycle_apply_negative a b c hab hac hbc,
    physicalThreeCycle_apply_seed a b c hab hac hbc, ?_, ?_, ?_⟩
  · rw [physicalThreeCycle_inverse a b c hab hac hbc]
    simp [cycleBackward, hab, hac, hbc, hba, hca, hcb]
  · rw [physicalThreeCycle_inverse a b c hab hac hbc]
    simp [cycleBackward, hab, hac, hbc, hba, hca, hcb]
  · rw [physicalThreeCycle_inverse a b c hab hac hbc]
    simp [cycleBackward, hab, hac, hbc, hba, hca, hcb]

/-! Physical offsets are manipulated modulo `k`; these two identities are used
to move between a seed and its two preceding physical labels. -/

def successor {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k := phase hk i 1

def predecessor {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k := phase hk i (k - 1)

private theorem successor_predecessor {k : ℕ} (hk : 0 < k) (i : Fin k) :
    successor hk (predecessor hk i) = i := by
  apply Fin.ext
  dsimp [successor, predecessor, phase]
  by_cases hi : i.val = 0
  · rw [hi]
    simp only [Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega : k - 1 < k),
      Nat.sub_add_cancel (by omega : 1 ≤ k)]
    simp
  · have hi' : 1 ≤ i.val := by omega
    have hsplit : i.val + (k - 1) = (i.val - 1) + k := by omega
    rw [hsplit, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i.val - 1 < k)]
    rw [Nat.sub_add_cancel hi']
    exact Nat.mod_eq_of_lt i.isLt

private theorem predecessor_successor {k : ℕ} (hk : 0 < k) (i : Fin k) :
    predecessor hk (successor hk i) = i := by
  apply Fin.ext
  dsimp [successor, predecessor, phase]
  by_cases hi : i.val + 1 < k
  · rw [Nat.mod_eq_of_lt hi]
    have hsplit : i.val + 1 + (k - 1) = i.val + k := by omega
    rw [hsplit, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  · have he : i.val + 1 = k := by omega
    have hi_eq : i.val = k - 1 := by omega
    rw [he]
    simp [hi_eq, Nat.mod_eq_of_lt hk]

private theorem phase_succ {k : ℕ} (hk : 0 < k) (i : Fin k) (m : ℕ) :
    phase hk i (m + 1) = successor hk (phase hk i m) := by
  apply Fin.ext
  change (i.val + (m + 1)) % k = ((i.val + m) % k + 1) % k
  rw [Nat.add_mod, Nat.add_mod]
  rw [Nat.add_mod m 1 k, Nat.add_mod i.val m k]
  simp [Nat.add_assoc, Nat.mod_mod]

private theorem native_positive_bound {k t : ℕ} (hk : 3 ≤ k)
    (hsmall : ∀ i : Fin k, |actualSource k t i| < quarter k →
      0 < actualSource k t i) :
    ∀ i : Fin k, 0 < actualSource k t i →
      3 * actualSource k t i ≤ modulus k := by
  classical
  obtain ⟨hQ, hN, hC, hNpos, hodd⟩ := source_geometry hk
  let w := actualSource k t
  let σ := fun i : Fin k => phase (by omega : 0 < k) i 1
  have hb (i : Fin k) : -(2 * quarter k - 1) ≤ w i ∧
      w i ≤ 2 * quarter k - 1 := by
    have h := centered_bounds hNpos hodd ((2 : ℤ) ^ i.val * (t : ℤ))
    change -half k ≤ w i ∧ w i ≤ half k at h
    rwa [hC] at h
  have hs (i : Fin k) : w (σ i) = doubleStep (modulus k) (w i) := by
    simpa [w, σ] using phase_step hk t i 0
  have hnz (i : Fin k) : w i ≠ 0 := by
    intro h
    have hh := hsmall i (by change |w i| < quarter k; rw [h]; norm_num; omega)
    change 0 < w i at hh
    omega
  have neg (i : Fin k) (hi : w i < 0) :
      quarter k ≤ -w i ∧ w (σ i) = 2 * w i + modulus k ∧
      0 < w (σ i) := by
    have hl : quarter k ≤ -w i := by
      by_contra hh
      have hp := hsmall i (by change |w i| < quarter k; rw [abs_of_neg hi]; omega)
      change 0 < w i at hp
      omega
    have ht := hs i
    rw [doubleStep, ite_eq_right (by omega : ¬modulus k < 4 * w i),
      ite_eq_left (by omega : 4 * w i < -modulus k)] at ht
    have hbi := hb i
    exact ⟨hl, ht, by omega⟩
  have posStep (i : Fin k) (hi : quarter k ≤ w i) :
      w (σ i) = 2 * w i - modulus k ∧ w (σ i) < 0 ∧
      w (σ (σ i)) = 4 * w i - modulus k ∧ 0 < w (σ (σ i)) := by
    have ht := hs i
    rw [doubleStep, ite_eq_left (by omega : modulus k < 4 * w i)] at ht
    have hbi := hb i
    have hneg : w (σ i) < 0 := by omega
    obtain ⟨_, ht2, hp2⟩ := neg (σ i) hneg
    exact ⟨ht, hneg, by omega, hp2⟩
  have existsPos : ∃ i, 0 < w i := by
    let i : Fin k := ⟨0, by omega⟩
    by_cases hi : 0 < w i
    · exact ⟨i, hi⟩
    · exact ⟨σ i, (neg i (by have := hnz i; omega)).2.2⟩
  let P := Finset.univ.filter (fun i : Fin k => 0 < w i)
  have memP (i : Fin k) : i ∈ P ↔ 0 < w i := by simp [P]
  obtain ⟨i, hi⟩ := existsPos
  obtain ⟨a, ha, hmax⟩ := P.exists_max_image w ⟨i, (memP i).2 hi⟩
  have hapos := (memP a).1 ha
  have haLarge : quarter k ≤ w a := by
    by_contra hh
    have ht := hs a
    rw [doubleStep, ite_eq_right (by omega : ¬modulus k < 4 * w a),
      ite_eq_right (by omega : ¬4 * w a < -modulus k)] at ht
    have hm := hmax (σ a) ((memP _).2 (by omega))
    omega
  obtain ⟨_, _, ht, hp⟩ := posStep a haLarge
  have hm := hmax (σ (σ a)) ((memP _).2 hp)
  intro j hj
  have hmj := hmax j ((memP _).2 hj)
  change 3 * w j ≤ modulus k
  omega

private def longSeed {k : ℕ} (hk : 0 < k) (h : ℕ)
    (w : Fin k → ℤ) (j : Fin k) : Prop :=
  w (predecessor hk j) < 0 ∧ 0 < w j ∧
    (2 : ℤ) ^ h * w j < quarter k

private noncomputable instance longSeedDecidable {k : ℕ} (hk : 0 < k)
    (h : ℕ) (w : Fin k → ℤ) : DecidablePred (longSeed hk h w) :=
  fun _ => Classical.propDecidable _

/-! This is the source-derived first-hit datum used by the adjacent-depth
assumption.  The witness is a physical seed and its literal native dyadic
path; no quotient by numerical values is involved. -/
def nativeFirstHit {k t : ℕ}
    (hk : 0 < k) (n : Fin k) (r : ℕ) : Prop :=
  ∃ a : Fin k,
    r + 2 ≤ k ∧ 0 < actualSource k t a ∧
      (∀ q < r,
        0 < actualSource k t (phase hk a q) ∧
          actualSource k t (phase hk a q) < quarter k) ∧
      actualSource k t (phase hk a r) =
        (2 : ℤ) ^ r * actualSource k t a ∧
      quarter k ≤ actualSource k t (phase hk a r) ∧
      actualSource k t (phase hk a (r + 1)) < 0

private theorem long_seed_successor_small {k t h : ℕ} (hk : 3 ≤ k)
    (j : Fin k) (hj : longSeed (by omega) h (actualSource k t) j)
    (hh : 1 ≤ h) :
    0 < actualSource k t (successor (by omega) j) ∧
      actualSource k t (successor (by omega) j) < quarter k := by
  dsimp [longSeed] at hj
  have hQ := (source_geometry hk).1
  have hNform := (source_geometry hk).2.1
  have hpow : (2 : ℤ) ^ h ≥ 2 := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hh
    norm_num at hp ⊢
    omega
  have hstep := phase_step hk t j 0
  simp only [phase_zero, zero_add] at hstep
  change actualSource k t (successor (by omega) j) =
    doubleStep (modulus k) (actualSource k t j) at hstep
  have hbranch : 4 * actualSource k t j < modulus k := by
    nlinarith [hj.2.2, hpow]
  rw [doubleStep, ite_eq_right (by omega : ¬ modulus k < 4 * actualSource k t j),
    ite_eq_right (by omega : ¬ 4 * actualSource k t j < -modulus k)] at hstep
  constructor
  · rw [hstep]
    omega
  · rw [hstep]
    nlinarith [hj.2.2, hpow, hj.2.1]

theorem native_adjacent_depth_first_hit {k t h : ℕ} (hk : 3 ≤ k)
    (hsmall : ∀ i : Fin k, |actualSource k t i| < quarter k →
      0 < actualSource k t i)
    (hh : 1 ≤ h)
    (hadj : ∀ (n : Fin k) (r : ℕ), actualSource k t n < 0 →
      nativeFirstHit (k := k) (t := t) (by omega) n r → r = h ∨ r = h + 1)
    (n : Fin k) (hn : actualSource k t n < 0) :
    ∃ r : ℕ, (r = h ∨ r = h + 1) ∧
      nativeFirstHit (k := k) (t := t) (by omega) n r := by
  obtain ⟨r, hr, hnodup, ha, hamod, hpre, hdyadic, hroot,
      hrootQ, hrootupper, hneg, hneglt, hnext, hnextpos, hnextmod,
      hmass, hdebt, htransport⟩ := native_chain_extraction hk hsmall n hn
  let a := phase (by omega : 0 < k) n 1
  have hfirst : nativeFirstHit (k := k) (t := t) (by omega) n r := by
    refine ⟨a, hr, ha, ?_, ?_, ?_, ?_⟩
    · simpa [a] using hpre
    · simpa [a] using hroot
    · simpa [a] using hrootQ
    · simpa [a] using hneglt
  exact ⟨r, hadj n r hn hfirst, hfirst⟩

private theorem phase_offset_injective {k : ℕ} (hk : 0 < k) (a : Fin k)
    {i j : ℕ} (hi : i < k) (hj : j < k)
    (hij : phase hk a i = phase hk a j) : i = j := by
  have hm0 : Nat.ModEq k (a.val + i) (a.val + j) := by
    exact congrArg Fin.val hij
  have hc := Nat.ModEq.add_left_cancel' a.val hm0
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hc

private theorem native_distinct {k t : ℕ} (hk : 3 ≤ k)
    {root neg next : Fin k} {p : ℤ}
    (hroot : actualSource k t root = p)
    (hneg : actualSource k t neg = 2 * p - modulus k)
    (hnext : actualSource k t next = 4 * p - modulus k)
    (hrootQ : quarter k ≤ p)
    (hrootpos : 0 < p) (hrootbound : 3 * p ≤ modulus k)
    (hrootnext : root ≠ next) :
    root ≠ neg ∧ root ≠ next ∧ neg ≠ next := by
  have hN : 0 < modulus k := (source_geometry hk).2.2.2.1
  have hnegval : 2 * p - modulus k < 0 := by omega
  have hnextval : 0 < 4 * p - modulus k := by
    have hQ := (source_geometry hk).1
    have hNform := (source_geometry hk).2.1
    omega
  constructor
  · intro h
    have := congrArg (actualSource k t) h
    omega
  constructor
  · intro h
    exact hrootnext h
  · intro h
    have := congrArg (actualSource k t) h
    omega

theorem native_long_seed_three_cycle {k t : ℕ} (hk : 3 ≤ k)
    (hsmall : ∀ i : Fin k, |actualSource k t i| < quarter k →
      0 < actualSource k t i)
    (n : Fin k) (hn : actualSource k t n < 0) :
    ∃ (a root neg next : Fin k) (r : ℕ),
      r + 2 ≤ k ∧ root = phase (by omega) a r ∧
        quarter k ≤ actualSource k t root ∧
        (2 ≤ r → ∃ h : ℕ,
      1 ≤ h ∧ r = h + 1 ∧
        root = phase (by omega) a r ∧
        neg = phase (by omega) a (r + 1) ∧
        next = phase (by omega) a (r + 2) ∧
        0 < actualSource k t a ∧
        actualSource k t root = (2 : ℤ) ^ r * actualSource k t a ∧
        quarter k ≤ actualSource k t root ∧
        3 * actualSource k t root ≤ modulus k ∧
        actualSource k t neg = 2 * actualSource k t root - modulus k ∧
        actualSource k t neg < 0 ∧
        actualSource k t next = 4 * actualSource k t root - modulus k ∧
        0 < actualSource k t next ∧
        (∃ e : Equiv.Perm (Fin k),
          (e root = next ∧ e neg = root ∧ e next = neg ∧
            e.symm root = neg ∧ e.symm neg = next ∧ e.symm next = root)) ∧
        (let N := modulus k
         let U := fun z : ℤ => z + if z < 0 then N else 0
         U (actualSource k t neg) - U (actualSource k t root) =
           actualSource k t root ∧
         U (actualSource k t next) - U (actualSource k t neg) =
           actualSource k t neg)) := by
  obtain ⟨r, hr, hnodup, ha, hamod, hpre, hdyadic, hroot, hrootQ, hrootupper,
    hneg, hneglt, hnext, hnextpos, _, _, _, _⟩ :=
    native_chain_extraction hk hsmall n hn
  let a := phase (by omega : 0 < k) n 1
  let root := phase (by omega : 0 < k) a r
  let neg := phase (by omega : 0 < k) a (r + 1)
  let next := phase (by omega : 0 < k) a (r + 2)
  have hroot' : actualSource k t root = (2 : ℤ) ^ r * actualSource k t a := by
    simpa [root, a] using hroot
  have hneg' : actualSource k t neg = 2 * actualSource k t root - modulus k := by
    simpa [root, neg, a] using hneg
  have hnext' : actualSource k t next = 4 * actualSource k t root - modulus k := by
    simpa [root, next, a] using hnext
  have hrootQ' : quarter k ≤ actualSource k t root := by
    simpa [root, a] using hrootQ
  have hrootupper' : 3 * actualSource k t root ≤ modulus k := by
    simpa [root, a] using hrootupper
  have hneglt' : actualSource k t neg < 0 := by
    simpa [neg, a] using hneglt
  have hnextpos' : 0 < actualSource k t next := by
    simpa [next, a] using hnextpos
  have ha' : 0 < actualSource k t a := by
    simpa [a] using ha
  have hrootnext : root ≠ next := by
    intro heq
    by_cases hlt : r + 2 < k
    · have hidx : r = r + 2 :=
        phase_offset_injective (by omega : 0 < k) a (by omega) hlt
          (by simpa [root, next] using heq)
      omega
    · have hrk : r + 2 = k := by omega
      have hnexta : next = a := by
        dsimp [next]
        apply Fin.ext
        rw [hrk]
        change (a.val + k) % k = a.val
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt]
      have hroota : root = a := heq.trans hnexta
      have hroota' : phase (by omega) a r = phase (by omega) a 0 := by
        simpa [root, a, phase_zero] using hroota
      have hr0 := phase_offset_injective (by omega : 0 < k) a
        (by omega) (by omega) hroota'
      omega
  have hrootnegnext : (root ≠ neg ∧ root ≠ next ∧ neg ≠ next) := by
    exact native_distinct (p := actualSource k t root) hk rfl hneg' hnext' hrootQ'
      (by omega) hrootupper' hrootnext
  rcases hrootnegnext with ⟨hrn, hrx, hnx⟩
  have hnr : neg ≠ root := Ne.symm hrn
  have hxr : next ≠ root := Ne.symm hrx
  have hnx' : next ≠ neg := Ne.symm hnx
  refine ⟨a, root, neg, next, r, hr, rfl, hrootQ', ?_⟩
  intro hlong
  refine ⟨r - 1, by omega, by omega, rfl, rfl, rfl, ha', hroot', hrootQ',
      hrootupper', hneg', hneglt', hnext', hnextpos', ?_, ?_⟩
  · have hroles := physicalThreeCycle_roles root neg next hrn hrx hnx
    exact ⟨physicalThreeCycle root neg next hrn hrx hnx, hroles.1, hroles.2.1,
      hroles.2.2.1, hroles.2.2.2.1, hroles.2.2.2.2.1,
      hroles.2.2.2.2.2⟩
  · constructor
    · dsimp
      rw [hneg', hroot']
      have hn : 2 * (actualSource k t root) - modulus k < 0 := by omega
      simp [if_pos hn, if_neg (by omega : ¬ actualSource k t root < 0)]
      omega
    · dsimp
      rw [hnext', hneg']
      have hn : 2 * actualSource k t root - modulus k < 0 := by omega
      have hp : 0 < 4 * actualSource k t root - modulus k := by omega
      simp [if_pos hn, if_neg (not_lt_of_ge (le_of_lt hp))]
      omega
end D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle

#print axioms D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle.native_long_seed_three_cycle
