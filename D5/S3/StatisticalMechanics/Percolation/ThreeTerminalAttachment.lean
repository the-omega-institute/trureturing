/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalAttachment
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalAttachment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent terminal attachment preserves a strengthened determinant bound. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalBond

/-! The source is a finite product pushforward, before its five entries are expanded. -/

set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment

open ThreeTerminalBond
open scoped BigOperators

/-- The terminal through which an independent network is attached. -/
inductive Port where
  | a | b | c
  deriving DecidableEq, Fintype

/-- A closed attachment separates its labelled terminal from its old block. -/
def detach (port : Port) (s : Mode) (bit : Bool) : Mode :=
  if bit then s else match port,s with
    | .a,.all | .a,.bc => .bc
    | .b,.all | .b,.ac => .ac
    | .c,.all | .c,.ab => .ab
    | _,_ => .separate

/-- Push forward the product of the original five-partition source and one
independent Bernoulli bit. No entrywise transfer formula defines this source. -/
def transfer (port : Port) (p : Mode → ℝ) (q : ℝ) (s : Mode) : ℝ :=
  ∑ t : Mode, ∑ bit : Bool,
    if detach port t bit = s then p t * (if bit then q else 1-q) else 0

private theorem transfer_values (p : Mode → ℝ) (q : ℝ) :
    transfer .a p q = (fun s => match s with
      | .separate => p .separate+(1-q)*(p .ab+p .ac)
      | .ab => q*p .ab
      | .bc => p .bc+(1-q)*p .all
      | .all => q*p .all
      | .ac => q*p .ac) ∧
    transfer .b p q = (fun s => match s with
      | .separate => p .separate+(1-q)*(p .ab+p .bc)
      | .ab => q*p .ab
      | .bc => q*p .bc
      | .all => q*p .all
      | .ac => p .ac+(1-q)*p .all) ∧
    transfer .c p q = (fun s => match s with
      | .separate => p .separate+(1-q)*(p .bc+p .ac)
      | .ab => p .ab+(1-q)*p .all
      | .bc => q*p .bc
      | .all => q*p .all
      | .ac => q*p .ac) := by
  have henum : (Finset.univ : Finset Mode) = {.separate,.ab,.bc,.all,.ac} := by decide
  repeat' constructor
  all_goals funext s
  all_goals cases s <;> simp [transfer,detach,henum,Fintype.sum_bool] <;> ring

private theorem transfer_defects (p : Mode → ℝ) (q : ℝ) :
    delta (transfer .a p q) = q*delta p+q*(1-q)*p .all*p .ac ∧
    delta (transfer .b p q) = q^2*delta p+
      q*(1-q)*p .all*(p .separate+p .ab+p .bc) ∧
    delta (transfer .c p q) = q*delta p+q*(1-q)*p .all*p .ac := by
  obtain ⟨ha,hb,hc⟩ := transfer_values p q
  constructor
  · rw [ha]
    simp only [delta]
    ring
  constructor
  · rw [hb]
    simp only [delta]
    ring
  · rw [hc]
    simp only [delta]
    ring

/-- A normalized nonnegative five-mode source with the strengthened defect
bound retains it after independent attachment at any one of its three labels.
All boundary rates, zero ac mass and every constant at least one are included. -/
theorem attachment_invariant (p : Mode → ℝ) (hp : ∀ s, 0 ≤ p s)
    (hn : ∑ s, p s = 1) (C : ℝ) (hC : 1 ≤ C) (q : ℝ)
    (hq : q ∈ Set.Icc 0 1) (hlow : 0 ≤ delta p)
    (hbound : delta p+p .all*p .ac ≤ C*p .ac) :
    ∀ port, 0 ≤ delta (transfer port p q) ∧
      delta (transfer port p q)+transfer port p q .all*transfer port p q .ac ≤
        C*transfer port p q .ac := by
  obtain ⟨ha,hb,hc⟩ := transfer_values p q
  have hqa := hq.1
  have hqb := hq.2
  have hqc : 0 ≤ 1-q := sub_nonneg.mpr hqb
  have hT := hp .all
  have hZ := hp .ac
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  obtain ⟨hda,hdb,hdc⟩ := transfer_defects p q
  have hsa : delta (transfer .a p q)+transfer .a p q .all*transfer .a p q .ac =
      q*(delta p+p .all*p .ac) := by
    rw [hda,ha]
    dsimp only
    ring
  have hsc : delta (transfer .c p q)+transfer .c p q .all*transfer .c p q .ac =
      q*(delta p+p .all*p .ac) := by
    rw [hdc,hc]
    dsimp only
    ring
  have hsb : delta (transfer .b p q)+transfer .b p q .all*transfer .b p q .ac =
      q^2*(delta p+p .all*p .ac)+q*(1-q)*p .all := by
    have henum : (Finset.univ : Finset Mode) = {.separate,.ab,.bc,.all,.ac} := by decide
    have hn' : p .separate+p .ab+p .bc+p .all+p .ac = 1 := by
      simpa [henum,add_assoc] using hn
    rw [hdb,hb]
    dsimp only
    linear_combination q*(1-q)*p .all*hn'
  intro port
  cases port with
  | a =>
    constructor
    · rw [hda]
      positivity
    · calc
        _ = q*(delta p+p .all*p .ac) := hsa
        _ ≤ q*(C*p .ac) := mul_le_mul_of_nonneg_left hbound hqa
        _ = C*transfer .a p q .ac := by rw [ha]; dsimp only; ring
  | b =>
    constructor
    · rw [hdb]
      have hN := hp .separate
      have hA := hp .ab
      have hB := hp .bc
      positivity
    · have hq2 : q^2 ≤ 1 := by
        have hh := mul_nonneg hqc (show 0 ≤ 1+q by linarith)
        nlinarith only [hh]
      have hcz := mul_nonneg hC0 hZ
      have hzbound : q^2*(C*p .ac) ≤ C*p .ac := by
        simpa using mul_le_mul_of_nonneg_right hq2 hcz
      have htbound : q*(1-q)*p .all ≤ C*(1-q)*p .all := by
        have hh := mul_le_mul_of_nonneg_right (le_trans hqb hC) (mul_nonneg hqc hT)
        simpa only [mul_assoc] using hh
      calc
        _ = q^2*(delta p+p .all*p .ac)+q*(1-q)*p .all := hsb
        _ ≤ q^2*(C*p .ac)+q*(1-q)*p .all :=
          add_le_add (mul_le_mul_of_nonneg_left hbound (sq_nonneg q)) le_rfl
        _ ≤ C*p .ac+C*(1-q)*p .all := add_le_add hzbound htbound
        _ = C*transfer .b p q .ac := by rw [hb]; dsimp only; ring
  | c =>
    constructor
    · rw [hdc]
      positivity
    · calc
        _ = q*(delta p+p .all*p .ac) := hsc
        _ ≤ q*(C*p .ac) := mul_le_mul_of_nonneg_left hbound hqa
        _ = C*transfer .c p q .ac := by rw [hc]; dsimp only; ring

/-- The absolute strengthened determinant bound is preserved by independent
attachment, without assuming a sign for the original determinant. -/
theorem attachment_signed_invariant (p : Mode → ℝ) (hp : ∀ s, 0 ≤ p s)
    (hn : ∑ s, p s = 1) (C : ℝ) (hC : 1 ≤ C) (q : ℝ)
    (hq : q ∈ Set.Icc 0 1)
    (hbound : |delta p|+p .all*p .ac ≤ C*p .ac) :
    ∀ port, |delta (transfer port p q)|+
      transfer port p q .all*transfer port p q .ac ≤
        C*transfer port p q .ac := by
  obtain ⟨ha,hb,hc⟩ := transfer_values p q
  obtain ⟨hda,hdb,hdc⟩ := transfer_defects p q
  have hqa := hq.1
  have hqb := hq.2
  have hqc : 0 ≤ 1-q := sub_nonneg.mpr hqb
  have hT := hp .all
  have hZ := hp .ac
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hrem : 0 ≤ q*(1-q)*p .all*p .ac := by positivity
  have habsa : |delta (transfer .a p q)| ≤
      q*|delta p|+q*(1-q)*p .all*p .ac := by
    rw [hda]
    calc
      _ ≤ |q*delta p|+|q*(1-q)*p .all*p .ac| := abs_add_le _ _
      _ = _ := by rw [abs_mul,abs_of_nonneg hqa,abs_of_nonneg hrem]
  have habsc : |delta (transfer .c p q)| ≤
      q*|delta p|+q*(1-q)*p .all*p .ac := by
    rw [hdc]
    calc
      _ ≤ |q*delta p|+|q*(1-q)*p .all*p .ac| := abs_add_le _ _
      _ = _ := by rw [abs_mul,abs_of_nonneg hqa,abs_of_nonneg hrem]
  have hremb : 0 ≤ q*(1-q)*p .all*(p .separate+p .ab+p .bc) := by
    have hN := hp .separate
    have hA := hp .ab
    have hB := hp .bc
    positivity
  have habsb : |delta (transfer .b p q)| ≤ q^2*|delta p|+
      q*(1-q)*p .all*(p .separate+p .ab+p .bc) := by
    rw [hdb]
    calc
      _ ≤ |q^2*delta p|+|q*(1-q)*p .all*(p .separate+p .ab+p .bc)| :=
        abs_add_le _ _
      _ = _ := by rw [abs_mul,abs_of_nonneg (sq_nonneg q),abs_of_nonneg hremb]
  intro port
  cases port with
  | a =>
    calc
      _ ≤ (q*|delta p|+q*(1-q)*p .all*p .ac)+
          transfer .a p q .all*transfer .a p q .ac := add_le_add habsa le_rfl
      _ = q*(|delta p|+p .all*p .ac) := by rw [ha]; dsimp only; ring
      _ ≤ q*(C*p .ac) := mul_le_mul_of_nonneg_left hbound hqa
      _ = C*transfer .a p q .ac := by rw [ha]; dsimp only; ring
  | b =>
    have henum : (Finset.univ : Finset Mode) = {.separate,.ab,.bc,.all,.ac} := by decide
    have hn' : p .separate+p .ab+p .bc+p .all+p .ac = 1 := by
      simpa [henum,add_assoc] using hn
    have hq2 : q^2 ≤ 1 := by
      have hh := mul_nonneg hqc (show 0 ≤ 1+q by linarith)
      nlinarith only [hh]
    have hzbound : q^2*(C*p .ac) ≤ C*p .ac := by
      simpa using mul_le_mul_of_nonneg_right hq2 (mul_nonneg hC0 hZ)
    have htbound : q*(1-q)*p .all ≤ C*(1-q)*p .all := by
      have hh := mul_le_mul_of_nonneg_right (le_trans hqb hC) (mul_nonneg hqc hT)
      simpa only [mul_assoc] using hh
    calc
      _ ≤ (q^2*|delta p|+q*(1-q)*p .all*(p .separate+p .ab+p .bc))+
          transfer .b p q .all*transfer .b p q .ac := add_le_add habsb le_rfl
      _ = q^2*(|delta p|+p .all*p .ac)+q*(1-q)*p .all := by
        rw [hb]
        dsimp only
        linear_combination q*(1-q)*p .all*hn'
      _ ≤ q^2*(C*p .ac)+q*(1-q)*p .all :=
        add_le_add (mul_le_mul_of_nonneg_left hbound (sq_nonneg q)) le_rfl
      _ ≤ C*p .ac+C*(1-q)*p .all := add_le_add hzbound htbound
      _ = C*transfer .b p q .ac := by rw [hb]; dsimp only; ring
  | c =>
    calc
      _ ≤ (q*|delta p|+q*(1-q)*p .all*p .ac)+
          transfer .c p q .all*transfer .c p q .ac := add_le_add habsc le_rfl
      _ = q*(|delta p|+p .all*p .ac) := by rw [hc]; dsimp only; ring
      _ ≤ q*(C*p .ac) := mul_le_mul_of_nonneg_left hbound hqa
      _ = C*transfer .c p q .ac := by rw [hc]; dsimp only; ring

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment.attachment_signed_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms attachment_signed_invariant

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment.attachment_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms attachment_invariant

end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalAttachment
