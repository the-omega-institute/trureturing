/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/Data/All
   generality: I
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:finite-exact-certificate)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/Main.makowski_schinzel_eta_le_42; premises=D5/S3/Arith/Divisors/MakowskiSchinzel/Data/All.roundOne_checked,D5/S3/Arith/Divisors/MakowskiSchinzel/Data/All.roundTwo_checked,D5/S3/Arith/Divisors/MakowskiSchinzel/Data/All.stage_shapes,D5/S3/Arith/Divisors/MakowskiSchinzel/Data/All.both_forbidden,D5/S3/Arith/Divisors/MakowskiSchinzel/Data/All.roundOne_forbidden,D5/S3/Arith/Divisors/MakowskiSchinzel/Data/All.roundTwo_forbidden,D5/S3/Arith/Divisors/MakowskiSchinzel/Data/All.conditional_forbidden,D5/S3/Arith/Divisors/MakowskiSchinzel/Data/All.three_forbidden,D5/S3/Arith/Divisors/MakowskiSchinzel/Data/All.small_prime_covered
   digest: Checked simultaneous exclusion stages and their exact forbidden supports. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix00
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix01
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix02
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix03
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix04
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix05
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix06
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix07
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix08
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix09
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix10
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix11
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix12
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Prefix13
import D5.S3.Arith.Divisors.MakowskiSchinzel.Data.Joint

/-! All prefix certificate stages, with each arithmetic check reused once. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.Arith.MakowskiSchinzel.Certificate.Data

/-- Simultaneous exclusion certificates with a common earlier forbidden support. -/
def roundOne : List PrefixCertificate :=
  [prefix00, prefix01, prefix02, prefix03, prefix04, prefix05, prefix06, prefix07, prefix08,
   prefix09, prefix10, prefix11, prefix12, prefix13, prefix14, prefix15, prefix16, prefix17,
   prefix18, prefix19, prefix20, prefix21, prefix22, prefix23, prefix24, prefix25, prefix26,
   prefix27, prefix28, prefix29, prefix30, prefix31, prefix32, prefix33, prefix34, prefix35,
   prefix36, prefix37, prefix38, prefix39, prefix40, prefix41, prefix42, prefix43, prefix44]

/-- Every check in the simultaneous exclusion stage is kernel verified. -/
theorem roundOne_checked : roundOne.all (·.check) = true := by
  have h00 : prefix00.check = true :=
    checked_member prefix00_checked (by simp)
  have h01 : prefix01.check = true :=
    checked_member prefix00_checked (by simp)
  have h02 : prefix02.check = true :=
    checked_member prefix00_checked (by simp)
  have h03 : prefix03.check = true :=
    checked_member prefix00_checked (by simp)
  have h04 : prefix04.check = true :=
    checked_member prefix01_checked (by simp)
  have h05 : prefix05.check = true :=
    checked_member prefix01_checked (by simp)
  have h06 : prefix06.check = true :=
    checked_member prefix01_checked (by simp)
  have h07 : prefix07.check = true :=
    checked_member prefix01_checked (by simp)
  have h08 : prefix08.check = true :=
    checked_member prefix02_checked (by simp)
  have h09 : prefix09.check = true :=
    checked_member prefix02_checked (by simp)
  have h10 : prefix10.check = true :=
    checked_member prefix02_checked (by simp)
  have h11 : prefix11.check = true :=
    checked_member prefix02_checked (by simp)
  have h12 : prefix12.check = true :=
    checked_member prefix03_checked (by simp)
  have h13 : prefix13.check = true :=
    checked_member prefix03_checked (by simp)
  have h14 : prefix14.check = true :=
    checked_member prefix03_checked (by simp)
  have h15 : prefix15.check = true :=
    checked_member prefix03_checked (by simp)
  have h16 : prefix16.check = true :=
    checked_member prefix04_checked (by simp)
  have h17 : prefix17.check = true :=
    checked_member prefix04_checked (by simp)
  have h18 : prefix18.check = true :=
    checked_member prefix04_checked (by simp)
  have h19 : prefix19.check = true :=
    checked_member prefix04_checked (by simp)
  have h20 : prefix20.check = true :=
    checked_member prefix05_checked (by simp)
  have h21 : prefix21.check = true :=
    checked_member prefix05_checked (by simp)
  have h22 : prefix22.check = true :=
    checked_member prefix05_checked (by simp)
  have h23 : prefix23.check = true :=
    checked_member prefix05_checked (by simp)
  have h24 : prefix24.check = true :=
    checked_member prefix06_checked (by simp)
  have h25 : prefix25.check = true :=
    checked_member prefix06_checked (by simp)
  have h26 : prefix26.check = true :=
    checked_member prefix06_checked (by simp)
  have h27 : prefix27.check = true :=
    checked_member prefix06_checked (by simp)
  have h28 : prefix28.check = true :=
    checked_member prefix07_checked (by simp)
  have h29 : prefix29.check = true :=
    checked_member prefix07_checked (by simp)
  have h30 : prefix30.check = true :=
    checked_member prefix07_checked (by simp)
  have h31 : prefix31.check = true :=
    checked_member prefix07_checked (by simp)
  have h32 : prefix32.check = true :=
    checked_member prefix08_checked (by simp)
  have h33 : prefix33.check = true :=
    checked_member prefix08_checked (by simp)
  have h34 : prefix34.check = true :=
    checked_member prefix08_checked (by simp)
  have h35 : prefix35.check = true :=
    checked_member prefix08_checked (by simp)
  have h36 : prefix36.check = true :=
    checked_member prefix09_checked (by simp)
  have h37 : prefix37.check = true :=
    checked_member prefix09_checked (by simp)
  have h38 : prefix38.check = true :=
    checked_member prefix09_checked (by simp)
  have h39 : prefix39.check = true :=
    checked_member prefix09_checked (by simp)
  have h40 : prefix40.check = true :=
    checked_member prefix10_checked (by simp)
  have h41 : prefix41.check = true :=
    checked_member prefix10_checked (by simp)
  have h42 : prefix42.check = true :=
    checked_member prefix10_checked (by simp)
  have h43 : prefix43.check = true :=
    checked_member prefix10_checked (by simp)
  have h44 : prefix44.check = true :=
    checked_member prefix11_checked (by simp)
  simp only [roundOne, List.all_cons, List.all_nil,
    h00, h01, h02, h03, h04, h05, h06, h07, h08, h09, h10, h11,
    h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
    h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35,
    h36, h37, h38, h39, h40, h41, h42, h43, h44, Bool.and_self]

/-- Simultaneous exclusion certificates with a common earlier forbidden support. -/
def roundTwo : List PrefixCertificate :=
  [prefix45, prefix46, prefix47, prefix48, prefix49]

/-- Every check in the simultaneous exclusion stage is kernel verified. -/
theorem roundTwo_checked : roundTwo.all (·.check) = true := by
  have h45 : prefix45.check = true :=
    checked_member prefix11_checked (by simp)
  have h46 : prefix46.check = true :=
    checked_member prefix11_checked (by simp)
  have h47 : prefix47.check = true :=
    checked_member prefix11_checked (by simp)
  have h48 : prefix48.check = true :=
    checked_member prefix12_checked (by simp)
  have h49 : prefix49.check = true :=
    checked_member prefix12_checked (by simp)
  simp only [roundTwo, List.all_cons, List.all_nil,
    h45, h46, h47, h48, h49, Bool.and_self]

/-- Every exclusion row has an odd prime modulus and the full budget of table entries. -/
theorem stage_shapes : ∀ c ∈ roundOne ++ roundTwo,
    c.r.Prime ∧ Odd c.r ∧ c.table.length = 42 := by decide

/-- The shared class forbids only already excluded supports. -/
theorem both_forbidden : ∀ s ∈ bothCertificate.forbidden,
    ∃ c ∈ roundOne ++ roundTwo, c.r = s := by decide

/-- Each first-stage forbidden support is empty. -/
theorem roundOne_forbidden : ∀ c ∈ roundOne, c.forbidden = [] := by decide

/-- Second-stage certificates forbid only members excluded in the first stage. -/
theorem roundTwo_forbidden :
    ∀ c ∈ roundTwo, ∀ s ∈ c.forbidden, ∃ d ∈ roundOne, d.r = s := by decide

/-- Conditional five and eleven tables use only earlier exclusions and the other prime. -/
theorem conditional_forbidden :
    (∀ s ∈ prefix50.forbidden, s = 11 ∨
      (∃ c ∈ roundOne ++ roundTwo, c.r = s)) ∧
    (∀ s ∈ prefix51.forbidden, s = 5 ∨
      (∃ c ∈ roundOne ++ roundTwo, c.r = s)) := by decide

/-- The final three-table uses only earlier exclusions and five and eleven. -/
theorem three_forbidden : ∀ s ∈ prefix52.forbidden,
    s = 5 ∨ s = 11 ∨ (∃ c ∈ roundOne ++ roundTwo, c.r = s) := by decide

/-- Every odd prime below one hundred thirty-one belongs to the exhausted support. -/
theorem small_prime_covered : ∀ r ∈ Finset.range 131,
    r.Prime → Odd r → r = 3 ∨ r = 5 ∨ r = 11 ∨
      (∃ c ∈ roundOne ++ roundTwo, c.r = r) := by decide

end D5.S3.Arith.MakowskiSchinzel.Certificate.Data
