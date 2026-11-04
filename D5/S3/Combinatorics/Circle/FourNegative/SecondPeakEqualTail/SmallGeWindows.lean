/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/SmallGeWindows
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Universal positive-coefficient identities for the original paired seam windows. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Algebra

/-! Exact equal-tail polynomial windows. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
open private A B L K SU SV SW scaledGates from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Algebra

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem small_l_ge_windows (p h s : ℤ) (hp : 2≤p) (hh : 1≤h) (hs : 1≤s) :
    ∀ i : Fin 12, 0≤scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 i := by
  let uP := p-2
  have huP : 0≤uP := by dsimp [uP]; omega
  let uS := h-1
  have huS : 0≤uS := by dsimp [uS]; omega
  let uR := s-1
  have huR : 0≤uR := by dsimp [uR]; omega
  intro i
  fin_cases i
  · have expansion : scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 0 =
      256 * uP^8 * uS^3 * uR + 256 * uP^8 * uS^3 + 768 * uP^8 * uS^2 * uR
      + 768 * uP^8 * uS^2 + 768 * uP^8 * uS * uR + 768 * uP^8 * uS
      + 256 * uP^8 * uR + 256 * uP^8 + 4096 * uP^7 * uS^3 * uR
      + 4096 * uP^7 * uS^3 + 12032 * uP^7 * uS^2 * uR + 12032 * uP^7 * uS^2
      + 11776 * uP^7 * uS * uR + 11776 * uP^7 * uS + 3840 * uP^7 * uR
      + 3840 * uP^7 + 28928 * uP^6 * uS^3 * uR + 28928 * uP^6 * uS^3
      + 83584 * uP^6 * uS^2 * uR + 83584 * uP^6 * uS^2 + 80384 * uP^6 * uS * uR
      + 80384 * uP^6 * uS + 25728 * uP^6 * uR + 25728 * uP^6
      + 117760 * uP^5 * uS^3 * uR + 117760 * uP^5 * uS^3 + 336320 * uP^5 * uS^2 * uR
      + 336320 * uP^5 * uS^2 + 319360 * uP^5 * uS * uR + 319360 * uP^5 * uS
      + 100800 * uP^5 * uR + 100800 * uP^5 + 302080 * uP^4 * uS^3 * uR
      + 302080 * uP^4 * uS^3 + 856960 * uP^4 * uS^2 * uR + 856960 * uP^4 * uS^2
      + 807616 * uP^4 * uS * uR + 807616 * uP^4 * uS + 252736 * uP^4 * uR
      + 252736 * uP^4 + 499712 * uP^3 * uS^3 * uR + 499712 * uP^3 * uS^3
      + 1414720 * uP^3 * uS^2 * uR + 1414720 * uP^3 * uS^2 + 1329888 * uP^3 * uS * uR
      + 1329888 * uP^3 * uS + 414880 * uP^3 * uR + 414880 * uP^3
      + 520192 * uP^2 * uS^3 * uR + 520192 * uP^2 * uS^3 + 1475968 * uP^2 * uS^2 * uR
      + 1475968 * uP^2 * uS^2 + 1390384 * uP^2 * uS * uR + 1390384 * uP^2 * uS
      + 434608 * uP^2 * uR + 434608 * uP^2 + 311296 * uP * uS^3 * uR
      + 311296 * uP * uS^3 + 888576 * uP * uS^2 * uR + 888576 * uP * uS^2
      + 842288 * uP * uS * uR + 842296 * uP * uS + 264992 * uP * uR
      + 265000 * uP + 81920 * uS^3 * uR + 81920 * uS^3
      + 236032 * uS^2 * uR + 236032 * uS^2 + 225952 * uS * uR
      + 225976 * uS + 71816 * uR + 71848 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uS,uR]
      ring
    change 0≤scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 0
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 1 =
      512 * uP^9 * uS^3 * uR + 512 * uP^9 * uS^3 + 1536 * uP^9 * uS^2 * uR
      + 1536 * uP^9 * uS^2 + 1536 * uP^9 * uS * uR + 1536 * uP^9 * uS
      + 512 * uP^9 * uR + 512 * uP^9 + 8960 * uP^8 * uS^3 * uR
      + 8960 * uP^8 * uS^3 + 26880 * uP^8 * uS^2 * uR + 26880 * uP^8 * uS^2
      + 26880 * uP^8 * uS * uR + 26880 * uP^8 * uS + 8960 * uP^8 * uR
      + 8960 * uP^8 + 69632 * uP^7 * uS^3 * uR + 69632 * uP^7 * uS^3
      + 209152 * uP^7 * uS^2 * uR + 209152 * uP^7 * uS^2 + 209408 * uP^7 * uS * uR
      + 209408 * uP^7 * uS + 69888 * uP^7 * uR + 69888 * uP^7
      + 315136 * uP^6 * uS^3 * uR + 315136 * uP^6 * uS^3 + 948736 * uP^6 * uS^2 * uR
      + 948736 * uP^6 * uS^2 + 952064 * uP^6 * uS * uR + 952064 * uP^6 * uS
      + 318464 * uP^6 * uR + 318464 * uP^6 + 914432 * uP^5 * uS^3 * uR
      + 914432 * uP^5 * uS^3 + 2761792 * uP^5 * uS^2 * uR + 2761792 * uP^5 * uS^2
      + 2780288 * uP^5 * uS * uR + 2780288 * uP^5 * uS + 932928 * uP^5 * uR
      + 932928 * uP^5 + 1762304 * uP^4 * uS^3 * uR + 1762304 * uP^4 * uS^3
      + 5343872 * uP^4 * uS^2 * uR + 5343872 * uP^4 * uS^2 + 5400896 * uP^4 * uS * uR
      + 5400896 * uP^4 * uS + 1819328 * uP^4 * uR + 1819328 * uP^4
      + 2252800 * uP^3 * uS^3 * uR + 2252800 * uP^3 * uS^3 + 6863296 * uP^3 * uS^2 * uR
      + 6863296 * uP^3 * uS^2 + 6968640 * uP^3 * uS * uR + 6968640 * uP^3 * uS
      + 2358144 * uP^3 * uR + 2358144 * uP^3 + 1839104 * uP^2 * uS^3 * uR
      + 1839104 * uP^2 * uS^3 + 5632640 * uP^2 * uS^2 * uR + 5632640 * uP^2 * uS^2
      + 5749136 * uP^2 * uS * uR + 5749136 * uP^2 * uS + 1955600 * uP^2 * uR
      + 1955600 * uP^2 + 868352 * uP * uS^3 * uR + 868352 * uP * uS^3
      + 2674944 * uP * uS^2 * uR + 2674944 * uP * uS^2 + 2746192 * uP * uS * uR
      + 2746184 * uP * uS + 939616 * uP * uR + 939608 * uP
      + 180224 * uS^3 * uR + 180224 * uS^3 + 558592 * uS^2 * uR
      + 558592 * uS^2 + 577120 * uS * uR + 577096 * uS
      + 198776 * uR + 198744 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uS,uR]
      ring
    change 0≤scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 1
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 2 =
      256 * uP^8 * uS^3 * uR + 256 * uP^8 * uS^3 + 768 * uP^8 * uS^2 * uR
      + 768 * uP^8 * uS^2 + 768 * uP^8 * uS * uR + 768 * uP^8 * uS
      + 256 * uP^8 * uR + 256 * uP^8 + 3840 * uP^7 * uS^3 * uR
      + 3968 * uP^7 * uS^3 + 11520 * uP^7 * uS^2 * uR + 11904 * uP^7 * uS^2
      + 11520 * uP^7 * uS * uR + 11904 * uP^7 * uS + 3840 * uP^7 * uR
      + 3968 * uP^7 + 25088 * uP^6 * uS^3 * uR + 27008 * uP^6 * uS^3
      + 75136 * uP^6 * uS^2 * uR + 80896 * uP^6 * uS^2 + 75008 * uP^6 * uS * uR
      + 80768 * uP^6 * uS + 24960 * uP^6 * uR + 26880 * uP^6
      + 93184 * uP^5 * uS^3 * uR + 105472 * uP^5 * uS^3 + 278208 * uP^5 * uS^2 * uR
      + 315104 * uP^5 * uS^2 + 276864 * uP^5 * uS * uR + 313792 * uP^5 * uS
      + 91840 * uP^5 * uR + 104160 * uP^5 + 215040 * uP^4 * uS^3 * uR
      + 258560 * uP^4 * uS^3 + 639296 * uP^4 * uS^2 * uR + 770208 * uP^4 * uS^2
      + 633472 * uP^4 * uS * uR + 764736 * uP^4 * uS + 209216 * uP^4 * uR
      + 253088 * uP^4 + 315392 * uP^3 * uS^3 * uR + 407552 * uP^3 * uS^3
      + 932864 * uP^3 * uS^2 * uR + 1210880 * uP^3 * uS^2 + 919520 * uP^3 * uS * uR
      + 1199072 * uP^3 * uS + 302048 * uP^3 * uR + 395744 * uP^3
      + 286720 * uP^2 * uS^3 * uR + 403456 * uP^2 * uS^3 + 843264 * uP^2 * uS^2 * uR
      + 1196800 * uP^2 * uS^2 + 826160 * uP^2 * uS * uR + 1183064 * uP^2 * uS
      + 269616 * uP^2 * uR + 389720 * uP^2 + 147456 * uP * uS^3 * uR
      + 229376 * uP * uS^3 + 431104 * uP * uS^2 * uR + 680448 * uP * uS^2
      + 419376 * uP * uS * uR + 672472 * uP * uS + 135728 * uP * uR
      + 221400 * uP + 32768 * uS^3 * uR + 57344 * uS^3
      + 95232 * uS^2 * uR + 170496 * uS^2 + 91808 * uS * uR
      + 168784 * uS + 29336 * uR + 55632 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uS,uR]
      ring
    change 0≤scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 2
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 3 =
      256 * uP^8 * uS^3 * uR + 256 * uP^8 * uS^3 + 768 * uP^8 * uS^2 * uR
      + 768 * uP^8 * uS^2 + 768 * uP^8 * uS * uR + 768 * uP^8 * uS
      + 256 * uP^8 * uR + 256 * uP^8 + 4352 * uP^7 * uS^3 * uR
      + 4224 * uP^7 * uS^3 + 13056 * uP^7 * uS^2 * uR + 12672 * uP^7 * uS^2
      + 13056 * uP^7 * uS * uR + 12672 * uP^7 * uS + 4352 * uP^7 * uR
      + 4224 * uP^7 + 32256 * uP^6 * uS^3 * uR + 30336 * uP^6 * uS^3
      + 96896 * uP^6 * uS^2 * uR + 91136 * uP^6 * uS^2 + 97024 * uP^6 * uS * uR
      + 91264 * uP^6 * uS + 32384 * uP^6 * uR + 30464 * uP^6
      + 136192 * uP^5 * uS^3 * uR + 123904 * uP^5 * uS^3 + 410048 * uP^5 * uS^2 * uR
      + 373152 * uP^5 * uS^2 + 411520 * uP^5 * uS * uR + 374592 * uP^5 * uS
      + 137664 * uP^5 * uR + 125344 * uP^5 + 358400 * uP^4 * uS^3 * uR
      + 314880 * uP^4 * uS^3 + 1082304 * uP^4 * uS^2 * uR + 951392 * uP^4 * uS^2
      + 1089408 * uP^4 * uS * uR + 958144 * uP^4 * uS + 365504 * uP^4 * uR
      + 321632 * uP^4 + 602112 * uP^3 * uS^3 * uR + 509952 * uP^3 * uS^3
      + 1824768 * uP^3 * uS^2 * uR + 1546752 * uP^3 * uS^2 + 1843232 * uP^3 * uS * uR
      + 1563680 * uP^3 * uS + 620576 * uP^3 * uR + 526880 * uP^3
      + 630784 * uP^2 * uS^3 * uR + 514048 * uP^2 * uS^3 + 1919488 * uP^2 * uS^2 * uR
      + 1565952 * uP^2 * uS^2 + 1946832 * uP^2 * uS * uR + 1589944 * uP^2 * uS
      + 658128 * uP^2 * uR + 538040 * uP^2 + 376832 * uP * uS^3 * uR
      + 294912 * uP * uS^3 + 1152000 * uP * uS^2 * uR + 902656 * uP * uS^2
      + 1173968 * uP * uS * uR + 920936 * uP * uS + 398800 * uP * uR
      + 313192 * uP + 98304 * uS^3 * uR + 73728 * uS^3
      + 302080 * uS^2 * uR + 226816 * uS^2 + 309600 * uS * uR
      + 232688 * uS + 105832 * uR + 79600 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uS,uR]
      ring
    change 0≤scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 3
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 4 =
      256 * uP^8 * uS^3 * uR + 256 * uP^8 * uS^3 + 768 * uP^8 * uS^2 * uR
      + 768 * uP^8 * uS^2 + 768 * uP^8 * uS * uR + 768 * uP^8 * uS
      + 256 * uP^8 * uR + 256 * uP^8 + 3840 * uP^7 * uS^3 * uR
      + 3968 * uP^7 * uS^3 + 11520 * uP^7 * uS^2 * uR + 11904 * uP^7 * uS^2
      + 11520 * uP^7 * uS * uR + 11904 * uP^7 * uS + 3840 * uP^7 * uR
      + 3968 * uP^7 + 25088 * uP^6 * uS^3 * uR + 27008 * uP^6 * uS^3
      + 75136 * uP^6 * uS^2 * uR + 80896 * uP^6 * uS^2 + 75008 * uP^6 * uS * uR
      + 80768 * uP^6 * uS + 24960 * uP^6 * uR + 26880 * uP^6
      + 93184 * uP^5 * uS^3 * uR + 105472 * uP^5 * uS^3 + 277952 * uP^5 * uS^2 * uR
      + 314976 * uP^5 * uS^2 + 276352 * uP^5 * uS * uR + 313536 * uP^5 * uS
      + 91584 * uP^5 * uR + 104032 * uP^5 + 215040 * uP^4 * uS^3 * uR
      + 258560 * uP^4 * uS^3 + 636736 * uP^4 * uS^2 * uR + 768928 * uP^4 * uS^2
      + 628352 * uP^4 * uS * uR + 762176 * uP^4 * uS + 206656 * uP^4 * uR
      + 251808 * uP^4 + 315392 * uP^3 * uS^3 * uR + 407552 * uP^3 * uS^3
      + 922624 * uP^3 * uS^2 * uR + 1205760 * uP^3 * uS^2 + 899040 * uP^3 * uS * uR
      + 1188864 * uP^3 * uS + 291808 * uP^3 * uR + 390656 * uP^3
      + 286720 * uP^2 * uS^3 * uR + 403456 * uP^2 * uS^3 + 822784 * uP^2 * uS^2 * uR
      + 1186560 * uP^2 * uS^2 + 785200 * uP^2 * uS * uR + 1162744 * uP^2 * uS
      + 249136 * uP^2 * uR + 379640 * uP^2 + 147456 * uP * uS^3 * uR
      + 229376 * uP * uS^3 + 410624 * uP * uS^2 * uR + 670208 * uP * uS^2
      + 378416 * uP * uS * uR + 652248 * uP * uS + 115248 * uP * uR
      + 211416 * uP + 32768 * uS^3 * uR + 57344 * uS^3
      + 87040 * uS^2 * uR + 166400 * uS^2 + 75424 * uS * uR
      + 160720 * uS + 21144 * uR + 51664 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uS,uR]
      ring
    change 0≤scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 4
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 5 =
      256 * uP^8 * uS^3 * uR + 256 * uP^8 * uS^3 + 768 * uP^8 * uS^2 * uR
      + 768 * uP^8 * uS^2 + 768 * uP^8 * uS * uR + 768 * uP^8 * uS
      + 256 * uP^8 * uR + 256 * uP^8 + 4352 * uP^7 * uS^3 * uR
      + 4224 * uP^7 * uS^3 + 13056 * uP^7 * uS^2 * uR + 12672 * uP^7 * uS^2
      + 13056 * uP^7 * uS * uR + 12672 * uP^7 * uS + 4352 * uP^7 * uR
      + 4224 * uP^7 + 32256 * uP^6 * uS^3 * uR + 30336 * uP^6 * uS^3
      + 96896 * uP^6 * uS^2 * uR + 91136 * uP^6 * uS^2 + 97024 * uP^6 * uS * uR
      + 91264 * uP^6 * uS + 32384 * uP^6 * uR + 30464 * uP^6
      + 136192 * uP^5 * uS^3 * uR + 123904 * uP^5 * uS^3 + 410176 * uP^5 * uS^2 * uR
      + 373216 * uP^5 * uS^2 + 411776 * uP^5 * uS * uR + 374720 * uP^5 * uS
      + 137792 * uP^5 * uR + 125408 * uP^5 + 358400 * uP^4 * uS^3 * uR
      + 314880 * uP^4 * uS^3 + 1083584 * uP^4 * uS^2 * uR + 952032 * uP^4 * uS^2
      + 1091968 * uP^4 * uS * uR + 959424 * uP^4 * uS + 366784 * uP^4 * uR
      + 322272 * uP^4 + 602112 * uP^3 * uS^3 * uR + 509952 * uP^3 * uS^3
      + 1829888 * uP^3 * uS^2 * uR + 1549312 * uP^3 * uS^2 + 1853472 * uP^3 * uS * uR
      + 1568784 * uP^3 * uS + 625696 * uP^3 * uR + 529424 * uP^3
      + 630784 * uP^2 * uS^3 * uR + 514048 * uP^2 * uS^3 + 1929728 * uP^2 * uS^2 * uR
      + 1571072 * uP^2 * uS^2 + 1967312 * uP^2 * uS * uR + 1600104 * uP^2 * uS
      + 668368 * uP^2 * uR + 543080 * uP^2 + 376832 * uP * uS^3 * uR
      + 294912 * uP * uS^3 + 1162240 * uP * uS^2 * uR + 907776 * uP * uS^2
      + 1194448 * uP * uS * uR + 931048 * uP * uS + 409040 * uP * uR
      + 318184 * uP + 98304 * uS^3 * uR + 73728 * uS^3
      + 306176 * uS^2 * uR + 228864 * uS^2 + 317792 * uS * uR
      + 236720 * uS + 109928 * uR + 81584 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uS,uR]
      ring
    change 0≤scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 5
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 6 =
      1536 * uP^8 * uS^3 * uR + 1536 * uP^8 * uS^3 + 4608 * uP^8 * uS^2 * uR
      + 4608 * uP^8 * uS^2 + 4608 * uP^8 * uS * uR + 4608 * uP^8 * uS
      + 1536 * uP^8 * uR + 1536 * uP^8 + 24320 * uP^7 * uS^3 * uR
      + 24320 * uP^7 * uS^3 + 72448 * uP^7 * uS^2 * uR + 72448 * uP^7 * uS^2
      + 71936 * uP^7 * uS * uR + 71936 * uP^7 * uS + 23808 * uP^7 * uR
      + 23808 * uP^7 + 168704 * uP^6 * uS^3 * uR + 168704 * uP^6 * uS^3
      + 499456 * uP^6 * uS^2 * uR + 499456 * uP^6 * uS^2 + 492800 * uP^6 * uS * uR
      + 492800 * uP^6 * uS + 162048 * uP^6 * uR + 162048 * uP^6
      + 669696 * uP^5 * uS^3 * uR + 669696 * uP^5 * uS^3 + 1972416 * uP^5 * uS^2 * uR
      + 1972416 * uP^5 * uS^2 + 1935744 * uP^5 * uS * uR + 1935744 * uP^5 * uS
      + 633024 * uP^5 * uR + 633024 * uP^5 + 1664000 * uP^4 * uS^3 * uR
      + 1664000 * uP^4 * uS^3 + 4881280 * uP^4 * uS^2 * uR + 4881280 * uP^4 * uS^2
      + 4770496 * uP^4 * uS * uR + 4770496 * uP^4 * uS + 1553216 * uP^4 * uR
      + 1553216 * uP^4 + 2650112 * uP^3 * uS^3 * uR + 2650112 * uP^3 * uS^3
      + 7753280 * uP^3 * uS^2 * uR + 7753280 * uP^3 * uS^2 + 7555808 * uP^3 * uS * uR
      + 7555808 * uP^3 * uS + 2452640 * uP^3 * uR + 2452640 * uP^3
      + 2641920 * uP^2 * uS^3 * uR + 2641920 * uP^2 * uS^3 + 7720320 * uP^2 * uS^2 * uR
      + 7720320 * uP^2 * uS^2 + 7513904 * uP^2 * uS * uR + 7513936 * uP^2 * uS
      + 2435504 * uP^2 * uR + 2435536 * uP^2 + 1507328 * uP * uS^3 * uR
      + 1507328 * uP * uS^3 + 4407040 * uP * uS^2 * uR + 4407040 * uP * uS^2
      + 4291120 * uP * uS * uR + 4291256 * uP * uS + 1391392 * uP * uR
      + 1391528 * uP + 376832 * uS^3 * uR + 376832 * uS^3
      + 1104384 * uS^2 * uR + 1104384 * uS^2 + 1077920 * uS * uR
      + 1078072 * uS + 350344 * uR + 350512 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uS,uR]
      ring
    change 0≤scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 6
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 7 =
      1024 * uP^9 * uS^3 * uR + 1024 * uP^9 * uS^3 + 3072 * uP^9 * uS^2 * uR
      + 3072 * uP^9 * uS^2 + 3072 * uP^9 * uS * uR + 3072 * uP^9 * uS
      + 1024 * uP^9 * uR + 1024 * uP^9 + 16896 * uP^8 * uS^3 * uR
      + 16896 * uP^8 * uS^3 + 50688 * uP^8 * uS^2 * uR + 50688 * uP^8 * uS^2
      + 50688 * uP^8 * uS * uR + 50688 * uP^8 * uS + 16896 * uP^8 * uR
      + 16896 * uP^8 + 123136 * uP^7 * uS^3 * uR + 123136 * uP^7 * uS^3
      + 369920 * uP^7 * uS^2 * uR + 369920 * uP^7 * uS^2 + 370432 * uP^7 * uS * uR
      + 370432 * uP^7 * uS + 123648 * uP^7 * uR + 123648 * uP^7
      + 519424 * uP^6 * uS^3 * uR + 519424 * uP^6 * uS^3 + 1565056 * uP^6 * uS^2 * uR
      + 1565056 * uP^6 * uS^2 + 1571840 * uP^6 * uS * uR + 1571840 * uP^6 * uS
      + 526208 * uP^6 * uR + 526208 * uP^6 + 1394688 * uP^5 * uS^3 * uR
      + 1394688 * uP^5 * uS^3 + 4222272 * uP^5 * uS^2 * uR + 4222272 * uP^5 * uS^2
      + 4260480 * uP^5 * uS * uR + 4260480 * uP^5 * uS + 1432896 * uP^5 * uR
      + 1432896 * uP^5 + 2464768 * uP^4 * uS^3 * uR + 2464768 * uP^4 * uS^3
      + 7512704 * uP^4 * uS^2 * uR + 7512704 * uP^4 * uS^2 + 7631168 * uP^4 * uS * uR
      + 7631168 * uP^4 * uS + 2583232 * uP^4 * uR + 2583232 * uP^4
      + 2854912 * uP^3 * uS^3 * uR + 2854912 * uP^3 * uS^3 + 8782272 * uP^3 * uS^2 * uR
      + 8782272 * uP^3 * uS^2 + 9000256 * uP^3 * uS * uR + 9000256 * uP^3 * uS
      + 3072896 * uP^3 * uR + 3072896 * uP^3 + 2076672 * uP^2 * uS^3 * uR
      + 2076672 * uP^2 * uS^3 + 6466176 * uP^2 * uS^2 * uR + 6466176 * uP^2 * uS^2
      + 6703504 * uP^2 * uS * uR + 6703472 * uP^2 * uS + 2314000 * uP^2 * uR
      + 2313968 * uP^2 + 851968 * uP * uS^3 * uR + 851968 * uP * uS^3
      + 2695424 * uP * uS^2 * uR + 2695424 * uP * uS^2 + 2836304 * uP * uS * uR
      + 2836168 * uP * uS + 992864 * uP * uR + 992728 * uP
      + 147456 * uS^3 * uR + 147456 * uS^3 + 476672 * uS^2 * uR
      + 476672 * uS^2 + 511584 * uS * uR + 511432 * uS
      + 182392 * uR + 182224 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uS,uR]
      ring
    change 0≤scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 7
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 8 =
      512 * uP^8 * uS^3 * uR + 512 * uP^8 * uS^3 + 1536 * uP^8 * uS^2 * uR
      + 1536 * uP^8 * uS^2 + 1536 * uP^8 * uS * uR + 1536 * uP^8 * uS
      + 512 * uP^8 * uR + 512 * uP^8 + 7680 * uP^7 * uS^3 * uR
      + 7936 * uP^7 * uS^3 + 23040 * uP^7 * uS^2 * uR + 23808 * uP^7 * uS^2
      + 23040 * uP^7 * uS * uR + 23808 * uP^7 * uS + 7680 * uP^7 * uR
      + 7936 * uP^7 + 50176 * uP^6 * uS^3 * uR + 54016 * uP^6 * uS^3
      + 150272 * uP^6 * uS^2 * uR + 161792 * uP^6 * uS^2 + 150016 * uP^6 * uS * uR
      + 161536 * uP^6 * uS + 49920 * uP^6 * uR + 53760 * uP^6
      + 186368 * uP^5 * uS^3 * uR + 210944 * uP^5 * uS^3 + 556480 * uP^5 * uS^2 * uR
      + 630272 * uP^5 * uS^2 + 553856 * uP^5 * uS * uR + 627712 * uP^5 * uS
      + 183744 * uP^5 * uR + 208384 * uP^5 + 430080 * uP^4 * uS^3 * uR
      + 517120 * uP^4 * uS^3 + 1279296 * uP^4 * uS^2 * uR + 1541120 * uP^4 * uS^2
      + 1268352 * uP^4 * uS * uR + 1530880 * uP^4 * uS + 419136 * uP^4 * uR
      + 506880 * uP^4 + 630784 * uP^3 * uS^3 * uR + 815104 * uP^3 * uS^3
      + 1868800 * uP^3 * uS^2 * uR + 2424832 * uP^3 * uS^2 + 1845216 * uP^3 * uS * uR
      + 2404320 * uP^3 * uS + 607200 * uP^3 * uR + 794592 * uP^3
      + 573440 * uP^2 * uS^3 * uR + 806912 * uP^2 * uS^3 + 1693184 * uP^2 * uS^2 * uR
      + 2400256 * uP^2 * uS^2 + 1665840 * uP^2 * uS * uR + 2379640 * uP^2 * uS
      + 546096 * uP^2 * uR + 786296 * uP^2 + 294912 * uP * uS^3 * uR
      + 458752 * uP * uS^3 + 869376 * uP * uS^2 * uR + 1368064 * uP * uS^2
      + 853552 * uP * uS * uR + 1359704 * uP * uS + 279088 * uP * uR
      + 450392 * uP + 65536 * uS^3 * uR + 114688 * uS^3
      + 193536 * uS^2 * uR + 344064 * uS^2 + 190112 * uS * uR
      + 344016 * uS + 62104 * uR + 114648 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uS,uR]
      ring
    change 0≤scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 8
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 9 =
      512 * uP^7 * uS^3 * uR + 256 * uP^7 * uS^3 + 1536 * uP^7 * uS^2 * uR
      + 768 * uP^7 * uS^2 + 1536 * uP^7 * uS * uR + 768 * uP^7 * uS
      + 512 * uP^7 * uR + 256 * uP^7 + 7168 * uP^6 * uS^3 * uR
      + 3328 * uP^6 * uS^3 + 21760 * uP^6 * uS^2 * uR + 10240 * uP^6 * uS^2
      + 22016 * uP^6 * uS * uR + 10496 * uP^6 * uS + 7424 * uP^6 * uR
      + 3584 * uP^6 + 43008 * uP^5 * uS^3 * uR + 18432 * uP^5 * uS^3
      + 131776 * uP^5 * uS^2 * uR + 57984 * uP^5 * uS^2 + 134528 * uP^5 * uS * uR
      + 60672 * uP^5 * uS + 45760 * uP^5 * uR + 21120 * uP^5
      + 143360 * uP^4 * uS^3 * uR + 56320 * uP^4 * uS^3 + 442304 * uP^4 * uS^2 * uR
      + 180480 * uP^4 * uS^2 + 454528 * uP^4 * uS * uR + 192000 * uP^4 * uS
      + 155584 * uP^4 * uR + 67840 * uP^4 + 286720 * uP^3 * uS^3 * uR
      + 102400 * uP^3 * uS^3 + 888832 * uP^3 * uS^2 * uR + 332800 * uP^3 * uS^2
      + 917536 * uP^3 * uS * uR + 358432 * uP^3 * uS + 315424 * uP^3 * uR
      + 128032 * uP^3 + 344064 * uP^2 * uS^3 * uR + 110592 * uP^2 * uS^3
      + 1069568 * uP^2 * uS^2 * uR + 362496 * uP^2 * uS^2 + 1107152 * uP^2 * uS * uR
      + 393368 * uP^2 * uS + 381648 * uP^2 * uR + 141464 * uP^2
      + 229376 * uP * uS^3 * uR + 65536 * uP * uS^3 + 713728 * uP * uS^2 * uR
      + 215040 * uP * uS^2 + 739792 * uP * uS * uR + 233704 * uP * uS
      + 255440 * uP * uR + 84200 * uP + 65536 * uS^3 * uR
      + 16384 * uS^3 + 203776 * uS^2 * uR + 53248 * uS^2
      + 211296 * uS * uR + 57456 * uS + 73064 * uR
      + 20584 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uS,uR]
      ring
    change 0≤scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 9
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 10 =
      512 * uP^8 * uS^3 * uR + 512 * uP^8 * uS^3 + 1536 * uP^8 * uS^2 * uR
      + 1536 * uP^8 * uS^2 + 1536 * uP^8 * uS * uR + 1536 * uP^8 * uS
      + 512 * uP^8 * uR + 512 * uP^8 + 7680 * uP^7 * uS^3 * uR
      + 7936 * uP^7 * uS^3 + 23040 * uP^7 * uS^2 * uR + 23808 * uP^7 * uS^2
      + 23040 * uP^7 * uS * uR + 23808 * uP^7 * uS + 7680 * uP^7 * uR
      + 7936 * uP^7 + 50176 * uP^6 * uS^3 * uR + 54016 * uP^6 * uS^3
      + 150272 * uP^6 * uS^2 * uR + 161792 * uP^6 * uS^2 + 150016 * uP^6 * uS * uR
      + 161536 * uP^6 * uS + 49920 * uP^6 * uR + 53760 * uP^6
      + 186368 * uP^5 * uS^3 * uR + 210944 * uP^5 * uS^3 + 555968 * uP^5 * uS^2 * uR
      + 630016 * uP^5 * uS^2 + 552832 * uP^5 * uS * uR + 627200 * uP^5 * uS
      + 183232 * uP^5 * uR + 208128 * uP^5 + 430080 * uP^4 * uS^3 * uR
      + 517120 * uP^4 * uS^3 + 1274176 * uP^4 * uS^2 * uR + 1538560 * uP^4 * uS^2
      + 1258112 * uP^4 * uS * uR + 1525760 * uP^4 * uS + 414016 * uP^4 * uR
      + 504320 * uP^4 + 630784 * uP^3 * uS^3 * uR + 815104 * uP^3 * uS^3
      + 1848320 * uP^3 * uS^2 * uR + 2414592 * uP^3 * uS^2 + 1804256 * uP^3 * uS * uR
      + 2383904 * uP^3 * uS + 586720 * uP^3 * uR + 784416 * uP^3
      + 573440 * uP^2 * uS^3 * uR + 806912 * uP^2 * uS^3 + 1652224 * uP^2 * uS^2 * uR
      + 2379776 * uP^2 * uS^2 + 1583920 * uP^2 * uS * uR + 2339000 * uP^2 * uS
      + 505136 * uP^2 * uR + 766136 * uP^2 + 294912 * uP * uS^3 * uR
      + 458752 * uP * uS^3 + 828416 * uP * uS^2 * uR + 1347584 * uP * uS^2
      + 771632 * uP * uS * uR + 1319256 * uP * uS + 238128 * uP * uR
      + 430424 * uP + 65536 * uS^3 * uR + 114688 * uS^3
      + 177152 * uS^2 * uR + 335872 * uS^2 + 157344 * uS * uR
      + 327888 * uS + 45720 * uR + 106704 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uS,uR]
      ring
    change 0≤scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 10
    rw [expansion]
    positivity
  · have expansion : scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 11 =
      512 * uP^8 * uS^3 * uR + 512 * uP^8 * uS^3 + 1536 * uP^8 * uS^2 * uR
      + 1536 * uP^8 * uS^2 + 1536 * uP^8 * uS * uR + 1536 * uP^8 * uS
      + 512 * uP^8 * uR + 512 * uP^8 + 8704 * uP^7 * uS^3 * uR
      + 8448 * uP^7 * uS^3 + 26112 * uP^7 * uS^2 * uR + 25344 * uP^7 * uS^2
      + 26112 * uP^7 * uS * uR + 25344 * uP^7 * uS + 8704 * uP^7 * uR
      + 8448 * uP^7 + 64512 * uP^6 * uS^3 * uR + 60672 * uP^6 * uS^3
      + 193792 * uP^6 * uS^2 * uR + 182272 * uP^6 * uS^2 + 194048 * uP^6 * uS * uR
      + 182528 * uP^6 * uS + 64768 * uP^6 * uR + 60928 * uP^6
      + 272384 * uP^5 * uS^3 * uR + 247808 * uP^5 * uS^3 + 820288 * uP^5 * uS^2 * uR
      + 746368 * uP^5 * uS^2 + 823424 * uP^5 * uS * uR + 749312 * uP^5 * uS
      + 275520 * uP^5 * uR + 250752 * uP^5 + 716800 * uP^4 * uS^3 * uR
      + 629760 * uP^4 * uS^3 + 2166464 * uP^4 * uS^2 * uR + 1903360 * uP^4 * uS^2
      + 2182528 * uP^4 * uS * uR + 1917440 * uP^4 * uS + 732864 * uP^4 * uR
      + 643840 * uP^4 + 1204224 * uP^3 * uS^3 * uR + 1019904 * uP^3 * uS^3
      + 3656704 * uP^3 * uS^2 * uR + 3095552 * uP^3 * uS^2 + 3700768 * uP^3 * uS * uR
      + 3131392 * uP^3 * uS + 1248288 * uP^3 * uR + 1055744 * uP^3
      + 1261568 * uP^2 * uS^3 * uR + 1028096 * uP^2 * uS^3 + 3852800 * uP^2 * uS^2 * uR
      + 3135488 * uP^2 * uS^2 + 3921104 * uP^2 * uS * uR + 3186696 * uP^2 * uS
      + 1329872 * uP^2 * uR + 1079304 * uP^2 + 753664 * uP * uS^3 * uR
      + 589824 * uP * uS^3 + 2317312 * uP * uS^2 * uR + 1808384 * uP * uS^2
      + 2374096 * uP * uS * uR + 1847336 * uP * uS + 810448 * uP * uR
      + 628776 * uP + 196608 * uS^3 * uR + 147456 * uS^3
      + 609280 * uS^2 * uR + 454656 * uS^2 + 629088 * uS * uR
      + 466992 * uS + 216424 * uR + 159792 := by
      dsimp [scaledGates,A,B,L,K,SU,SV,SW,uP,uS,uR]
      ring
    change 0≤scaledGates (4*p^2*h) p s (p*h+h) (8*p*(p*h+h+1)-8) (4*p^2*h+4*p*h) (8*p^2*h+8*p*h) 1 11
    rw [expansion]
    positivity

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
