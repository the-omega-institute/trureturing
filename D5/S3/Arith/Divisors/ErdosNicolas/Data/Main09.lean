/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Main09
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Main09.chunk_checked
   digest: Exact numerical and binary coverage certificate for the main exponent box. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainSupport
import D5.S3.Arith.Divisors.ErdosNicolas.Data.RankReadouts01

/-! Opaque numerical subproofs bound temporary kernel reduction memory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.Main09

private abbrev C (lo hi : Fin 7 → ℕ) (tree : MainTree) : Prop :=
  checkExponentBoxTree mainScale boxPrimes lo hi tree = true

/-- Lower exponents at this subtree root. -/
def lo : Fin 7 → ℕ := ![9, 2, 0, 0, 0, 0, 0]

/-- Upper exponents at the same root. -/
def hi : Fin 7 → ℕ := ![17, 7, 1, 0, 1, 1, 1]

private def n2987 : MainTree := .leaf (mainGapLeaf ![17, 3, 0, 0, 0, 0, 0])
private def n2988 : MainTree := .leaf (mainGapLeaf ![17, 3, 0, 0, 0, 0, 1])
private def n2986 : MainTree := .split 6 0 n2987 n2988
private def n2990 : MainTree := .leaf (mainGapLeaf ![17, 3, 0, 0, 0, 1, 0])
private def n2991 : MainTree := .leaf (mainGapLeaf ![17, 3, 0, 0, 0, 1, 1])
private def n2989 : MainTree := .split 6 0 n2990 n2991
private def n2985 : MainTree := .split 5 0 n2986 n2989
private def n2994 : MainTree := .leaf (mainGapLeaf ![17, 3, 0, 0, 1, 0, 0])
private def n2995 : MainTree := .leaf (mainGapLeaf ![17, 3, 0, 0, 1, 0, 1])
private def n2993 : MainTree := .split 6 0 n2994 n2995
private def n2997 : MainTree := .leaf (mainGapLeaf ![17, 3, 0, 0, 1, 1, 0])
private def n2998 : MainTree := .leaf (mainGapLeaf ![17, 3, 0, 0, 1, 1, 1])
private def n2996 : MainTree := .split 6 0 n2997 n2998
private def n2992 : MainTree := .split 5 0 n2993 n2996
private def n2984 : MainTree := .split 4 0 n2985 n2992
private def n3002 : MainTree := .leaf (mainGapLeaf ![17, 3, 1, 0, 0, 0, 0])
private def n3003 : MainTree := .leaf (mainGapLeaf ![17, 3, 1, 0, 0, 0, 1])
private def n3001 : MainTree := .split 6 0 n3002 n3003
private def n3005 : MainTree := .leaf (mainGapLeaf ![17, 3, 1, 0, 0, 1, 0])
private def n3006 : MainTree := .leaf (mainGapLeaf ![17, 3, 1, 0, 0, 1, 1])
private def n3004 : MainTree := .split 6 0 n3005 n3006
private def n3000 : MainTree := .split 5 0 n3001 n3004
private def n3009 : MainTree := .leaf (mainGapLeaf ![17, 3, 1, 0, 1, 0, 0])
private def n3010 : MainTree := .leaf (mainGapLeaf ![17, 3, 1, 0, 1, 0, 1])
private def n3008 : MainTree := .split 6 0 n3009 n3010
private def n3012 : MainTree := .leaf (mainGapLeaf ![17, 3, 1, 0, 1, 1, 0])
private def n3013 : MainTree := .leaf (mainGapLeaf ![17, 3, 1, 0, 1, 1, 1])
private def n3011 : MainTree := .split 6 0 n3012 n3013
private def n3007 : MainTree := .split 5 0 n3008 n3011
private def n2999 : MainTree := .split 4 0 n3000 n3007
private def n2983 : MainTree := .split 2 0 n2984 n2999
private def n3017 : MainTree := .leaf (mainGapLeaf ![17, 7, 0, 0, 0, 0, 1])
private def n3018 : MainTree := .leaf (mainGapLeaf ![17, 7, 0, 0, 0, 1, 1])
private def n3016 : MainTree := .split 5 0 n3017 n3018
private def n3020 : MainTree := .leaf (mainGapLeaf ![17, 7, 0, 0, 1, 0, 1])
private def n3021 : MainTree := .leaf (mainGapLeaf ![17, 7, 0, 0, 1, 1, 1])
private def n3019 : MainTree := .split 5 0 n3020 n3021
private def n3015 : MainTree := .split 4 0 n3016 n3019
private def n3025 : MainTree := .leaf (mainGapLeaf ![17, 7, 1, 0, 0, 0, 0])
private def n3026 : MainTree := .leaf (mainGapLeaf ![17, 7, 1, 0, 0, 0, 1])
private def n3024 : MainTree := .split 6 0 n3025 n3026
private def n3028 : MainTree := .leaf (mainGapLeaf ![17, 7, 1, 0, 0, 1, 0])
private def n3029 : MainTree := .leaf (mainGapLeaf ![17, 7, 1, 0, 0, 1, 1])
private def n3027 : MainTree := .split 6 0 n3028 n3029
private def n3023 : MainTree := .split 5 0 n3024 n3027
private def n3032 : MainTree := .leaf (mainGapLeaf ![17, 7, 1, 0, 1, 0, 0])
private def n3033 : MainTree := .leaf (mainGapLeaf ![17, 7, 1, 0, 1, 0, 1])
private def n3031 : MainTree := .split 6 0 n3032 n3033
private def n3034 : MainTree :=
  .leaf (.rankIndexed 1 2304 RankReadouts01.rankReadout3034)
private def n3030 : MainTree := .split 5 0 n3031 n3034
private def n3022 : MainTree := .split 4 0 n3023 n3030
private def n3014 : MainTree := .split 2 0 n3015 n3022
private def n2982 : MainTree := .split 1 3 n2983 n3014

private theorem c2985 : C ![9, 2, 0, 0, 0, 0, 0] ![17, 3, 0, 0, 0, 1, 1] n2985 := by
  decide +kernel

private theorem c2992 : C ![9, 2, 0, 0, 1, 0, 0] ![17, 3, 0, 0, 1, 1, 1] n2992 := by
  decide +kernel

private theorem c2984 : C ![9, 2, 0, 0, 0, 0, 0] ![17, 3, 0, 0, 1, 1, 1] n2984 := by
  exact checkExponentBoxTree_join c2985 c2992 (by decide +kernel)

private theorem c3000 : C ![9, 2, 1, 0, 0, 0, 0] ![17, 3, 1, 0, 0, 1, 1] n3000 := by
  decide +kernel

private theorem c3008 : C ![9, 2, 1, 0, 1, 0, 0] ![17, 3, 1, 0, 1, 0, 1] n3008 := by
  decide +kernel

private theorem c3012 : C ![9, 2, 1, 0, 1, 1, 0] ![17, 3, 1, 0, 1, 1, 0] n3012 := by
  decide +kernel

private theorem c3013 : C ![9, 2, 1, 0, 1, 1, 1] ![17, 3, 1, 0, 1, 1, 1] n3013 := by
  decide +kernel

private theorem c3011 : C ![9, 2, 1, 0, 1, 1, 0] ![17, 3, 1, 0, 1, 1, 1] n3011 := by
  exact checkExponentBoxTree_join c3012 c3013 (by decide +kernel)

private theorem c3007 : C ![9, 2, 1, 0, 1, 0, 0] ![17, 3, 1, 0, 1, 1, 1] n3007 := by
  exact checkExponentBoxTree_join c3008 c3011 (by decide +kernel)

private theorem c2999 : C ![9, 2, 1, 0, 0, 0, 0] ![17, 3, 1, 0, 1, 1, 1] n2999 := by
  exact checkExponentBoxTree_join c3000 c3007 (by decide +kernel)

private theorem c2983 : C ![9, 2, 0, 0, 0, 0, 0] ![17, 3, 1, 0, 1, 1, 1] n2983 := by
  exact checkExponentBoxTree_join c2984 c2999 (by decide +kernel)

private theorem c3016 : C ![9, 4, 0, 0, 0, 0, 0] ![17, 7, 0, 0, 0, 1, 1] n3016 := by
  decide +kernel

private theorem c3020 : C ![9, 4, 0, 0, 1, 0, 0] ![17, 7, 0, 0, 1, 0, 1] n3020 := by
  decide +kernel

private theorem c3021 : C ![9, 4, 0, 0, 1, 1, 0] ![17, 7, 0, 0, 1, 1, 1] n3021 := by
  decide +kernel

private theorem c3019 : C ![9, 4, 0, 0, 1, 0, 0] ![17, 7, 0, 0, 1, 1, 1] n3019 := by
  exact checkExponentBoxTree_join c3020 c3021 (by decide +kernel)

private theorem c3015 : C ![9, 4, 0, 0, 0, 0, 0] ![17, 7, 0, 0, 1, 1, 1] n3015 := by
  exact checkExponentBoxTree_join c3016 c3019 (by decide +kernel)

private theorem c3024 : C ![9, 4, 1, 0, 0, 0, 0] ![17, 7, 1, 0, 0, 0, 1] n3024 := by
  decide +kernel

private theorem c3028 : C ![9, 4, 1, 0, 0, 1, 0] ![17, 7, 1, 0, 0, 1, 0] n3028 := by
  decide +kernel

private theorem c3029 : C ![9, 4, 1, 0, 0, 1, 1] ![17, 7, 1, 0, 0, 1, 1] n3029 := by
  decide +kernel

private theorem c3027 : C ![9, 4, 1, 0, 0, 1, 0] ![17, 7, 1, 0, 0, 1, 1] n3027 := by
  exact checkExponentBoxTree_join c3028 c3029 (by decide +kernel)

private theorem c3023 : C ![9, 4, 1, 0, 0, 0, 0] ![17, 7, 1, 0, 0, 1, 1] n3023 := by
  exact checkExponentBoxTree_join c3024 c3027 (by decide +kernel)

private theorem c3032 : C ![9, 4, 1, 0, 1, 0, 0] ![17, 7, 1, 0, 1, 0, 0] n3032 := by
  decide +kernel

private theorem c3033 : C ![9, 4, 1, 0, 1, 0, 1] ![17, 7, 1, 0, 1, 0, 1] n3033 := by
  decide +kernel

private theorem c3031 : C ![9, 4, 1, 0, 1, 0, 0] ![17, 7, 1, 0, 1, 0, 1] n3031 := by
  exact checkExponentBoxTree_join c3032 c3033 (by decide +kernel)

private theorem c3034 : C ![9, 4, 1, 0, 1, 1, 0] ![17, 7, 1, 0, 1, 1, 1] n3034 := by
  decide +kernel

private theorem c3030 : C ![9, 4, 1, 0, 1, 0, 0] ![17, 7, 1, 0, 1, 1, 1] n3030 := by
  exact checkExponentBoxTree_join c3031 c3034 (by decide +kernel)

private theorem c3022 : C ![9, 4, 1, 0, 0, 0, 0] ![17, 7, 1, 0, 1, 1, 1] n3022 := by
  exact checkExponentBoxTree_join c3023 c3030 (by decide +kernel)

private theorem c3014 : C ![9, 4, 0, 0, 0, 0, 0] ![17, 7, 1, 0, 1, 1, 1] n3014 := by
  exact checkExponentBoxTree_join c3015 c3022 (by decide +kernel)

private theorem c2982 : C ![9, 2, 0, 0, 0, 0, 0] ![17, 7, 1, 0, 1, 1, 1] n2982 := by
  exact checkExponentBoxTree_join c2983 c3014 (by decide +kernel)

/-- The complete binary certificate at this subtree root. -/
def certificate : MainTree := n2982

theorem chunk_checked :
    checkExponentBoxTree mainScale boxPrimes lo hi certificate = true := c2982

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.Main09
