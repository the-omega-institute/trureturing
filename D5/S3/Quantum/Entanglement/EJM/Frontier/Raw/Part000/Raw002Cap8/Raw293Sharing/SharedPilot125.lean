/- Prepared exact same-goal candidate; no elaboration or kernel/resource verdict.
   Target: Accepted 16 329851 <15878>, the original 125 actual contexts.
   It is Raw293's [3,2,3] descendant, not the full Raw293 or any Response.
   All 31 splits, 57 bounds and 37 original symmetry/partial tests remain.
   The full original prefix cache is checked once at the root. Every one of
   124 child caches follows from its actual parent's full equality and a
   32-row step equality. Local update keys retain state(row index and both
   actions), all four MirrorRow fields, local coordinate and outcome.
   Native extraction and static checks are not acceptance assumptions. -/
import D5.S3.Quantum.Entanglement.EJM.Tail442V2.Helper
import D5.S3.Quantum.Entanglement.EJM.CanonicalCacheStateEqualityCandidate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.Raw002Cap8.Raw293Sharing.SharedPilot125
open EJMCacheState (Cache CachedLocal triangleStep singletonStep step lower)
open EJMLocalCacheData (triangleIncidence singletonIncidence)
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial Accepted)
open Tail442V2.Helper (FullLocalFields cachedLocal_eq_of_fields cache_eq_of_checked)
open D5.S0.Certificates.FiniteSymmetryDAGNode (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
  (check checkSplit checked_split_node)
open EJMPartialBoundData (scale)

theorem step_eq_of_local_eq (cache nextCache : Cache) (g : Fin 20) (a : Fin 4)
    (triangle : ∀ k : Fin 16,
      (match triangleIncidence g k with
       | none => cache.triangle k
       | some i => triangleStep (cache.triangle k) i a) = nextCache.triangle k)
    (singleton : ∀ k : Fin 16,
      (match singletonIncidence g k with
       | none => cache.singleton k
       | some i => singletonStep (cache.singleton k) i a) = nextCache.singleton k) :
    step cache g a = nextCache := by
  cases nextCache with
  | mk triangles singletons =>
    unfold step
    exact congrArg₂ Cache.mk (funext triangle) (funext singleton)


abbrev ReplayNode :=
  Node EJMOriginalGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut

private def isBound : ReplayNode → Bool
  | .bound => true
  | _ => false

private theorem bound_of_isBound (node : ReplayNode)
    (receipt : isBound node = true) : node = .bound := by
  cases node with
  | bound => rfl
  | symmetry s => simp only [isBound, Bool.false_eq_true] at receipt
  | split i children => simp only [isBound, Bool.false_eq_true] at receipt

private def checkSymmetry (node : ReplayNode) (cut : EJMGlobalScoreSymmetry.Cut) : Bool :=
  match node with
  | .symmetry actual => decide (actual = cut)
  | _ => false

private theorem symmetry_of_checked (node : ReplayNode) (cut : EJMGlobalScoreSymmetry.Cut)
    (receipt : checkSymmetry node cut = true) : node = .symmetry cut := by
  cases node with
  | bound => simp only [checkSymmetry, Bool.false_eq_true] at receipt
  | symmetry actual => exact congrArg Node.symmetry (of_decide_eq_true receipt)
  | split i children => simp only [checkSymmetry, Bool.false_eq_true] at receipt

/-- Original bound check with an earned complete cache equality. -/
theorem accepted_bound_of_cache (depth code fuel : ℕ)
    (index : Fin EJMOriginalGlobalDAGData.Size) (cache : Cache)
    (fuelEquation : 21 - depth = fuel + 1)
    (cacheEquation : prefixCache depth code = cache)
    (node : EJMOriginalGlobalDAGData.nodes (fuel + 1) index = .bound)
    (bound : scale ≤ lower cache) : Accepted depth code index := by
  unfold Accepted
  rw [fuelEquation, cacheEquation]
  simpa only [check, node] using (decide_eq_true bound)

/-- The symmetry premise checks the entire original partial assignment. -/
theorem accepted_symmetry_of_cache (depth code fuel : ℕ)
    (index : Fin EJMOriginalGlobalDAGData.Size) (cache : Cache)
    (cut : EJMGlobalScoreSymmetry.Cut)
    (fuelEquation : 21 - depth = fuel + 1)
    (cacheEquation : prefixCache depth code = cache)
    (node : EJMOriginalGlobalDAGData.nodes (fuel + 1) index = .symmetry cut)
    (dominates : EJMGlobalScoreSymmetry.dominates cut (prefixPartial depth code) = true) :
    Accepted depth code index := by
  unfold Accepted
  rw [fuelEquation, cacheEquation]
  simpa only [check, node] using dominates

def triangleLocal000 : CachedLocal 41294 :=
  ⟨(25, (7, 5)), ⟨6643750, (-3707226961347000), 0x0, 0x0⟩⟩

def triangleLocal001 : CachedLocal 41294 :=
  ⟨(35, (1, 4)), ⟨6721875, (-5172936963846015), 0x0, 0x0⟩⟩

def triangleLocal002 : CachedLocal 41294 :=
  ⟨(35, (7, 5)), ⟨6721875, (-5172936963846015), 0x0, 0x0⟩⟩

def triangleLocal003 : CachedLocal 41294 :=
  ⟨(46, (1, 4)), ⟨6800000, (-5964221990099100), 0x0, 0x0⟩⟩

def triangleLocal004 : CachedLocal 41294 :=
  ⟨(46, (7, 5)), ⟨6800000, (-5964221990099100), 0x0, 0x0⟩⟩

def triangleLocal005 : CachedLocal 41294 :=
  ⟨(46, (10, 5)), ⟨6800000, (-5964221990099100), 0x0, 0x0⟩⟩

def triangleLocal006 : CachedLocal 41294 :=
  ⟨(49, (1, 2)), ⟨5237500, (-4996023802015155), 0x0, 0x0⟩⟩

def triangleLocal007 : CachedLocal 41294 :=
  ⟨(49, (7, 3)), ⟨5237500, (-4996023802015155), 0x0, 0x0⟩⟩

def triangleLocal008 : CachedLocal 41294 :=
  ⟨(72, (10, 5)), ⟨6815625, (-5753629859726385), 0x0, 0x0⟩⟩

def triangleLocal009 : CachedLocal 41294 :=
  ⟨(88, (7, 5)), ⟨6831250, (-6533737750016295), 0x0, 0x0⟩⟩

def triangleLocal010 : CachedLocal 41294 :=
  ⟨(102, (7, 5)), ⟨6909375, (-5609974939001160), 0x0, 0x0⟩⟩

def triangleLocal011 : CachedLocal 41294 :=
  ⟨(109, (1, 4)), ⟨6722500, (-5674947107240775), 0x0, 0x0⟩⟩

def triangleLocal012 : CachedLocal 41294 :=
  ⟨(109, (7, 5)), ⟨6722500, (-5674947107240775), 0x0, 0x0⟩⟩

def triangleLocal013 : CachedLocal 41294 :=
  ⟨(112, (0, 4)), ⟨6800625, (-3925354327648845), 0x0, 0x0⟩⟩

def triangleLocal014 : CachedLocal 41294 :=
  ⟨(112, (6, 5)), ⟨6800625, (-3925354327648845), 0x0, 0x0⟩⟩

def triangleLocal015 : CachedLocal 41294 :=
  ⟨(115, (1, 2)), ⟨5238125, (-4165265902980000), 0x0, 0x0⟩⟩

def triangleLocal016 : CachedLocal 41294 :=
  ⟨(115, (7, 3)), ⟨5238125, (-4165265902980000), 0x0, 0x0⟩⟩

def triangleLocal017 : CachedLocal 41294 :=
  ⟨(122, (4, 4)), ⟨6660000, (-5791210381386885), 0x0, 0x0⟩⟩

def triangleLocal018 : CachedLocal 41294 :=
  ⟨(143, (7, 5)), ⟨6675625, (-6950356015461495), 0x0, 0x0⟩⟩

def triangleLocal019 : CachedLocal 41294 :=
  ⟨(146, (4, 2)), ⟨5113125, (-4243892560337430), 0x0, 0x0⟩⟩

def triangleLocal020 : CachedLocal 41294 :=
  ⟨(149, (4, 7)), ⟨2456875, (-7445148830257320), 0x0, 0x0⟩⟩

def triangleLocal021 : CachedLocal 41294 :=
  ⟨(149, (10, 7)), ⟨2456875, (-7445148830257320), 0x0, 0x0⟩⟩

def triangleLocal022 : CachedLocal 41294 :=
  ⟨(155, (7, 5)), ⟨6753750, (-6866201123129985), 0x0, 0x0⟩⟩

def triangleLocal023 : CachedLocal 41294 :=
  ⟨(163, (6, 5)), ⟨6831875, (-6357813247351020), 0x0, 0x0⟩⟩

def triangleLocal024 : CachedLocal 41294 :=
  ⟨(167, (6, 5)), ⟨7222500, (-5936530980842280), 0x0, 0x0⟩⟩

def triangleLocal025 : CachedLocal 41294 :=
  ⟨(176, (1, 0)), ⟨3210000, (-5645662019500230), 0x0, 0x0⟩⟩

def triangleLocal026 : CachedLocal 41294 :=
  ⟨(176, (7, 1)), ⟨3210000, (-5645662019500230), 0x0, 0x0⟩⟩

def triangleLocal027 : CachedLocal 41294 :=
  ⟨(180, (0, 4)), ⟨6413125, (-4604128437162345), 0x0, 0x0⟩⟩

def triangleLocal028 : CachedLocal 41294 :=
  ⟨(180, (6, 5)), ⟨6413125, (-4604128437162345), 0x0, 0x0⟩⟩

def triangleLocal029 : CachedLocal 41294 :=
  ⟨(182, (1, 0)), ⟨3288125, (-4086178612945065), 0x0, 0x0⟩⟩

def triangleLocal030 : CachedLocal 41294 :=
  ⟨(182, (7, 1)), ⟨3288125, (-4086178612945065), 0x0, 0x0⟩⟩

def triangleLocal031 : CachedLocal 41294 :=
  ⟨(194, (7, 4)), ⟨6350625, (-5476039009315875), 0x0, 0x0⟩⟩

def triangleLocal032 : CachedLocal 41294 :=
  ⟨(209, (7, 4)), ⟨6428750, (-4809825729568860), 0x0, 0x0⟩⟩

def triangleLocal033 : CachedLocal 41294 :=
  ⟨(225, (7, 4)), ⟨6506875, (-4469343471237645), 0x0, 0x0⟩⟩

def triangleLocal034 : CachedLocal 41294 :=
  ⟨(245, (7, 1)), ⟨3256875, (-5894215444816335), 0x0, 0x0⟩⟩

def triangleLocal035 : CachedLocal 41294 :=
  ⟨(252, (7, 1)), ⟨3335000, (-5231125974747855), 0x0, 0x0⟩⟩

def triangleLocal036 : CachedLocal 41294 :=
  ⟨(256, (7, 1)), ⟨3413125, (-6041449658158005), 0x0, 0x0⟩⟩

def triangleLocal037 : CachedLocal 41294 :=
  ⟨(381, (6, 1)), ⟨784400, (3480835429896825), 0x0, 0x0⟩⟩

def triangleLocal038 : CachedLocal 41294 :=
  ⟨(428, (3, 10)), ⟨6425025, (3555822618847590), 0x0, 0x0⟩⟩

def triangleLocal039 : CachedLocal 41294 :=
  ⟨(470, (1, 1)), ⟨475025, (3379239389722560), 0x0, 0x0⟩⟩

def triangleLocal040 : CachedLocal 41294 :=
  ⟨(486, (1, 1)), ⟨553150, (3753803428248510), 0x0, 0x0⟩⟩

def triangleLocal041 : CachedLocal 41294 :=
  ⟨(501, (1, 1)), ⟨631275, (3414124955527650), 0x0, 0x0⟩⟩

def triangleLocal042 : CachedLocal 41294 :=
  ⟨(612, (7, 1)), ⟨863150, (5715137198300985), 0x0, 0x0⟩⟩

def triangleLocal043 : CachedLocal 41294 :=
  ⟨(616, (6, 1)), ⟨941275, (5067799146593820), 0x0, 0x0⟩⟩

def triangleLocal044 : CachedLocal 41294 :=
  ⟨(620, (6, 1)), ⟨1331900, (4223182285130445), 0x0, 0x0⟩⟩

def triangleLocal045 : CachedLocal 41294 :=
  ⟨(663, (10, 11)), ⟨6753775, (3631121719909320), 0x0, 0x0⟩⟩

def triangleLocal046 : CachedLocal 41294 :=
  ⟨(687, (6, 1)), ⟨553775, (4592661951515820), 0x0, 0x0⟩⟩

def triangleLocal047 : CachedLocal 41294 :=
  ⟨(691, (6, 1)), ⟨944400, (5921283230770635), 0x0, 0x0⟩⟩

def triangleLocal048 : CachedLocal 41294 :=
  ⟨(695, (6, 1)), ⟨1335025, (4088170374304380), 0x0, 0x0⟩⟩

def triangleLocal049 : CachedLocal 41294 :=
  ⟨(699, (6, 0)), ⟨631900, (4630480416300375), 0x0, 0x0⟩⟩

def triangleLocal050 : CachedLocal 41294 :=
  ⟨(702, (6, 0)), ⟨1022525, (4144044755437860), 0x0, 0x0⟩⟩

def triangleLocal051 : CachedLocal 41294 :=
  ⟨(706, (6, 0)), ⟨1413150, (5638227898742985), 0x0, 0x0⟩⟩

def triangleLocal052 : CachedLocal 41294 :=
  ⟨(897, (4, 15)), ⟨4866900, (5085030545612745), 0x0, 0x0⟩⟩

def triangleLocal053 : CachedLocal 41294 :=
  ⟨(897, (10, 15)), ⟨4866900, (5085030545612745), 0x0, 0x0⟩⟩

def triangleLocal054 : CachedLocal 41294 :=
  ⟨(1088, (6, 7)), ⟨1428900, (5624801353729740), 0x0, 0x0⟩⟩

def triangleLocal055 : CachedLocal 41294 :=
  ⟨(1168, (4, 14)), ⟨4898275, (5192168068937850), 0x0, 0x0⟩⟩

def triangleLocal056 : CachedLocal 41294 :=
  ⟨(1168, (10, 14)), ⟨4898275, (5192168068937850), 0x0, 0x0⟩⟩

def triangleLocal057 : CachedLocal 41294 :=
  ⟨(1313, (6, 5)), ⟨6800005, (3900892882899285), 0x0, 0x0⟩⟩

def triangleLocal058 : CachedLocal 41294 :=
  ⟨(1393, (6, 4)), ⟨6334380, (5665451714120835), 0x0, 0x0⟩⟩

def triangleLocal059 : CachedLocal 41294 :=
  ⟨(1431, (6, 1)), ⟨3365630, (5260595146463475), 0x0, 0x0⟩⟩

def triangleLocal060 : CachedLocal 41294 :=
  ⟨(1595, (4, 7)), ⟨2456880, (1712390054567010), 0x0, 0x0⟩⟩

def triangleLocal061 : CachedLocal 41294 :=
  ⟨(1595, (10, 7)), ⟨2456880, (1712390054567010), 0x0, 0x0⟩⟩

def triangleLocal062 : CachedLocal 41294 :=
  ⟨(1944, (4, 13)), ⟨4866880, (5828317818760710), 0x0, 0x0⟩⟩

def triangleLocal063 : CachedLocal 41294 :=
  ⟨(1944, (10, 13)), ⟨4866880, (5828317818760710), 0x0, 0x0⟩⟩

def triangleLocal064 : CachedLocal 41294 :=
  ⟨(2024, (4, 12)), ⟨4898130, (4748990360422035), 0x0, 0x0⟩⟩

def triangleLocal065 : CachedLocal 41294 :=
  ⟨(2024, (10, 12)), ⟨4898130, (4748990360422035), 0x0, 0x0⟩⟩

def triangleLocal066 : CachedLocal 41294 :=
  ⟨(2281, (0, 7)), ⟨2053880, (5055044862701925), 0x0, 0x0⟩⟩

def triangleLocal067 : CachedLocal 41294 :=
  ⟨(2406, (4, 13)), ⟨4851380, (6133915405678515), 0x0, 0x0⟩⟩

def triangleLocal068 : CachedLocal 41294 :=
  ⟨(2406, (10, 13)), ⟨4851380, (6133915405678515), 0x0, 0x0⟩⟩

def triangleLocal069 : CachedLocal 41294 :=
  ⟨(2866, (0, 12)), ⟨4104630, (4507514612828955), 0x0, 0x0⟩⟩

def triangleLocal070 : CachedLocal 41294 :=
  ⟨(2866, (6, 12)), ⟨4104630, (4507514612828955), 0x0, 0x0⟩⟩

def triangleLocal071 : CachedLocal 41294 :=
  ⟨(2999, (0, 3)), ⟨784430, (2713047281903595), 0x0, 0x0⟩⟩

def triangleLocal072 : CachedLocal 41294 :=
  ⟨(2999, (6, 3)), ⟨784430, (2713047281903595), 0x0, 0x0⟩⟩

def triangleLocal073 : CachedLocal 41294 :=
  ⟨(3149, (6, 3)), ⟨396930, (6401708006573880), 0x0, 0x0⟩⟩

def triangleLocal074 : CachedLocal 41294 :=
  ⟨(3157, (6, 2)), ⟨1178180, (6381313046358705), 0x0, 0x0⟩⟩

def triangleLocal075 : CachedLocal 41294 :=
  ⟨(3222, (5, 16)), ⟨6818805, (1890842618202720), 0x0, 0x0⟩⟩

def triangleLocal076 : CachedLocal 41294 :=
  ⟨(3268, (3, 14)), ⟨3006305, (5199041958119100), 0x0, 0x0⟩⟩

def triangleLocal077 : CachedLocal 41294 :=
  ⟨(3299, (0, 2)), ⟨790680, (1955508897500340), 0x0, 0x0⟩⟩

def triangleLocal078 : CachedLocal 41294 :=
  ⟨(3299, (6, 2)), ⟨790680, (1955508897500340), 0x0, 0x0⟩⟩

def triangleLocal079 : CachedLocal 41294 :=
  ⟨(3311, (1, 2)), ⟨868805, (481973994954270), 0x0, 0x0⟩⟩

def triangleLocal080 : CachedLocal 41294 :=
  ⟨(3311, (7, 2)), ⟨868805, (481973994954270), 0x0, 0x0⟩⟩

def triangleLocal081 : CachedLocal 41294 :=
  ⟨(3327, (7, 2)), ⟨946930, (1980856146372285), 0x0, 0x0⟩⟩

def triangleLocal082 : CachedLocal 41294 :=
  ⟨(3343, (1, 2)), ⟨1025055, (2106992624248785), 0x0, 0x0⟩⟩

def triangleLocal083 : CachedLocal 41294 :=
  ⟨(3343, (7, 2)), ⟨1025055, (2106992624248785), 0x0, 0x0⟩⟩

def triangleLocal084 : CachedLocal 41294 :=
  ⟨(3575, (4, 8)), ⟨3210055, (947539263536775), 0x0, 0x0⟩⟩

def triangleLocal085 : CachedLocal 41294 :=
  ⟨(3575, (10, 8)), ⟨3210055, (947539263536775), 0x0, 0x0⟩⟩

def triangleLocal086 : CachedLocal 41294 :=
  ⟨(3660, (4, 8)), ⟨3241305, (2762031758654805), 0x0, 0x0⟩⟩

def triangleLocal087 : CachedLocal 41294 :=
  ⟨(3660, (10, 8)), ⟨3241305, (2762031758654805), 0x0, 0x0⟩⟩

def triangleLocal088 : CachedLocal 41294 :=
  ⟨(3720, (4, 8)), ⟨3256930, (1173894411412905), 0x0, 0x0⟩⟩

def triangleLocal089 : CachedLocal 41294 :=
  ⟨(3720, (10, 8)), ⟨3256930, (1173894411412905), 0x0, 0x0⟩⟩

def triangleLocal090 : CachedLocal 41294 :=
  ⟨(3774, (7, 2)), ⟨947555, (1726075169612430), 0x0, 0x0⟩⟩

def triangleLocal091 : CachedLocal 41294 :=
  ⟨(3790, (1, 2)), ⟨1025680, (1563697081407825), 0x0, 0x0⟩⟩

def triangleLocal092 : CachedLocal 41294 :=
  ⟨(3790, (7, 2)), ⟨1025680, (1563697081407825), 0x0, 0x0⟩⟩

def triangleLocal093 : CachedLocal 41294 :=
  ⟨(3944, (10, 15)), ⟨3288805, (3689031296298075), 0x0, 0x0⟩⟩

def triangleLocal094 : CachedLocal 41294 :=
  ⟨(3955, (10, 15)), ⟨3304430, (1256447371383750), 0x0, 0x0⟩⟩

def triangleLocal095 : CachedLocal 41294 :=
  ⟨(3986, (10, 15)), ⟨3320055, (5970826325000355), 0x0, 0x0⟩⟩

def triangleLocal096 : CachedLocal 41294 :=
  ⟨(4018, (10, 15)), ⟨3335680, (3579798898035360), 0x0, 0x0⟩⟩

def triangleLocal097 : CachedLocal 41294 :=
  ⟨(4041, (4, 13)), ⟨948180, (4808755408250430), 0x0, 0x0⟩⟩

def triangleLocal098 : CachedLocal 41294 :=
  ⟨(4041, (7, 2)), ⟨948180, (4808755408250430), 0x0, 0x0⟩⟩

def triangleLocal099 : CachedLocal 41294 :=
  ⟨(4053, (1, 2)), ⟨1026305, (4437151282127655), 0x0, 0x0⟩⟩

def triangleLocal100 : CachedLocal 41294 :=
  ⟨(4053, (7, 2)), ⟨1026305, (4437151282127655), 0x0, 0x0⟩⟩

def triangleLocal101 : CachedLocal 41294 :=
  ⟨(4090, (4, 13)), ⟨979430, (3900729691354860), 0x0, 0x0⟩⟩

def triangleLocal102 : CachedLocal 41294 :=
  ⟨(4137, (4, 13)), ⟨995055, (2192232399713265), 0x0, 0x0⟩⟩

def triangleLocal103 : CachedLocal 41294 :=
  ⟨(4173, (6, 2)), ⟨948805, (1585561925437035), 0x0, 0x0⟩⟩

def triangleLocal104 : CachedLocal 41294 :=
  ⟨(4177, (0, 2)), ⟨1339430, (1676603878264770), 0x0, 0x0⟩⟩

def triangleLocal105 : CachedLocal 41294 :=
  ⟨(4177, (6, 2)), ⟨1339430, (1676603878264770), 0x0, 0x0⟩⟩

def triangleLocal106 : CachedLocal 41294 :=
  ⟨(4184, (4, 22)), ⟨7276930, (3702223384917330), 0x0, 0x0⟩⟩

def triangleLocal107 : CachedLocal 41294 :=
  ⟨(4184, (4, 23)), ⟨7276930, (3702223384917330), 0x0, 0x0⟩⟩

def triangleLocal108 : CachedLocal 41294 :=
  ⟨(4184, (10, 22)), ⟨7276930, (3702223384917330), 0x0, 0x0⟩⟩

def triangleLocal109 : CachedLocal 41294 :=
  ⟨(4184, (10, 23)), ⟨7276930, (3702223384917330), 0x0, 0x0⟩⟩

def triangleLocal110 : CachedLocal 41294 :=
  ⟨(4187, (4, 22)), ⟨7292555, (4305283856800290), 0x0, 0x0⟩⟩

def triangleLocal111 : CachedLocal 41294 :=
  ⟨(4187, (10, 22)), ⟨7292555, (4305283856800290), 0x0, 0x0⟩⟩

def triangleLocal112 : CachedLocal 41294 :=
  ⟨(4211, (4, 22)), ⟨7308180, (2465316850656660), 0x0, 0x0⟩⟩

def triangleLocal113 : CachedLocal 41294 :=
  ⟨(4211, (4, 23)), ⟨7308180, (2465316850656660), 0x0, 0x0⟩⟩

def triangleLocal114 : CachedLocal 41294 :=
  ⟨(4211, (10, 22)), ⟨7308180, (2465316850656660), 0x0, 0x0⟩⟩

def triangleLocal115 : CachedLocal 41294 :=
  ⟨(4211, (10, 23)), ⟨7308180, (2465316850656660), 0x0, 0x0⟩⟩

def triangleLocal116 : CachedLocal 41294 :=
  ⟨(4238, (4, 22)), ⟨7323805, (566066489491230), 0x0, 0x0⟩⟩

def triangleLocal117 : CachedLocal 41294 :=
  ⟨(4238, (10, 22)), ⟨7323805, (566066489491230), 0x0, 0x0⟩⟩

def triangleLocal118 : CachedLocal 41294 :=
  ⟨(4291, (5, 17)), ⟨6803930, (1116722051341260), 0x0, 0x0⟩⟩

def triangleLocal119 : CachedLocal 41294 :=
  ⟨(4324, (3, 12)), ⟨1053930, (1280890928299710), 0x0, 0x0⟩⟩

def triangleLocal120 : CachedLocal 41294 :=
  ⟨(4406, (10, 15)), ⟨3288930, (-995105458681425), 0x0, 0x0⟩⟩

def triangleLocal121 : CachedLocal 41294 :=
  ⟨(4425, (10, 15)), ⟨3320180, (4547585540172675), 0x0, 0x0⟩⟩

def triangleLocal122 : CachedLocal 41294 :=
  ⟨(4444, (10, 13)), ⟨1382680, (5554236910674270), 0x0, 0x0⟩⟩

def triangleLocal123 : CachedLocal 41294 :=
  ⟨(4445, (10, 15)), ⟨3335805, (3151146774209070), 0x0, 0x0⟩⟩

def triangleLocal124 : CachedLocal 41294 :=
  ⟨(4465, (4, 13)), ⟨979555, (14939352640485), 0x0, 0x0⟩⟩

def triangleLocal125 : CachedLocal 41294 :=
  ⟨(4492, (4, 13)), ⟨995180, (-1323763747204080), 0x0, 0x0⟩⟩

def triangleLocal126 : CachedLocal 41294 :=
  ⟨(4514, (4, 22)), ⟨7277055, (5490310412082405), 0x0, 0x0⟩⟩

def triangleLocal127 : CachedLocal 41294 :=
  ⟨(4514, (10, 22)), ⟨7277055, (5490310412082405), 0x0, 0x0⟩⟩

def triangleLocal128 : CachedLocal 41294 :=
  ⟨(4526, (4, 22)), ⟨7308305, (3311109194335215), 0x0, 0x0⟩⟩

def triangleLocal129 : CachedLocal 41294 :=
  ⟨(4526, (10, 22)), ⟨7308305, (3311109194335215), 0x0, 0x0⟩⟩

def triangleLocal130 : CachedLocal 41294 :=
  ⟨(4526, (10, 23)), ⟨7308305, (3311109194335215), 0x0, 0x0⟩⟩

def triangleLocal131 : CachedLocal 41294 :=
  ⟨(4541, (4, 22)), ⟨7323930, (2690478467773005), 0x0, 0x0⟩⟩

def triangleLocal132 : CachedLocal 41294 :=
  ⟨(4541, (10, 22)), ⟨7323930, (2690478467773005), 0x0, 0x0⟩⟩

def triangleLocal133 : CachedLocal 41294 :=
  ⟨(4546, (7, 15)), ⟨3320305, (3113335932716100), 0x0, 0x0⟩⟩

def triangleLocal134 : CachedLocal 41294 :=
  ⟨(4550, (6, 15)), ⟨3398430, (1255418541454350), 0x0, 0x0⟩⟩

def triangleLocal135 : CachedLocal 41294 :=
  ⟨(4560, (1, 13)), ⟨1057805, (7419325338778080), 0x0, 0x0⟩⟩

def triangleLocal136 : CachedLocal 41294 :=
  ⟨(4564, (6, 15)), ⟨3401555, (2437602580228725), 0x0, 0x0⟩⟩

def triangleLocal137 : CachedLocal 41294 :=
  ⟨(4577, (4, 22)), ⟨7308430, (5588821220206770), 0x0, 0x0⟩⟩

def triangleLocal138 : CachedLocal 41294 :=
  ⟨(4584, (4, 22)), ⟨7324055, (1910405242148130), 0x0, 0x0⟩⟩

def triangleLocal139 : CachedLocal 41294 :=
  ⟨(4634, (1, 4)), ⟨6956250, (-5964221990099100), 0x1100000000, 0x801880000b8000046000019⟩⟩

def triangleLocal140 : CachedLocal 41294 :=
  ⟨(4634, (7, 5)), ⟨6956250, (-5964221990099100), 0x1100000000, 0x801880000b8000046000019⟩⟩

def triangleLocal141 : CachedLocal 41294 :=
  ⟨(4684, (7, 5)), ⟨6987500, (-6533737750016295), 0x1100000000, 0x33000016060009030002e⟩⟩

def triangleLocal142 : CachedLocal 41294 :=
  ⟨(4726, (0, 4)), ⟨7581875, (-5964221990099100), 0x1000000000, 0xc803980001c03000daaa002e⟩⟩

def triangleLocal143 : CachedLocal 41294 :=
  ⟨(4726, (6, 5)), ⟨7581875, (-5964221990099100), 0x1000000000, 0xc803980001c03000daaa002e⟩⟩

def triangleLocal144 : CachedLocal 41294 :=
  ⟨(4762, (6, 5)), ⟨7613125, (-6950356015461495), 0x1000000000, 0x53800028c30013618008f⟩⟩

def triangleLocal145 : CachedLocal 41294 :=
  ⟨(4774, (4, 4)), ⟨6706875, (-6950356015461495), 0x1110000000, 0x8049000023c0000f492002e⟩⟩

def triangleLocal146 : CachedLocal 41294 :=
  ⟨(4800, (0, 4)), ⟨7585000, (-5674947107240775), 0x1000000000, 0x56805b2a801b4000168aa0023⟩⟩

def triangleLocal147 : CachedLocal 41294 :=
  ⟨(4800, (6, 5)), ⟨7585000, (-5674947107240775), 0x1000000000, 0x56805b2a801b4000168aa0023⟩⟩

def triangleLocal148 : CachedLocal 41294 :=
  ⟨(4803, (0, 2)), ⟨5710000, (-5645662019500230), 0x1000000000, 0x56803986802c034016cad0031⟩⟩

def triangleLocal149 : CachedLocal 41294 :=
  ⟨(4803, (6, 3)), ⟨5710000, (-5645662019500230), 0x1000000000, 0x56803986802c034016cad0031⟩⟩

def triangleLocal150 : CachedLocal 41294 :=
  ⟨(4841, (7, 4)), ⟨6585000, (-5791210381386885), 0x1100000000, 0x708000344000184c0007a⟩⟩

def triangleLocal151 : CachedLocal 41294 :=
  ⟨(4871, (6, 3)), ⟨5756875, (-6041449658158005), 0x1000000000, 0xd008006803d43401f8f50092⟩⟩

def triangleLocal152 : CachedLocal 41294 :=
  ⟨(4940, (6, 5)), ⟨6450625, (-6866201123129985), 0x1111000000, 0xd807e0680344300136600048⟩⟩

def triangleLocal153 : CachedLocal 41294 :=
  ⟨(4944, (6, 5)), ⟨6841250, (-6533737750016295), 0x1111000000, 0xd80800680308000146180058⟩⟩

def triangleLocal154 : CachedLocal 41294 :=
  ⟨(4948, (6, 5)), ⟨7231875, (-5936530980842280), 0x1111000000, 0xd807a868038400014e180066⟩⟩

def triangleLocal155 : CachedLocal 41294 :=
  ⟨(5140, (7, 1)), ⟨1096900, (3480835429896825), 0x1100000000, 0x80cb800064c00030e00017d⟩⟩

def triangleLocal156 : CachedLocal 41294 :=
  ⟨(5417, (6, 1)), ⟨1722525, (3379239389722560), 0x1000000000, 0x13600009a03004c8a801d6⟩⟩

def triangleLocal157 : CachedLocal 41294 :=
  ⟨(5492, (6, 1)), ⟨1725650, (3753803428248510), 0x1000000000, 0x15b8000acc00055ea801e6⟩⟩

def triangleLocal158 : CachedLocal 41294 :=
  ⟨(5499, (6, 0)), ⟨1803775, (3414124955527650), 0x1000000000, 0x1610000af8000576a901f5⟩⟩

def triangleLocal159 : CachedLocal 41294 :=
  ⟨(10376, (4, 8)), ⟨3272555, (481973994954270), 0x1110000000, 0x74400039318c19de000df7⟩⟩

def triangleLocal160 : CachedLocal 41294 :=
  ⟨(10376, (10, 8)), ⟨3272555, (481973994954270), 0x1110000000, 0x74400039318c19de000df7⟩⟩

def triangleLocal161 : CachedLocal 41294 :=
  ⟨(10893, (10, 15)), ⟨3351305, (1256447371383750), 0x1110000000, 0x7d90003e48001ee6000f68⟩⟩

def triangleLocal162 : CachedLocal 41294 :=
  ⟨(11067, (4, 13)), ⟨1010680, (1256447371383750), 0x1110000000, 0x8148003fe92c1ee6000fc9⟩⟩

def triangleLocal163 : CachedLocal 41294 :=
  ⟨(11302, (4, 22)), ⟨7339430, (566066489491230), 0x1110000000, 0x84700041cc0020b6001058⟩⟩

def triangleLocal164 : CachedLocal 41294 :=
  ⟨(11302, (10, 22)), ⟨7339430, (566066489491230), 0x1110000000, 0x84700041cc0020b6001058⟩⟩

def triangleLocal165 : CachedLocal 41294 :=
  ⟨(11315, (0, 2)), ⟨170680, (1955508897500340), 0x1111000000, 0xc08228603ef4301d5e180ce3⟩⟩

def triangleLocal166 : CachedLocal 41294 :=
  ⟨(11315, (6, 2)), ⟨170680, (1955508897500340), 0x1111000000, 0xc08228603ef4301d5e180ce3⟩⟩

def triangleLocal167 : CachedLocal 41294 :=
  ⟨(11319, (0, 2)), ⟨951930, (1585561925437035), 0x1111000000, 0x8268603f24301d7c180cff⟩⟩

def triangleLocal168 : CachedLocal 41294 :=
  ⟨(11319, (6, 2)), ⟨951930, (1585561925437035), 0x1111000000, 0x8268603f24301d7c180cff⟩⟩

def triangleLocal169 : CachedLocal 41294 :=
  ⟨(11323, (0, 2)), ⟨1342555, (1563697081407825), 0x1111000000, 0x8288603f54301d9c180d0f⟩⟩

def triangleLocal170 : CachedLocal 41294 :=
  ⟨(11323, (6, 2)), ⟨1342555, (1563697081407825), 0x1111000000, 0x8288603f54301d9c180d0f⟩⟩

def triangleLocal171 : CachedLocal 41294 :=
  ⟨(11707, (10, 15)), ⟨3351430, (-995105458681425), 0x1110000000, 0x8ae80045252c1f92001136⟩⟩

def triangleLocal172 : CachedLocal 41294 :=
  ⟨(11806, (4, 13)), ⟨1010805, (-1323763747204080), 0x1110000000, 0x8c600045c52c1ed0961136⟩⟩

def triangleLocal173 : CachedLocal 41294 :=
  ⟨(11917, (4, 22)), ⟨7339555, (2690478467773005), 0x1110000000, 0x8de80046b92c20b00011a2⟩⟩

def triangleLocal174 : CachedLocal 41294 :=
  ⟨(11917, (10, 22)), ⟨7339555, (2690478467773005), 0x1110000000, 0x8de80046b92c20b00011a2⟩⟩

def triangleLocal175 : CachedLocal 41294 :=
  ⟨(11958, (6, 15)), ⟨3789055, (14939352640485), 0x1000000000, 0x8e30604709ec1ff4f61171⟩⟩

def triangleLocal176 : CachedLocal 41294 :=
  ⟨(11974, (6, 15)), ⟨3792180, (-1323763747204080), 0x1000000000, 0x8ea2b84741ec2052f6118c⟩⟩

def triangleLocal177 : CachedLocal 41294 :=
  ⟨(11977, (1, 13)), ⟨1135930, (3113335932716100), 0x1100000000, 0x8e825847098c1f24c61149⟩⟩

def triangleLocal178 : CachedLocal 41294 :=
  ⟨(12000, (6, 15)), ⟨3404680, (1255418541454350), 0x1111000000, 0x8ea0004718c022ba600fb2⟩⟩

def triangleLocal179 : CachedLocal 41294 :=
  ⟨(12033, (4, 22)), ⟨7339680, (1910405242148130), 0x1110000000, 0x8f400047852c20e69611ae⟩⟩

def triangleLocal180 : CachedLocal 41294 :=
  ⟨(12033, (10, 22)), ⟨7339680, (1910405242148130), 0x1110000000, 0x8f400047852c20e69611ae⟩⟩

def triangleLocal181 : CachedLocal 41294 :=
  ⟨(12042, (0, 22)), ⟨7714805, (566066489491230), 0x1000000000, 0x8f5bd847a1ec211cf611bd⟩⟩

def triangleLocal182 : CachedLocal 41294 :=
  ⟨(12042, (6, 22)), ⟨7714805, (566066489491230), 0x1000000000, 0x8f5bd847a1ec211cf611bd⟩⟩

def triangleLocal183 : CachedLocal 41294 :=
  ⟨(13020, (0, 4)), ⟨6644395, (-5964221990099100), 0x1111111100, 0x183af8081d64000c0692002e⟩⟩

def triangleLocal184 : CachedLocal 41294 :=
  ⟨(13076, (4, 7)), ⟨2456895, (-7445148830257320), 0x1111111100, 0x183f40081e60000c76000095⟩⟩

def triangleLocal185 : CachedLocal 41294 :=
  ⟨(13346, (0, 7)), ⟨2053895, (-7445148830257320), 0x1111111100, 0x1859918825980011d2f00095⟩⟩

def triangleLocal186 : CachedLocal 41294 :=
  ⟨(13545, (0, 1)), ⟨784420, (3480835429896825), 0x1111111100, 0x1862a80831352c11d200017d⟩⟩

def triangleLocal187 : CachedLocal 41294 :=
  ⟨(13592, (3, 10)), ⟨6425045, (1890842618202720), 0x1111111100, 0x186620c83259ec0ae20001ac⟩⟩

def triangleLocal188 : CachedLocal 41294 :=
  ⟨(13631, (0, 1)), ⟨396920, (1712390054567010), 0x1111111100, 0x186718082eddec0c7690017d⟩⟩

def triangleLocal189 : CachedLocal 41294 :=
  ⟨(14201, (4, 15)), ⟨4866920, (2465316850656660), 0x1111111100, 0x18839b8031352c0f30000381⟩⟩

def triangleLocal190 : CachedLocal 41294 :=
  ⟨(14663, (4, 15)), ⟨4851420, (2713047281903595), 0x1111111100, 0x4c88d73802edd2c12cc900381⟩⟩

def triangleLocal191 : CachedLocal 41294 :=
  ⟨(14680, (1, 11)), ⟨6273295, (1116722051341260), 0x1111111100, 0x6488ae128430d5c0a42c00297⟩⟩

def triangleLocal192 : CachedLocal 41294 :=
  ⟨(14697, (0, 6)), ⟨1273295, (1280890928299710), 0x1111111100, 0x7c87d912843912e0b2e910440⟩⟩

def triangleLocal193 : CachedLocal 41294 :=
  ⟨(14783, (4, 14)), ⟨4898295, (1955508897500340), 0x1111111100, 0x4c8839b80338dbc1664000490⟩⟩

def triangleLocal194 : CachedLocal 41294 :=
  ⟨(15127, (0, 14)), ⟨4495295, (3311109194335215), 0x1111111100, 0x3188d72603155ec0fd0f00490⟩⟩

def triangleLocal195 : CachedLocal 41294 :=
  ⟨(15339, (0, 4)), ⟨7591250, (-5964221990099100), 0x2111000000, 0x4a0961a4849d9242580aa121a0089618004b000024ec18121a⟩⟩

def triangleLocal196 : CachedLocal 41294 :=
  ⟨(15339, (6, 5)), ⟨7591250, (-5964221990099100), 0x2111000000, 0x4a0961a4849d9242580aa121a0089618004b000024ec18121a⟩⟩

def triangleLocal197 : CachedLocal 41294 :=
  ⟨(15387, (6, 5)), ⟨7622500, (-6950356015461495), 0x2111000000, 0x9aa0004d40002698f212a60089838684ba400253418124c⟩⟩

def triangleLocal198 : CachedLocal 41294 :=
  ⟨(15897, (6, 1)), ⟨1731900, (3379239389722560), 0x2111000000, 0xb2a0005941502afea8146f008abd80055d0002a52181414⟩⟩

def triangleLocal199 : CachedLocal 41294 :=
  ⟨(20373, (0, 2)), ⟨1733180, (481973994954270), 0x2111000000, 0x161d800b0ddec5110002c330015ea060aab430519c18265c⟩⟩

def triangleLocal200 : CachedLocal 41294 :=
  ⟨(20373, (6, 2)), ⟨1733180, (481973994954270), 0x2111000000, 0x161d800b0ddec5110002c330015ea060aab430519c18265c⟩⟩

def triangleLocal201 : CachedLocal 41294 :=
  ⟨(21118, (6, 15)), ⟨3795305, (-1323763747204080), 0x2111000000, 0x17702b8bb25ec5676f62e1e001763000bad8c05b76602a8d⟩⟩

def triangleLocal202 : CachedLocal 41294 :=
  ⟨(21203, (0, 22)), ⟨7717930, (566066489491230), 0x2111000000, 0x4b17853d8bc05ec584cf62e8d001785180bc04c05d1a602c26⟩⟩

def triangleLocal203 : CachedLocal 41294 :=
  ⟨(21203, (0, 23)), ⟨7717930, (566066489491230), 0x2111000000, 0x4b17853d8bc05ec584cf62e8d001785180bc04c05d1a602c26⟩⟩

def triangleLocal204 : CachedLocal 41294 :=
  ⟨(26820, (6, 5)), ⟨6800024, (-5964221990099100), 0x2222222210, 0x4d9cb4b80d4615c72b09232dc049c7a8e0e270cc6c4400329a⟩⟩

def triangleLocal205 : CachedLocal 41294 :=
  ⟨(26923, (4, 7)), ⟨2456899, (-7445148830257320), 0x2222222210, 0x709d8ba60dde5bc6a7ed83422049cdf820e51c9c69d2003314⟩⟩

def triangleLocal206 : CachedLocal 41294 :=
  ⟨(26923, (10, 7)), ⟨2456899, (-7445148830257320), 0x2222222210, 0x709d8ba60dde5bc6a7ed83422049cdf820e51c9c69d2003314⟩⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00025 :
    triangleLocal000.row = EJMTriangleCacheData.mirror triangleLocal000.state.1 := by
  have fields : FullLocalFields triangleLocal000
      ⟨triangleLocal000.state, EJMTriangleCacheData.mirror triangleLocal000.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00035 :
    triangleLocal002.row = EJMTriangleCacheData.mirror triangleLocal002.state.1 := by
  have fields : FullLocalFields triangleLocal002
      ⟨triangleLocal002.state, EJMTriangleCacheData.mirror triangleLocal002.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00046 :
    triangleLocal003.row = EJMTriangleCacheData.mirror triangleLocal003.state.1 := by
  have fields : FullLocalFields triangleLocal003
      ⟨triangleLocal003.state, EJMTriangleCacheData.mirror triangleLocal003.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00049 :
    triangleLocal007.row = EJMTriangleCacheData.mirror triangleLocal007.state.1 := by
  have fields : FullLocalFields triangleLocal007
      ⟨triangleLocal007.state, EJMTriangleCacheData.mirror triangleLocal007.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00072 :
    triangleLocal008.row = EJMTriangleCacheData.mirror triangleLocal008.state.1 := by
  have fields : FullLocalFields triangleLocal008
      ⟨triangleLocal008.state, EJMTriangleCacheData.mirror triangleLocal008.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00088 :
    triangleLocal009.row = EJMTriangleCacheData.mirror triangleLocal009.state.1 := by
  have fields : FullLocalFields triangleLocal009
      ⟨triangleLocal009.state, EJMTriangleCacheData.mirror triangleLocal009.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00102 :
    triangleLocal010.row = EJMTriangleCacheData.mirror triangleLocal010.state.1 := by
  have fields : FullLocalFields triangleLocal010
      ⟨triangleLocal010.state, EJMTriangleCacheData.mirror triangleLocal010.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00109 :
    triangleLocal012.row = EJMTriangleCacheData.mirror triangleLocal012.state.1 := by
  have fields : FullLocalFields triangleLocal012
      ⟨triangleLocal012.state, EJMTriangleCacheData.mirror triangleLocal012.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00112 :
    triangleLocal014.row = EJMTriangleCacheData.mirror triangleLocal014.state.1 := by
  have fields : FullLocalFields triangleLocal014
      ⟨triangleLocal014.state, EJMTriangleCacheData.mirror triangleLocal014.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00115 :
    triangleLocal016.row = EJMTriangleCacheData.mirror triangleLocal016.state.1 := by
  have fields : FullLocalFields triangleLocal016
      ⟨triangleLocal016.state, EJMTriangleCacheData.mirror triangleLocal016.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00122 :
    triangleLocal017.row = EJMTriangleCacheData.mirror triangleLocal017.state.1 := by
  have fields : FullLocalFields triangleLocal017
      ⟨triangleLocal017.state, EJMTriangleCacheData.mirror triangleLocal017.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00143 :
    triangleLocal018.row = EJMTriangleCacheData.mirror triangleLocal018.state.1 := by
  have fields : FullLocalFields triangleLocal018
      ⟨triangleLocal018.state, EJMTriangleCacheData.mirror triangleLocal018.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00146 :
    triangleLocal019.row = EJMTriangleCacheData.mirror triangleLocal019.state.1 := by
  have fields : FullLocalFields triangleLocal019
      ⟨triangleLocal019.state, EJMTriangleCacheData.mirror triangleLocal019.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00149 :
    triangleLocal020.row = EJMTriangleCacheData.mirror triangleLocal020.state.1 := by
  have fields : FullLocalFields triangleLocal020
      ⟨triangleLocal020.state, EJMTriangleCacheData.mirror triangleLocal020.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00155 :
    triangleLocal022.row = EJMTriangleCacheData.mirror triangleLocal022.state.1 := by
  have fields : FullLocalFields triangleLocal022
      ⟨triangleLocal022.state, EJMTriangleCacheData.mirror triangleLocal022.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00163 :
    triangleLocal023.row = EJMTriangleCacheData.mirror triangleLocal023.state.1 := by
  have fields : FullLocalFields triangleLocal023
      ⟨triangleLocal023.state, EJMTriangleCacheData.mirror triangleLocal023.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00167 :
    triangleLocal024.row = EJMTriangleCacheData.mirror triangleLocal024.state.1 := by
  have fields : FullLocalFields triangleLocal024
      ⟨triangleLocal024.state, EJMTriangleCacheData.mirror triangleLocal024.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00176 :
    triangleLocal025.row = EJMTriangleCacheData.mirror triangleLocal025.state.1 := by
  have fields : FullLocalFields triangleLocal025
      ⟨triangleLocal025.state, EJMTriangleCacheData.mirror triangleLocal025.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00180 :
    triangleLocal027.row = EJMTriangleCacheData.mirror triangleLocal027.state.1 := by
  have fields : FullLocalFields triangleLocal027
      ⟨triangleLocal027.state, EJMTriangleCacheData.mirror triangleLocal027.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00182 :
    triangleLocal029.row = EJMTriangleCacheData.mirror triangleLocal029.state.1 := by
  have fields : FullLocalFields triangleLocal029
      ⟨triangleLocal029.state, EJMTriangleCacheData.mirror triangleLocal029.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00194 :
    triangleLocal031.row = EJMTriangleCacheData.mirror triangleLocal031.state.1 := by
  have fields : FullLocalFields triangleLocal031
      ⟨triangleLocal031.state, EJMTriangleCacheData.mirror triangleLocal031.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00209 :
    triangleLocal032.row = EJMTriangleCacheData.mirror triangleLocal032.state.1 := by
  have fields : FullLocalFields triangleLocal032
      ⟨triangleLocal032.state, EJMTriangleCacheData.mirror triangleLocal032.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00225 :
    triangleLocal033.row = EJMTriangleCacheData.mirror triangleLocal033.state.1 := by
  have fields : FullLocalFields triangleLocal033
      ⟨triangleLocal033.state, EJMTriangleCacheData.mirror triangleLocal033.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00245 :
    triangleLocal034.row = EJMTriangleCacheData.mirror triangleLocal034.state.1 := by
  have fields : FullLocalFields triangleLocal034
      ⟨triangleLocal034.state, EJMTriangleCacheData.mirror triangleLocal034.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00252 :
    triangleLocal035.row = EJMTriangleCacheData.mirror triangleLocal035.state.1 := by
  have fields : FullLocalFields triangleLocal035
      ⟨triangleLocal035.state, EJMTriangleCacheData.mirror triangleLocal035.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00256 :
    triangleLocal036.row = EJMTriangleCacheData.mirror triangleLocal036.state.1 := by
  have fields : FullLocalFields triangleLocal036
      ⟨triangleLocal036.state, EJMTriangleCacheData.mirror triangleLocal036.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00381 :
    triangleLocal037.row = EJMTriangleCacheData.mirror triangleLocal037.state.1 := by
  have fields : FullLocalFields triangleLocal037
      ⟨triangleLocal037.state, EJMTriangleCacheData.mirror triangleLocal037.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00428 :
    triangleLocal038.row = EJMTriangleCacheData.mirror triangleLocal038.state.1 := by
  have fields : FullLocalFields triangleLocal038
      ⟨triangleLocal038.state, EJMTriangleCacheData.mirror triangleLocal038.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00470 :
    triangleLocal039.row = EJMTriangleCacheData.mirror triangleLocal039.state.1 := by
  have fields : FullLocalFields triangleLocal039
      ⟨triangleLocal039.state, EJMTriangleCacheData.mirror triangleLocal039.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00486 :
    triangleLocal040.row = EJMTriangleCacheData.mirror triangleLocal040.state.1 := by
  have fields : FullLocalFields triangleLocal040
      ⟨triangleLocal040.state, EJMTriangleCacheData.mirror triangleLocal040.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00501 :
    triangleLocal041.row = EJMTriangleCacheData.mirror triangleLocal041.state.1 := by
  have fields : FullLocalFields triangleLocal041
      ⟨triangleLocal041.state, EJMTriangleCacheData.mirror triangleLocal041.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00612 :
    triangleLocal042.row = EJMTriangleCacheData.mirror triangleLocal042.state.1 := by
  have fields : FullLocalFields triangleLocal042
      ⟨triangleLocal042.state, EJMTriangleCacheData.mirror triangleLocal042.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00616 :
    triangleLocal043.row = EJMTriangleCacheData.mirror triangleLocal043.state.1 := by
  have fields : FullLocalFields triangleLocal043
      ⟨triangleLocal043.state, EJMTriangleCacheData.mirror triangleLocal043.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00620 :
    triangleLocal044.row = EJMTriangleCacheData.mirror triangleLocal044.state.1 := by
  have fields : FullLocalFields triangleLocal044
      ⟨triangleLocal044.state, EJMTriangleCacheData.mirror triangleLocal044.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00663 :
    triangleLocal045.row = EJMTriangleCacheData.mirror triangleLocal045.state.1 := by
  have fields : FullLocalFields triangleLocal045
      ⟨triangleLocal045.state, EJMTriangleCacheData.mirror triangleLocal045.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00687 :
    triangleLocal046.row = EJMTriangleCacheData.mirror triangleLocal046.state.1 := by
  have fields : FullLocalFields triangleLocal046
      ⟨triangleLocal046.state, EJMTriangleCacheData.mirror triangleLocal046.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00691 :
    triangleLocal047.row = EJMTriangleCacheData.mirror triangleLocal047.state.1 := by
  have fields : FullLocalFields triangleLocal047
      ⟨triangleLocal047.state, EJMTriangleCacheData.mirror triangleLocal047.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00695 :
    triangleLocal048.row = EJMTriangleCacheData.mirror triangleLocal048.state.1 := by
  have fields : FullLocalFields triangleLocal048
      ⟨triangleLocal048.state, EJMTriangleCacheData.mirror triangleLocal048.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00699 :
    triangleLocal049.row = EJMTriangleCacheData.mirror triangleLocal049.state.1 := by
  have fields : FullLocalFields triangleLocal049
      ⟨triangleLocal049.state, EJMTriangleCacheData.mirror triangleLocal049.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00702 :
    triangleLocal050.row = EJMTriangleCacheData.mirror triangleLocal050.state.1 := by
  have fields : FullLocalFields triangleLocal050
      ⟨triangleLocal050.state, EJMTriangleCacheData.mirror triangleLocal050.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00706 :
    triangleLocal051.row = EJMTriangleCacheData.mirror triangleLocal051.state.1 := by
  have fields : FullLocalFields triangleLocal051
      ⟨triangleLocal051.state, EJMTriangleCacheData.mirror triangleLocal051.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_00897 :
    triangleLocal052.row = EJMTriangleCacheData.mirror triangleLocal052.state.1 := by
  have fields : FullLocalFields triangleLocal052
      ⟨triangleLocal052.state, EJMTriangleCacheData.mirror triangleLocal052.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_01088 :
    triangleLocal054.row = EJMTriangleCacheData.mirror triangleLocal054.state.1 := by
  have fields : FullLocalFields triangleLocal054
      ⟨triangleLocal054.state, EJMTriangleCacheData.mirror triangleLocal054.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_01168 :
    triangleLocal056.row = EJMTriangleCacheData.mirror triangleLocal056.state.1 := by
  have fields : FullLocalFields triangleLocal056
      ⟨triangleLocal056.state, EJMTriangleCacheData.mirror triangleLocal056.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_01313 :
    triangleLocal057.row = EJMTriangleCacheData.mirror triangleLocal057.state.1 := by
  have fields : FullLocalFields triangleLocal057
      ⟨triangleLocal057.state, EJMTriangleCacheData.mirror triangleLocal057.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_01393 :
    triangleLocal058.row = EJMTriangleCacheData.mirror triangleLocal058.state.1 := by
  have fields : FullLocalFields triangleLocal058
      ⟨triangleLocal058.state, EJMTriangleCacheData.mirror triangleLocal058.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_01431 :
    triangleLocal059.row = EJMTriangleCacheData.mirror triangleLocal059.state.1 := by
  have fields : FullLocalFields triangleLocal059
      ⟨triangleLocal059.state, EJMTriangleCacheData.mirror triangleLocal059.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_01595 :
    triangleLocal061.row = EJMTriangleCacheData.mirror triangleLocal061.state.1 := by
  have fields : FullLocalFields triangleLocal061
      ⟨triangleLocal061.state, EJMTriangleCacheData.mirror triangleLocal061.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_01944 :
    triangleLocal063.row = EJMTriangleCacheData.mirror triangleLocal063.state.1 := by
  have fields : FullLocalFields triangleLocal063
      ⟨triangleLocal063.state, EJMTriangleCacheData.mirror triangleLocal063.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_02024 :
    triangleLocal064.row = EJMTriangleCacheData.mirror triangleLocal064.state.1 := by
  have fields : FullLocalFields triangleLocal064
      ⟨triangleLocal064.state, EJMTriangleCacheData.mirror triangleLocal064.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_02281 :
    triangleLocal066.row = EJMTriangleCacheData.mirror triangleLocal066.state.1 := by
  have fields : FullLocalFields triangleLocal066
      ⟨triangleLocal066.state, EJMTriangleCacheData.mirror triangleLocal066.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_02406 :
    triangleLocal068.row = EJMTriangleCacheData.mirror triangleLocal068.state.1 := by
  have fields : FullLocalFields triangleLocal068
      ⟨triangleLocal068.state, EJMTriangleCacheData.mirror triangleLocal068.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_02866 :
    triangleLocal069.row = EJMTriangleCacheData.mirror triangleLocal069.state.1 := by
  have fields : FullLocalFields triangleLocal069
      ⟨triangleLocal069.state, EJMTriangleCacheData.mirror triangleLocal069.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_02999 :
    triangleLocal071.row = EJMTriangleCacheData.mirror triangleLocal071.state.1 := by
  have fields : FullLocalFields triangleLocal071
      ⟨triangleLocal071.state, EJMTriangleCacheData.mirror triangleLocal071.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03149 :
    triangleLocal073.row = EJMTriangleCacheData.mirror triangleLocal073.state.1 := by
  have fields : FullLocalFields triangleLocal073
      ⟨triangleLocal073.state, EJMTriangleCacheData.mirror triangleLocal073.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03157 :
    triangleLocal074.row = EJMTriangleCacheData.mirror triangleLocal074.state.1 := by
  have fields : FullLocalFields triangleLocal074
      ⟨triangleLocal074.state, EJMTriangleCacheData.mirror triangleLocal074.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03222 :
    triangleLocal075.row = EJMTriangleCacheData.mirror triangleLocal075.state.1 := by
  have fields : FullLocalFields triangleLocal075
      ⟨triangleLocal075.state, EJMTriangleCacheData.mirror triangleLocal075.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03268 :
    triangleLocal076.row = EJMTriangleCacheData.mirror triangleLocal076.state.1 := by
  have fields : FullLocalFields triangleLocal076
      ⟨triangleLocal076.state, EJMTriangleCacheData.mirror triangleLocal076.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03299 :
    triangleLocal077.row = EJMTriangleCacheData.mirror triangleLocal077.state.1 := by
  have fields : FullLocalFields triangleLocal077
      ⟨triangleLocal077.state, EJMTriangleCacheData.mirror triangleLocal077.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03311 :
    triangleLocal080.row = EJMTriangleCacheData.mirror triangleLocal080.state.1 := by
  have fields : FullLocalFields triangleLocal080
      ⟨triangleLocal080.state, EJMTriangleCacheData.mirror triangleLocal080.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03327 :
    triangleLocal081.row = EJMTriangleCacheData.mirror triangleLocal081.state.1 := by
  have fields : FullLocalFields triangleLocal081
      ⟨triangleLocal081.state, EJMTriangleCacheData.mirror triangleLocal081.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03343 :
    triangleLocal083.row = EJMTriangleCacheData.mirror triangleLocal083.state.1 := by
  have fields : FullLocalFields triangleLocal083
      ⟨triangleLocal083.state, EJMTriangleCacheData.mirror triangleLocal083.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03575 :
    triangleLocal085.row = EJMTriangleCacheData.mirror triangleLocal085.state.1 := by
  have fields : FullLocalFields triangleLocal085
      ⟨triangleLocal085.state, EJMTriangleCacheData.mirror triangleLocal085.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03660 :
    triangleLocal087.row = EJMTriangleCacheData.mirror triangleLocal087.state.1 := by
  have fields : FullLocalFields triangleLocal087
      ⟨triangleLocal087.state, EJMTriangleCacheData.mirror triangleLocal087.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03720 :
    triangleLocal089.row = EJMTriangleCacheData.mirror triangleLocal089.state.1 := by
  have fields : FullLocalFields triangleLocal089
      ⟨triangleLocal089.state, EJMTriangleCacheData.mirror triangleLocal089.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03774 :
    triangleLocal090.row = EJMTriangleCacheData.mirror triangleLocal090.state.1 := by
  have fields : FullLocalFields triangleLocal090
      ⟨triangleLocal090.state, EJMTriangleCacheData.mirror triangleLocal090.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03790 :
    triangleLocal091.row = EJMTriangleCacheData.mirror triangleLocal091.state.1 := by
  have fields : FullLocalFields triangleLocal091
      ⟨triangleLocal091.state, EJMTriangleCacheData.mirror triangleLocal091.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03944 :
    triangleLocal093.row = EJMTriangleCacheData.mirror triangleLocal093.state.1 := by
  have fields : FullLocalFields triangleLocal093
      ⟨triangleLocal093.state, EJMTriangleCacheData.mirror triangleLocal093.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03955 :
    triangleLocal094.row = EJMTriangleCacheData.mirror triangleLocal094.state.1 := by
  have fields : FullLocalFields triangleLocal094
      ⟨triangleLocal094.state, EJMTriangleCacheData.mirror triangleLocal094.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_03986 :
    triangleLocal095.row = EJMTriangleCacheData.mirror triangleLocal095.state.1 := by
  have fields : FullLocalFields triangleLocal095
      ⟨triangleLocal095.state, EJMTriangleCacheData.mirror triangleLocal095.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04018 :
    triangleLocal096.row = EJMTriangleCacheData.mirror triangleLocal096.state.1 := by
  have fields : FullLocalFields triangleLocal096
      ⟨triangleLocal096.state, EJMTriangleCacheData.mirror triangleLocal096.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04041 :
    triangleLocal098.row = EJMTriangleCacheData.mirror triangleLocal098.state.1 := by
  have fields : FullLocalFields triangleLocal098
      ⟨triangleLocal098.state, EJMTriangleCacheData.mirror triangleLocal098.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04053 :
    triangleLocal099.row = EJMTriangleCacheData.mirror triangleLocal099.state.1 := by
  have fields : FullLocalFields triangleLocal099
      ⟨triangleLocal099.state, EJMTriangleCacheData.mirror triangleLocal099.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04090 :
    triangleLocal101.row = EJMTriangleCacheData.mirror triangleLocal101.state.1 := by
  have fields : FullLocalFields triangleLocal101
      ⟨triangleLocal101.state, EJMTriangleCacheData.mirror triangleLocal101.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04137 :
    triangleLocal102.row = EJMTriangleCacheData.mirror triangleLocal102.state.1 := by
  have fields : FullLocalFields triangleLocal102
      ⟨triangleLocal102.state, EJMTriangleCacheData.mirror triangleLocal102.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04173 :
    triangleLocal103.row = EJMTriangleCacheData.mirror triangleLocal103.state.1 := by
  have fields : FullLocalFields triangleLocal103
      ⟨triangleLocal103.state, EJMTriangleCacheData.mirror triangleLocal103.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04177 :
    triangleLocal104.row = EJMTriangleCacheData.mirror triangleLocal104.state.1 := by
  have fields : FullLocalFields triangleLocal104
      ⟨triangleLocal104.state, EJMTriangleCacheData.mirror triangleLocal104.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04184 :
    triangleLocal108.row = EJMTriangleCacheData.mirror triangleLocal108.state.1 := by
  have fields : FullLocalFields triangleLocal108
      ⟨triangleLocal108.state, EJMTriangleCacheData.mirror triangleLocal108.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04187 :
    triangleLocal111.row = EJMTriangleCacheData.mirror triangleLocal111.state.1 := by
  have fields : FullLocalFields triangleLocal111
      ⟨triangleLocal111.state, EJMTriangleCacheData.mirror triangleLocal111.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04211 :
    triangleLocal115.row = EJMTriangleCacheData.mirror triangleLocal115.state.1 := by
  have fields : FullLocalFields triangleLocal115
      ⟨triangleLocal115.state, EJMTriangleCacheData.mirror triangleLocal115.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04238 :
    triangleLocal116.row = EJMTriangleCacheData.mirror triangleLocal116.state.1 := by
  have fields : FullLocalFields triangleLocal116
      ⟨triangleLocal116.state, EJMTriangleCacheData.mirror triangleLocal116.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04291 :
    triangleLocal118.row = EJMTriangleCacheData.mirror triangleLocal118.state.1 := by
  have fields : FullLocalFields triangleLocal118
      ⟨triangleLocal118.state, EJMTriangleCacheData.mirror triangleLocal118.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04324 :
    triangleLocal119.row = EJMTriangleCacheData.mirror triangleLocal119.state.1 := by
  have fields : FullLocalFields triangleLocal119
      ⟨triangleLocal119.state, EJMTriangleCacheData.mirror triangleLocal119.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04406 :
    triangleLocal120.row = EJMTriangleCacheData.mirror triangleLocal120.state.1 := by
  have fields : FullLocalFields triangleLocal120
      ⟨triangleLocal120.state, EJMTriangleCacheData.mirror triangleLocal120.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04425 :
    triangleLocal121.row = EJMTriangleCacheData.mirror triangleLocal121.state.1 := by
  have fields : FullLocalFields triangleLocal121
      ⟨triangleLocal121.state, EJMTriangleCacheData.mirror triangleLocal121.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04444 :
    triangleLocal122.row = EJMTriangleCacheData.mirror triangleLocal122.state.1 := by
  have fields : FullLocalFields triangleLocal122
      ⟨triangleLocal122.state, EJMTriangleCacheData.mirror triangleLocal122.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04445 :
    triangleLocal123.row = EJMTriangleCacheData.mirror triangleLocal123.state.1 := by
  have fields : FullLocalFields triangleLocal123
      ⟨triangleLocal123.state, EJMTriangleCacheData.mirror triangleLocal123.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04465 :
    triangleLocal124.row = EJMTriangleCacheData.mirror triangleLocal124.state.1 := by
  have fields : FullLocalFields triangleLocal124
      ⟨triangleLocal124.state, EJMTriangleCacheData.mirror triangleLocal124.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04492 :
    triangleLocal125.row = EJMTriangleCacheData.mirror triangleLocal125.state.1 := by
  have fields : FullLocalFields triangleLocal125
      ⟨triangleLocal125.state, EJMTriangleCacheData.mirror triangleLocal125.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04514 :
    triangleLocal127.row = EJMTriangleCacheData.mirror triangleLocal127.state.1 := by
  have fields : FullLocalFields triangleLocal127
      ⟨triangleLocal127.state, EJMTriangleCacheData.mirror triangleLocal127.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04526 :
    triangleLocal130.row = EJMTriangleCacheData.mirror triangleLocal130.state.1 := by
  have fields : FullLocalFields triangleLocal130
      ⟨triangleLocal130.state, EJMTriangleCacheData.mirror triangleLocal130.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04541 :
    triangleLocal131.row = EJMTriangleCacheData.mirror triangleLocal131.state.1 := by
  have fields : FullLocalFields triangleLocal131
      ⟨triangleLocal131.state, EJMTriangleCacheData.mirror triangleLocal131.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04546 :
    triangleLocal133.row = EJMTriangleCacheData.mirror triangleLocal133.state.1 := by
  have fields : FullLocalFields triangleLocal133
      ⟨triangleLocal133.state, EJMTriangleCacheData.mirror triangleLocal133.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04550 :
    triangleLocal134.row = EJMTriangleCacheData.mirror triangleLocal134.state.1 := by
  have fields : FullLocalFields triangleLocal134
      ⟨triangleLocal134.state, EJMTriangleCacheData.mirror triangleLocal134.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04560 :
    triangleLocal135.row = EJMTriangleCacheData.mirror triangleLocal135.state.1 := by
  have fields : FullLocalFields triangleLocal135
      ⟨triangleLocal135.state, EJMTriangleCacheData.mirror triangleLocal135.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04564 :
    triangleLocal136.row = EJMTriangleCacheData.mirror triangleLocal136.state.1 := by
  have fields : FullLocalFields triangleLocal136
      ⟨triangleLocal136.state, EJMTriangleCacheData.mirror triangleLocal136.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04577 :
    triangleLocal137.row = EJMTriangleCacheData.mirror triangleLocal137.state.1 := by
  have fields : FullLocalFields triangleLocal137
      ⟨triangleLocal137.state, EJMTriangleCacheData.mirror triangleLocal137.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04584 :
    triangleLocal138.row = EJMTriangleCacheData.mirror triangleLocal138.state.1 := by
  have fields : FullLocalFields triangleLocal138
      ⟨triangleLocal138.state, EJMTriangleCacheData.mirror triangleLocal138.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04634 :
    triangleLocal140.row = EJMTriangleCacheData.mirror triangleLocal140.state.1 := by
  have fields : FullLocalFields triangleLocal140
      ⟨triangleLocal140.state, EJMTriangleCacheData.mirror triangleLocal140.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04684 :
    triangleLocal141.row = EJMTriangleCacheData.mirror triangleLocal141.state.1 := by
  have fields : FullLocalFields triangleLocal141
      ⟨triangleLocal141.state, EJMTriangleCacheData.mirror triangleLocal141.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04726 :
    triangleLocal143.row = EJMTriangleCacheData.mirror triangleLocal143.state.1 := by
  have fields : FullLocalFields triangleLocal143
      ⟨triangleLocal143.state, EJMTriangleCacheData.mirror triangleLocal143.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04762 :
    triangleLocal144.row = EJMTriangleCacheData.mirror triangleLocal144.state.1 := by
  have fields : FullLocalFields triangleLocal144
      ⟨triangleLocal144.state, EJMTriangleCacheData.mirror triangleLocal144.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04774 :
    triangleLocal145.row = EJMTriangleCacheData.mirror triangleLocal145.state.1 := by
  have fields : FullLocalFields triangleLocal145
      ⟨triangleLocal145.state, EJMTriangleCacheData.mirror triangleLocal145.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04800 :
    triangleLocal147.row = EJMTriangleCacheData.mirror triangleLocal147.state.1 := by
  have fields : FullLocalFields triangleLocal147
      ⟨triangleLocal147.state, EJMTriangleCacheData.mirror triangleLocal147.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04803 :
    triangleLocal149.row = EJMTriangleCacheData.mirror triangleLocal149.state.1 := by
  have fields : FullLocalFields triangleLocal149
      ⟨triangleLocal149.state, EJMTriangleCacheData.mirror triangleLocal149.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04841 :
    triangleLocal150.row = EJMTriangleCacheData.mirror triangleLocal150.state.1 := by
  have fields : FullLocalFields triangleLocal150
      ⟨triangleLocal150.state, EJMTriangleCacheData.mirror triangleLocal150.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04871 :
    triangleLocal151.row = EJMTriangleCacheData.mirror triangleLocal151.state.1 := by
  have fields : FullLocalFields triangleLocal151
      ⟨triangleLocal151.state, EJMTriangleCacheData.mirror triangleLocal151.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04940 :
    triangleLocal152.row = EJMTriangleCacheData.mirror triangleLocal152.state.1 := by
  have fields : FullLocalFields triangleLocal152
      ⟨triangleLocal152.state, EJMTriangleCacheData.mirror triangleLocal152.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04944 :
    triangleLocal153.row = EJMTriangleCacheData.mirror triangleLocal153.state.1 := by
  have fields : FullLocalFields triangleLocal153
      ⟨triangleLocal153.state, EJMTriangleCacheData.mirror triangleLocal153.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_04948 :
    triangleLocal154.row = EJMTriangleCacheData.mirror triangleLocal154.state.1 := by
  have fields : FullLocalFields triangleLocal154
      ⟨triangleLocal154.state, EJMTriangleCacheData.mirror triangleLocal154.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_05140 :
    triangleLocal155.row = EJMTriangleCacheData.mirror triangleLocal155.state.1 := by
  have fields : FullLocalFields triangleLocal155
      ⟨triangleLocal155.state, EJMTriangleCacheData.mirror triangleLocal155.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_05417 :
    triangleLocal156.row = EJMTriangleCacheData.mirror triangleLocal156.state.1 := by
  have fields : FullLocalFields triangleLocal156
      ⟨triangleLocal156.state, EJMTriangleCacheData.mirror triangleLocal156.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_05492 :
    triangleLocal157.row = EJMTriangleCacheData.mirror triangleLocal157.state.1 := by
  have fields : FullLocalFields triangleLocal157
      ⟨triangleLocal157.state, EJMTriangleCacheData.mirror triangleLocal157.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_05499 :
    triangleLocal158.row = EJMTriangleCacheData.mirror triangleLocal158.state.1 := by
  have fields : FullLocalFields triangleLocal158
      ⟨triangleLocal158.state, EJMTriangleCacheData.mirror triangleLocal158.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_10376 :
    triangleLocal160.row = EJMTriangleCacheData.mirror triangleLocal160.state.1 := by
  have fields : FullLocalFields triangleLocal160
      ⟨triangleLocal160.state, EJMTriangleCacheData.mirror triangleLocal160.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_10893 :
    triangleLocal161.row = EJMTriangleCacheData.mirror triangleLocal161.state.1 := by
  have fields : FullLocalFields triangleLocal161
      ⟨triangleLocal161.state, EJMTriangleCacheData.mirror triangleLocal161.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_11067 :
    triangleLocal162.row = EJMTriangleCacheData.mirror triangleLocal162.state.1 := by
  have fields : FullLocalFields triangleLocal162
      ⟨triangleLocal162.state, EJMTriangleCacheData.mirror triangleLocal162.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_11302 :
    triangleLocal164.row = EJMTriangleCacheData.mirror triangleLocal164.state.1 := by
  have fields : FullLocalFields triangleLocal164
      ⟨triangleLocal164.state, EJMTriangleCacheData.mirror triangleLocal164.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_11315 :
    triangleLocal165.row = EJMTriangleCacheData.mirror triangleLocal165.state.1 := by
  have fields : FullLocalFields triangleLocal165
      ⟨triangleLocal165.state, EJMTriangleCacheData.mirror triangleLocal165.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_11319 :
    triangleLocal167.row = EJMTriangleCacheData.mirror triangleLocal167.state.1 := by
  have fields : FullLocalFields triangleLocal167
      ⟨triangleLocal167.state, EJMTriangleCacheData.mirror triangleLocal167.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_11323 :
    triangleLocal169.row = EJMTriangleCacheData.mirror triangleLocal169.state.1 := by
  have fields : FullLocalFields triangleLocal169
      ⟨triangleLocal169.state, EJMTriangleCacheData.mirror triangleLocal169.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_11707 :
    triangleLocal171.row = EJMTriangleCacheData.mirror triangleLocal171.state.1 := by
  have fields : FullLocalFields triangleLocal171
      ⟨triangleLocal171.state, EJMTriangleCacheData.mirror triangleLocal171.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_11806 :
    triangleLocal172.row = EJMTriangleCacheData.mirror triangleLocal172.state.1 := by
  have fields : FullLocalFields triangleLocal172
      ⟨triangleLocal172.state, EJMTriangleCacheData.mirror triangleLocal172.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_11917 :
    triangleLocal174.row = EJMTriangleCacheData.mirror triangleLocal174.state.1 := by
  have fields : FullLocalFields triangleLocal174
      ⟨triangleLocal174.state, EJMTriangleCacheData.mirror triangleLocal174.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_11958 :
    triangleLocal175.row = EJMTriangleCacheData.mirror triangleLocal175.state.1 := by
  have fields : FullLocalFields triangleLocal175
      ⟨triangleLocal175.state, EJMTriangleCacheData.mirror triangleLocal175.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_11974 :
    triangleLocal176.row = EJMTriangleCacheData.mirror triangleLocal176.state.1 := by
  have fields : FullLocalFields triangleLocal176
      ⟨triangleLocal176.state, EJMTriangleCacheData.mirror triangleLocal176.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_11977 :
    triangleLocal177.row = EJMTriangleCacheData.mirror triangleLocal177.state.1 := by
  have fields : FullLocalFields triangleLocal177
      ⟨triangleLocal177.state, EJMTriangleCacheData.mirror triangleLocal177.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_12000 :
    triangleLocal178.row = EJMTriangleCacheData.mirror triangleLocal178.state.1 := by
  have fields : FullLocalFields triangleLocal178
      ⟨triangleLocal178.state, EJMTriangleCacheData.mirror triangleLocal178.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_12033 :
    triangleLocal180.row = EJMTriangleCacheData.mirror triangleLocal180.state.1 := by
  have fields : FullLocalFields triangleLocal180
      ⟨triangleLocal180.state, EJMTriangleCacheData.mirror triangleLocal180.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_12042 :
    triangleLocal182.row = EJMTriangleCacheData.mirror triangleLocal182.state.1 := by
  have fields : FullLocalFields triangleLocal182
      ⟨triangleLocal182.state, EJMTriangleCacheData.mirror triangleLocal182.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_13020 :
    triangleLocal183.row = EJMTriangleCacheData.mirror triangleLocal183.state.1 := by
  have fields : FullLocalFields triangleLocal183
      ⟨triangleLocal183.state, EJMTriangleCacheData.mirror triangleLocal183.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_13076 :
    triangleLocal184.row = EJMTriangleCacheData.mirror triangleLocal184.state.1 := by
  have fields : FullLocalFields triangleLocal184
      ⟨triangleLocal184.state, EJMTriangleCacheData.mirror triangleLocal184.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_13346 :
    triangleLocal185.row = EJMTriangleCacheData.mirror triangleLocal185.state.1 := by
  have fields : FullLocalFields triangleLocal185
      ⟨triangleLocal185.state, EJMTriangleCacheData.mirror triangleLocal185.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_13545 :
    triangleLocal186.row = EJMTriangleCacheData.mirror triangleLocal186.state.1 := by
  have fields : FullLocalFields triangleLocal186
      ⟨triangleLocal186.state, EJMTriangleCacheData.mirror triangleLocal186.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_13592 :
    triangleLocal187.row = EJMTriangleCacheData.mirror triangleLocal187.state.1 := by
  have fields : FullLocalFields triangleLocal187
      ⟨triangleLocal187.state, EJMTriangleCacheData.mirror triangleLocal187.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_13631 :
    triangleLocal188.row = EJMTriangleCacheData.mirror triangleLocal188.state.1 := by
  have fields : FullLocalFields triangleLocal188
      ⟨triangleLocal188.state, EJMTriangleCacheData.mirror triangleLocal188.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_14201 :
    triangleLocal189.row = EJMTriangleCacheData.mirror triangleLocal189.state.1 := by
  have fields : FullLocalFields triangleLocal189
      ⟨triangleLocal189.state, EJMTriangleCacheData.mirror triangleLocal189.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_14663 :
    triangleLocal190.row = EJMTriangleCacheData.mirror triangleLocal190.state.1 := by
  have fields : FullLocalFields triangleLocal190
      ⟨triangleLocal190.state, EJMTriangleCacheData.mirror triangleLocal190.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_14680 :
    triangleLocal191.row = EJMTriangleCacheData.mirror triangleLocal191.state.1 := by
  have fields : FullLocalFields triangleLocal191
      ⟨triangleLocal191.state, EJMTriangleCacheData.mirror triangleLocal191.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_14697 :
    triangleLocal192.row = EJMTriangleCacheData.mirror triangleLocal192.state.1 := by
  have fields : FullLocalFields triangleLocal192
      ⟨triangleLocal192.state, EJMTriangleCacheData.mirror triangleLocal192.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_14783 :
    triangleLocal193.row = EJMTriangleCacheData.mirror triangleLocal193.state.1 := by
  have fields : FullLocalFields triangleLocal193
      ⟨triangleLocal193.state, EJMTriangleCacheData.mirror triangleLocal193.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_mirror_15127 :
    triangleLocal194.row = EJMTriangleCacheData.mirror triangleLocal194.state.1 := by
  have fields : FullLocalFields triangleLocal194
      ⟨triangleLocal194.state, EJMTriangleCacheData.mirror triangleLocal194.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 41294 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_000 :
    (triangleStep triangleLocal140 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal000.state := by
  decide +kernel

theorem triangle_update_000 :
    triangleStep triangleLocal140 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal000 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_000 triangle_mirror_00025

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_001 :
    (triangleStep triangleLocal140 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal007.state := by
  decide +kernel

theorem triangle_update_001 :
    triangleStep triangleLocal140 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal007 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_001 triangle_mirror_00049

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_002 :
    (triangleStep triangleLocal140 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal004.state := by
  decide +kernel

theorem triangle_update_002 :
    triangleStep triangleLocal140 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal004 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_002 triangle_mirror_00046

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_003 :
    (triangleStep triangleLocal140 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal002.state := by
  decide +kernel

theorem triangle_update_003 :
    triangleStep triangleLocal140 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal002 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_003 triangle_mirror_00035

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_004 :
    (triangleStep triangleLocal141 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal005.state := by
  decide +kernel

theorem triangle_update_004 :
    triangleStep triangleLocal141 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal005 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_004 triangle_mirror_00046

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_005 :
    (triangleStep triangleLocal141 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal010.state := by
  decide +kernel

theorem triangle_update_005 :
    triangleStep triangleLocal141 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal010 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_005 triangle_mirror_00102

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_006 :
    (triangleStep triangleLocal141 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal009.state := by
  decide +kernel

theorem triangle_update_006 :
    triangleStep triangleLocal141 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal009 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_006 triangle_mirror_00088

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_007 :
    (triangleStep triangleLocal141 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal008.state := by
  decide +kernel

theorem triangle_update_007 :
    triangleStep triangleLocal141 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal008 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_007 triangle_mirror_00072

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_008 :
    (triangleStep triangleLocal142 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal004.state := by
  decide +kernel

theorem triangle_update_008 :
    triangleStep triangleLocal142 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal004 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_008 triangle_mirror_00046

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_009 :
    (triangleStep triangleLocal142 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal015.state := by
  decide +kernel

theorem triangle_update_009 :
    triangleStep triangleLocal142 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal015 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_009 triangle_mirror_00115

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_010 :
    (triangleStep triangleLocal142 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal011.state := by
  decide +kernel

theorem triangle_update_010 :
    triangleStep triangleLocal142 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal011 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_010 triangle_mirror_00109

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_011 :
    (triangleStep triangleLocal142 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal013.state := by
  decide +kernel

theorem triangle_update_011 :
    triangleStep triangleLocal142 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal013 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_011 triangle_mirror_00112

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_012 :
    (triangleStep triangleLocal143 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal003.state := by
  decide +kernel

theorem triangle_update_012 :
    triangleStep triangleLocal143 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal003 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_012 triangle_mirror_00046

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_013 :
    (triangleStep triangleLocal143 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal016.state := by
  decide +kernel

theorem triangle_update_013 :
    triangleStep triangleLocal143 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal016 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_013 triangle_mirror_00115

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_014 :
    (triangleStep triangleLocal143 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal014.state := by
  decide +kernel

theorem triangle_update_014 :
    triangleStep triangleLocal143 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal014 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_014 triangle_mirror_00112

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_015 :
    (triangleStep triangleLocal143 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal012.state := by
  decide +kernel

theorem triangle_update_015 :
    triangleStep triangleLocal143 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal012 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_015 triangle_mirror_00109

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_016 :
    (triangleStep triangleLocal144 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal018.state := by
  decide +kernel

theorem triangle_update_016 :
    triangleStep triangleLocal144 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal018 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_016 triangle_mirror_00143

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_017 :
    (triangleStep triangleLocal144 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal024.state := by
  decide +kernel

theorem triangle_update_017 :
    triangleStep triangleLocal144 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal024 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_017 triangle_mirror_00167

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_018 :
    (triangleStep triangleLocal144 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal023.state := by
  decide +kernel

theorem triangle_update_018 :
    triangleStep triangleLocal144 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal023 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_018 triangle_mirror_00163

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_019 :
    (triangleStep triangleLocal144 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal022.state := by
  decide +kernel

theorem triangle_update_019 :
    triangleStep triangleLocal144 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal022 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_019 triangle_mirror_00155

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_020 :
    (triangleStep triangleLocal146 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal002.state := by
  decide +kernel

theorem triangle_update_020 :
    triangleStep triangleLocal146 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal002 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_020 triangle_mirror_00035

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_021 :
    (triangleStep triangleLocal146 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal030.state := by
  decide +kernel

theorem triangle_update_021 :
    triangleStep triangleLocal146 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal030 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_021 triangle_mirror_00182

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_022 :
    (triangleStep triangleLocal146 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal027.state := by
  decide +kernel

theorem triangle_update_022 :
    triangleStep triangleLocal146 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal027 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_022 triangle_mirror_00180

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_023 :
    (triangleStep triangleLocal146 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal012.state := by
  decide +kernel

theorem triangle_update_023 :
    triangleStep triangleLocal146 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal012 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_023 triangle_mirror_00109

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_024 :
    (triangleStep triangleLocal147 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal001.state := by
  decide +kernel

theorem triangle_update_024 :
    triangleStep triangleLocal147 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal001 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_024 triangle_mirror_00035

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_025 :
    (triangleStep triangleLocal147 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal029.state := by
  decide +kernel

theorem triangle_update_025 :
    triangleStep triangleLocal147 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal029 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_025 triangle_mirror_00182

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_026 :
    (triangleStep triangleLocal147 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal011.state := by
  decide +kernel

theorem triangle_update_026 :
    triangleStep triangleLocal147 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal011 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_026 triangle_mirror_00109

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_027 :
    (triangleStep triangleLocal147 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal028.state := by
  decide +kernel

theorem triangle_update_027 :
    triangleStep triangleLocal147 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal028 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_027 triangle_mirror_00180

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_028 :
    (triangleStep triangleLocal148 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal007.state := by
  decide +kernel

theorem triangle_update_028 :
    triangleStep triangleLocal148 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal007 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_028 triangle_mirror_00049

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_029 :
    (triangleStep triangleLocal148 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal025.state := by
  decide +kernel

theorem triangle_update_029 :
    triangleStep triangleLocal148 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal025 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_029 triangle_mirror_00176

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_030 :
    (triangleStep triangleLocal148 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal029.state := by
  decide +kernel

theorem triangle_update_030 :
    triangleStep triangleLocal148 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal029 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_030 triangle_mirror_00182

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_031 :
    (triangleStep triangleLocal148 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal016.state := by
  decide +kernel

theorem triangle_update_031 :
    triangleStep triangleLocal148 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal016 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_031 triangle_mirror_00115

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_032 :
    (triangleStep triangleLocal149 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal006.state := by
  decide +kernel

theorem triangle_update_032 :
    triangleStep triangleLocal149 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal006 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_032 triangle_mirror_00049

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_033 :
    (triangleStep triangleLocal149 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal026.state := by
  decide +kernel

theorem triangle_update_033 :
    triangleStep triangleLocal149 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal026 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_033 triangle_mirror_00176

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_034 :
    (triangleStep triangleLocal149 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal015.state := by
  decide +kernel

theorem triangle_update_034 :
    triangleStep triangleLocal149 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal015 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_034 triangle_mirror_00115

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_035 :
    (triangleStep triangleLocal149 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal030.state := by
  decide +kernel

theorem triangle_update_035 :
    triangleStep triangleLocal149 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal030 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_035 triangle_mirror_00182

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_036 :
    (triangleStep triangleLocal150 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal017.state := by
  decide +kernel

theorem triangle_update_036 :
    triangleStep triangleLocal150 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal017 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_036 triangle_mirror_00122

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_037 :
    (triangleStep triangleLocal150 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal033.state := by
  decide +kernel

theorem triangle_update_037 :
    triangleStep triangleLocal150 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal033 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_037 triangle_mirror_00225

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_038 :
    (triangleStep triangleLocal150 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal031.state := by
  decide +kernel

theorem triangle_update_038 :
    triangleStep triangleLocal150 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal031 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_038 triangle_mirror_00194

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_039 :
    (triangleStep triangleLocal150 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal032.state := by
  decide +kernel

theorem triangle_update_039 :
    triangleStep triangleLocal150 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal032 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_039 triangle_mirror_00209

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_040 :
    (triangleStep triangleLocal151 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal019.state := by
  decide +kernel

theorem triangle_update_040 :
    triangleStep triangleLocal151 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal019 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_040 triangle_mirror_00146

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_041 :
    (triangleStep triangleLocal151 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal034.state := by
  decide +kernel

theorem triangle_update_041 :
    triangleStep triangleLocal151 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal034 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_041 triangle_mirror_00245

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_042 :
    (triangleStep triangleLocal151 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal036.state := by
  decide +kernel

theorem triangle_update_042 :
    triangleStep triangleLocal151 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal036 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_042 triangle_mirror_00256

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_043 :
    (triangleStep triangleLocal151 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal035.state := by
  decide +kernel

theorem triangle_update_043 :
    triangleStep triangleLocal151 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal035 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_043 triangle_mirror_00252

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_044 :
    (triangleStep triangleLocal152 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal008.state := by
  decide +kernel

theorem triangle_update_044 :
    triangleStep triangleLocal152 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal008 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_044 triangle_mirror_00072

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_045 :
    (triangleStep triangleLocal152 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal035.state := by
  decide +kernel

theorem triangle_update_045 :
    triangleStep triangleLocal152 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal035 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_045 triangle_mirror_00252

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_046 :
    (triangleStep triangleLocal152 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal032.state := by
  decide +kernel

theorem triangle_update_046 :
    triangleStep triangleLocal152 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal032 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_046 triangle_mirror_00209

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_047 :
    (triangleStep triangleLocal152 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal022.state := by
  decide +kernel

theorem triangle_update_047 :
    triangleStep triangleLocal152 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal022 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_047 triangle_mirror_00155

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_048 :
    (triangleStep triangleLocal153 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal009.state := by
  decide +kernel

theorem triangle_update_048 :
    triangleStep triangleLocal153 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal009 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_048 triangle_mirror_00088

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_049 :
    (triangleStep triangleLocal153 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal036.state := by
  decide +kernel

theorem triangle_update_049 :
    triangleStep triangleLocal153 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal036 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_049 triangle_mirror_00256

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_050 :
    (triangleStep triangleLocal153 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal031.state := by
  decide +kernel

theorem triangle_update_050 :
    triangleStep triangleLocal153 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal031 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_050 triangle_mirror_00194

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_051 :
    (triangleStep triangleLocal153 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal023.state := by
  decide +kernel

theorem triangle_update_051 :
    triangleStep triangleLocal153 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal023 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_051 triangle_mirror_00163

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_052 :
    (triangleStep triangleLocal154 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal010.state := by
  decide +kernel

theorem triangle_update_052 :
    triangleStep triangleLocal154 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal010 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_052 triangle_mirror_00102

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_053 :
    (triangleStep triangleLocal154 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal034.state := by
  decide +kernel

theorem triangle_update_053 :
    triangleStep triangleLocal154 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal034 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_053 triangle_mirror_00245

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_054 :
    (triangleStep triangleLocal154 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal033.state := by
  decide +kernel

theorem triangle_update_054 :
    triangleStep triangleLocal154 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal033 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_054 triangle_mirror_00225

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_055 :
    (triangleStep triangleLocal154 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal024.state := by
  decide +kernel

theorem triangle_update_055 :
    triangleStep triangleLocal154 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal024 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_055 triangle_mirror_00167

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_056 :
    (triangleStep triangleLocal156 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal039.state := by
  decide +kernel

theorem triangle_update_056 :
    triangleStep triangleLocal156 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal039 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_056 triangle_mirror_00470

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_057 :
    (triangleStep triangleLocal156 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal042.state := by
  decide +kernel

theorem triangle_update_057 :
    triangleStep triangleLocal156 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal042 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_057 triangle_mirror_00612

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_058 :
    (triangleStep triangleLocal156 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal044.state := by
  decide +kernel

theorem triangle_update_058 :
    triangleStep triangleLocal156 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal044 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_058 triangle_mirror_00620

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_059 :
    (triangleStep triangleLocal156 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal043.state := by
  decide +kernel

theorem triangle_update_059 :
    triangleStep triangleLocal156 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal043 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_059 triangle_mirror_00616

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_060 :
    (triangleStep triangleLocal157 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal040.state := by
  decide +kernel

theorem triangle_update_060 :
    triangleStep triangleLocal157 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal040 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_060 triangle_mirror_00486

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_061 :
    (triangleStep triangleLocal157 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal046.state := by
  decide +kernel

theorem triangle_update_061 :
    triangleStep triangleLocal157 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal046 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_061 triangle_mirror_00687

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_062 :
    (triangleStep triangleLocal157 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal048.state := by
  decide +kernel

theorem triangle_update_062 :
    triangleStep triangleLocal157 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal048 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_062 triangle_mirror_00695

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_063 :
    (triangleStep triangleLocal157 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal047.state := by
  decide +kernel

theorem triangle_update_063 :
    triangleStep triangleLocal157 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal047 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_063 triangle_mirror_00691

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_064 :
    (triangleStep triangleLocal158 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal041.state := by
  decide +kernel

theorem triangle_update_064 :
    triangleStep triangleLocal158 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal041 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_064 triangle_mirror_00501

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_065 :
    (triangleStep triangleLocal158 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal049.state := by
  decide +kernel

theorem triangle_update_065 :
    triangleStep triangleLocal158 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal049 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_065 triangle_mirror_00699

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_066 :
    (triangleStep triangleLocal158 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal050.state := by
  decide +kernel

theorem triangle_update_066 :
    triangleStep triangleLocal158 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal050 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_066 triangle_mirror_00702

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_067 :
    (triangleStep triangleLocal158 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal051.state := by
  decide +kernel

theorem triangle_update_067 :
    triangleStep triangleLocal158 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal051 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_067 triangle_mirror_00706

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_068 :
    (triangleStep triangleLocal159 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal080.state := by
  decide +kernel

theorem triangle_update_068 :
    triangleStep triangleLocal159 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal080 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_068 triangle_mirror_03311

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_069 :
    (triangleStep triangleLocal159 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal086.state := by
  decide +kernel

theorem triangle_update_069 :
    triangleStep triangleLocal159 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal086 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_069 triangle_mirror_03660

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_070 :
    (triangleStep triangleLocal159 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal084.state := by
  decide +kernel

theorem triangle_update_070 :
    triangleStep triangleLocal159 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal084 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_070 triangle_mirror_03575

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_071 :
    (triangleStep triangleLocal159 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal088.state := by
  decide +kernel

theorem triangle_update_071 :
    triangleStep triangleLocal159 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal088 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_071 triangle_mirror_03720

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_072 :
    (triangleStep triangleLocal160 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal079.state := by
  decide +kernel

theorem triangle_update_072 :
    triangleStep triangleLocal160 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal079 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_072 triangle_mirror_03311

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_073 :
    (triangleStep triangleLocal160 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal087.state := by
  decide +kernel

theorem triangle_update_073 :
    triangleStep triangleLocal160 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal087 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_073 triangle_mirror_03660

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_074 :
    (triangleStep triangleLocal160 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal085.state := by
  decide +kernel

theorem triangle_update_074 :
    triangleStep triangleLocal160 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal085 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_074 triangle_mirror_03575

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_075 :
    (triangleStep triangleLocal160 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal089.state := by
  decide +kernel

theorem triangle_update_075 :
    triangleStep triangleLocal160 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal089 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_075 triangle_mirror_03720

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_076 :
    (triangleStep triangleLocal161 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal095.state := by
  decide +kernel

theorem triangle_update_076 :
    triangleStep triangleLocal161 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal095 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_076 triangle_mirror_03986

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_077 :
    (triangleStep triangleLocal161 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal094.state := by
  decide +kernel

theorem triangle_update_077 :
    triangleStep triangleLocal161 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal094 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_077 triangle_mirror_03955

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_078 :
    (triangleStep triangleLocal161 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal096.state := by
  decide +kernel

theorem triangle_update_078 :
    triangleStep triangleLocal161 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal096 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_078 triangle_mirror_04018

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_079 :
    (triangleStep triangleLocal161 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal093.state := by
  decide +kernel

theorem triangle_update_079 :
    triangleStep triangleLocal161 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal093 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_079 triangle_mirror_03944

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_080 :
    (triangleStep triangleLocal162 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal101.state := by
  decide +kernel

theorem triangle_update_080 :
    triangleStep triangleLocal162 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal101 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_080 triangle_mirror_04090

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_081 :
    (triangleStep triangleLocal162 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal097.state := by
  decide +kernel

theorem triangle_update_081 :
    triangleStep triangleLocal162 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal097 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_081 triangle_mirror_04041

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_082 :
    (triangleStep triangleLocal162 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal102.state := by
  decide +kernel

theorem triangle_update_082 :
    triangleStep triangleLocal162 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal102 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_082 triangle_mirror_04137

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_083 :
    (triangleStep triangleLocal162 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal094.state := by
  decide +kernel

theorem triangle_update_083 :
    triangleStep triangleLocal162 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal094 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_083 triangle_mirror_03955

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_084 :
    (triangleStep triangleLocal163 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal116.state := by
  decide +kernel

theorem triangle_update_084 :
    triangleStep triangleLocal163 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal116 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_084 triangle_mirror_04238

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_085 :
    (triangleStep triangleLocal163 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal112.state := by
  decide +kernel

theorem triangle_update_085 :
    triangleStep triangleLocal163 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal112 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_085 triangle_mirror_04211

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_086 :
    (triangleStep triangleLocal163 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal106.state := by
  decide +kernel

theorem triangle_update_086 :
    triangleStep triangleLocal163 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal106 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_086 triangle_mirror_04184

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_087 :
    (triangleStep triangleLocal163 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal110.state := by
  decide +kernel

theorem triangle_update_087 :
    triangleStep triangleLocal163 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal110 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_087 triangle_mirror_04187

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_088 :
    (triangleStep triangleLocal164 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal117.state := by
  decide +kernel

theorem triangle_update_088 :
    triangleStep triangleLocal164 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal117 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_088 triangle_mirror_04238

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_089 :
    (triangleStep triangleLocal164 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal114.state := by
  decide +kernel

theorem triangle_update_089 :
    triangleStep triangleLocal164 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal114 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_089 triangle_mirror_04211

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_090 :
    (triangleStep triangleLocal164 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal108.state := by
  decide +kernel

theorem triangle_update_090 :
    triangleStep triangleLocal164 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal108 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_090 triangle_mirror_04184

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_091 :
    (triangleStep triangleLocal164 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal111.state := by
  decide +kernel

theorem triangle_update_091 :
    triangleStep triangleLocal164 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal111 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_091 triangle_mirror_04187

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_092 :
    (triangleStep triangleLocal168 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal081.state := by
  decide +kernel

theorem triangle_update_092 :
    triangleStep triangleLocal168 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal081 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_092 triangle_mirror_03327

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_093 :
    (triangleStep triangleLocal168 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal098.state := by
  decide +kernel

theorem triangle_update_093 :
    triangleStep triangleLocal168 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal098 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_093 triangle_mirror_04041

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_094 :
    (triangleStep triangleLocal168 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal090.state := by
  decide +kernel

theorem triangle_update_094 :
    triangleStep triangleLocal168 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal090 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_094 triangle_mirror_03774

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_095 :
    (triangleStep triangleLocal168 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal103.state := by
  decide +kernel

theorem triangle_update_095 :
    triangleStep triangleLocal168 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal103 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_095 triangle_mirror_04173

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_096 :
    (triangleStep triangleLocal169 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal082.state := by
  decide +kernel

theorem triangle_update_096 :
    triangleStep triangleLocal169 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal082 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_096 triangle_mirror_03343

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_097 :
    (triangleStep triangleLocal169 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal099.state := by
  decide +kernel

theorem triangle_update_097 :
    triangleStep triangleLocal169 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal099 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_097 triangle_mirror_04053

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_098 :
    (triangleStep triangleLocal169 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal091.state := by
  decide +kernel

theorem triangle_update_098 :
    triangleStep triangleLocal169 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal091 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_098 triangle_mirror_03790

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_099 :
    (triangleStep triangleLocal169 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal104.state := by
  decide +kernel

theorem triangle_update_099 :
    triangleStep triangleLocal169 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal104 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_099 triangle_mirror_04177

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_100 :
    (triangleStep triangleLocal170 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal083.state := by
  decide +kernel

theorem triangle_update_100 :
    triangleStep triangleLocal170 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal083 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_100 triangle_mirror_03343

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_101 :
    (triangleStep triangleLocal170 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal100.state := by
  decide +kernel

theorem triangle_update_101 :
    triangleStep triangleLocal170 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal100 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_101 triangle_mirror_04053

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_102 :
    (triangleStep triangleLocal170 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal092.state := by
  decide +kernel

theorem triangle_update_102 :
    triangleStep triangleLocal170 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal092 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_102 triangle_mirror_03790

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_103 :
    (triangleStep triangleLocal170 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal105.state := by
  decide +kernel

theorem triangle_update_103 :
    triangleStep triangleLocal170 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal105 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_103 triangle_mirror_04177

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_104 :
    (triangleStep triangleLocal171 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal121.state := by
  decide +kernel

theorem triangle_update_104 :
    triangleStep triangleLocal171 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal121 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_104 triangle_mirror_04425

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_105 :
    (triangleStep triangleLocal171 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal097.state := by
  decide +kernel

theorem triangle_update_105 :
    triangleStep triangleLocal171 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal097 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_105 triangle_mirror_04041

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_106 :
    (triangleStep triangleLocal171 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal123.state := by
  decide +kernel

theorem triangle_update_106 :
    triangleStep triangleLocal171 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal123 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_106 triangle_mirror_04445

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_107 :
    (triangleStep triangleLocal171 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal120.state := by
  decide +kernel

theorem triangle_update_107 :
    triangleStep triangleLocal171 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal120 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_107 triangle_mirror_04406

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_108 :
    (triangleStep triangleLocal172 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal124.state := by
  decide +kernel

theorem triangle_update_108 :
    triangleStep triangleLocal172 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal124 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_108 triangle_mirror_04465

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_109 :
    (triangleStep triangleLocal172 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal120.state := by
  decide +kernel

theorem triangle_update_109 :
    triangleStep triangleLocal172 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal120 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_109 triangle_mirror_04406

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_110 :
    (triangleStep triangleLocal172 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal125.state := by
  decide +kernel

theorem triangle_update_110 :
    triangleStep triangleLocal172 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal125 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_110 triangle_mirror_04492

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_111 :
    (triangleStep triangleLocal172 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal093.state := by
  decide +kernel

theorem triangle_update_111 :
    triangleStep triangleLocal172 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal093 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_111 triangle_mirror_03944

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_112 :
    (triangleStep triangleLocal173 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal131.state := by
  decide +kernel

theorem triangle_update_112 :
    triangleStep triangleLocal173 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal131 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_112 triangle_mirror_04541

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_113 :
    (triangleStep triangleLocal173 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal128.state := by
  decide +kernel

theorem triangle_update_113 :
    triangleStep triangleLocal173 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal128 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_113 triangle_mirror_04526

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_114 :
    (triangleStep triangleLocal173 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal126.state := by
  decide +kernel

theorem triangle_update_114 :
    triangleStep triangleLocal173 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal126 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_114 triangle_mirror_04514

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_115 :
    (triangleStep triangleLocal173 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal109.state := by
  decide +kernel

theorem triangle_update_115 :
    triangleStep triangleLocal173 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal109 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_115 triangle_mirror_04184

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_116 :
    (triangleStep triangleLocal174 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal132.state := by
  decide +kernel

theorem triangle_update_116 :
    triangleStep triangleLocal174 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal132 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_116 triangle_mirror_04541

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_117 :
    (triangleStep triangleLocal174 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal129.state := by
  decide +kernel

theorem triangle_update_117 :
    triangleStep triangleLocal174 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal129 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_117 triangle_mirror_04526

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_118 :
    (triangleStep triangleLocal174 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal127.state := by
  decide +kernel

theorem triangle_update_118 :
    triangleStep triangleLocal174 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal127 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_118 triangle_mirror_04514

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_119 :
    (triangleStep triangleLocal174 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal107.state := by
  decide +kernel

theorem triangle_update_119 :
    triangleStep triangleLocal174 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal107 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_119 triangle_mirror_04184

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_120 :
    (triangleStep triangleLocal175 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal133.state := by
  decide +kernel

theorem triangle_update_120 :
    triangleStep triangleLocal175 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal133 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_120 triangle_mirror_04546

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_121 :
    (triangleStep triangleLocal175 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal101.state := by
  decide +kernel

theorem triangle_update_121 :
    triangleStep triangleLocal175 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal101 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_121 triangle_mirror_04090

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_122 :
    (triangleStep triangleLocal175 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal134.state := by
  decide +kernel

theorem triangle_update_122 :
    triangleStep triangleLocal175 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal134 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_122 triangle_mirror_04550

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_123 :
    (triangleStep triangleLocal175 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal124.state := by
  decide +kernel

theorem triangle_update_123 :
    triangleStep triangleLocal175 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal124 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_123 triangle_mirror_04465

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_124 :
    (triangleStep triangleLocal176 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal135.state := by
  decide +kernel

theorem triangle_update_124 :
    triangleStep triangleLocal176 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal135 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_124 triangle_mirror_04560

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_125 :
    (triangleStep triangleLocal176 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal102.state := by
  decide +kernel

theorem triangle_update_125 :
    triangleStep triangleLocal176 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal102 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_125 triangle_mirror_04137

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_126 :
    (triangleStep triangleLocal176 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal136.state := by
  decide +kernel

theorem triangle_update_126 :
    triangleStep triangleLocal176 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal136 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_126 triangle_mirror_04564

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_127 :
    (triangleStep triangleLocal176 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal125.state := by
  decide +kernel

theorem triangle_update_127 :
    triangleStep triangleLocal176 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal125 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_127 triangle_mirror_04492

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_128 :
    (triangleStep triangleLocal178 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal134.state := by
  decide +kernel

theorem triangle_update_128 :
    triangleStep triangleLocal178 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal134 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_128 triangle_mirror_04550

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_129 :
    (triangleStep triangleLocal178 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal123.state := by
  decide +kernel

theorem triangle_update_129 :
    triangleStep triangleLocal178 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal123 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_129 triangle_mirror_04445

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_130 :
    (triangleStep triangleLocal178 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal136.state := by
  decide +kernel

theorem triangle_update_130 :
    triangleStep triangleLocal178 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal136 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_130 triangle_mirror_04564

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_131 :
    (triangleStep triangleLocal178 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal096.state := by
  decide +kernel

theorem triangle_update_131 :
    triangleStep triangleLocal178 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal096 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_131 triangle_mirror_04018

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_132 :
    (triangleStep triangleLocal179 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal138.state := by
  decide +kernel

theorem triangle_update_132 :
    triangleStep triangleLocal179 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal138 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_132 triangle_mirror_04584

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_133 :
    (triangleStep triangleLocal179 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal137.state := by
  decide +kernel

theorem triangle_update_133 :
    triangleStep triangleLocal179 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal137 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_133 triangle_mirror_04577

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_134 :
    (triangleStep triangleLocal179 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal130.state := by
  decide +kernel

theorem triangle_update_134 :
    triangleStep triangleLocal179 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal130 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_134 triangle_mirror_04526

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_135 :
    (triangleStep triangleLocal179 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal115.state := by
  decide +kernel

theorem triangle_update_135 :
    triangleStep triangleLocal179 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal115 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_135 triangle_mirror_04211

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_136 :
    (triangleStep triangleLocal184 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal060.state := by
  decide +kernel

theorem triangle_update_136 :
    triangleStep triangleLocal184 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal060 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_136 triangle_mirror_01595

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_137 :
    (triangleStep triangleLocal184 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal020.state := by
  decide +kernel

theorem triangle_update_137 :
    triangleStep triangleLocal184 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal020 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_137 triangle_mirror_00149

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_138 :
    (triangleStep triangleLocal184 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal064.state := by
  decide +kernel

theorem triangle_update_138 :
    triangleStep triangleLocal184 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal064 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_138 triangle_mirror_02024

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_139 :
    (triangleStep triangleLocal184 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal062.state := by
  decide +kernel

theorem triangle_update_139 :
    triangleStep triangleLocal184 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal062 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_139 triangle_mirror_01944

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_140 :
    (triangleStep triangleLocal185 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal066.state := by
  decide +kernel

theorem triangle_update_140 :
    triangleStep triangleLocal185 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal066 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_140 triangle_mirror_02281

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_141 :
    (triangleStep triangleLocal185 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal021.state := by
  decide +kernel

theorem triangle_update_141 :
    triangleStep triangleLocal185 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal021 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_141 triangle_mirror_00149

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_142 :
    (triangleStep triangleLocal185 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal069.state := by
  decide +kernel

theorem triangle_update_142 :
    triangleStep triangleLocal185 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal069 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_142 triangle_mirror_02866

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_143 :
    (triangleStep triangleLocal185 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal067.state := by
  decide +kernel

theorem triangle_update_143 :
    triangleStep triangleLocal185 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal067 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_143 triangle_mirror_02406

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_144 :
    (triangleStep triangleLocal187 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal058.state := by
  decide +kernel

theorem triangle_update_144 :
    triangleStep triangleLocal187 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal058 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_144 triangle_mirror_01393

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_145 :
    (triangleStep triangleLocal187 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal076.state := by
  decide +kernel

theorem triangle_update_145 :
    triangleStep triangleLocal187 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal076 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_145 triangle_mirror_03268

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_146 :
    (triangleStep triangleLocal187 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal038.state := by
  decide +kernel

theorem triangle_update_146 :
    triangleStep triangleLocal187 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal038 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_146 triangle_mirror_00428

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_147 :
    (triangleStep triangleLocal187 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal075.state := by
  decide +kernel

theorem triangle_update_147 :
    triangleStep triangleLocal187 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal075 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_147 triangle_mirror_03222

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_148 :
    (triangleStep triangleLocal188 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal037.state := by
  decide +kernel

theorem triangle_update_148 :
    triangleStep triangleLocal188 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal037 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_148 triangle_mirror_00381

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_149 :
    (triangleStep triangleLocal188 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal061.state := by
  decide +kernel

theorem triangle_update_149 :
    triangleStep triangleLocal188 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal061 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_149 triangle_mirror_01595

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_150 :
    (triangleStep triangleLocal188 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal077.state := by
  decide +kernel

theorem triangle_update_150 :
    triangleStep triangleLocal188 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal077 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_150 triangle_mirror_03299

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_151 :
    (triangleStep triangleLocal188 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal071.state := by
  decide +kernel

theorem triangle_update_151 :
    triangleStep triangleLocal188 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal071 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_151 triangle_mirror_02999

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_152 :
    (triangleStep triangleLocal189 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal073.state := by
  decide +kernel

theorem triangle_update_152 :
    triangleStep triangleLocal189 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal073 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_152 triangle_mirror_03149

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_153 :
    (triangleStep triangleLocal189 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal063.state := by
  decide +kernel

theorem triangle_update_153 :
    triangleStep triangleLocal189 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal063 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_153 triangle_mirror_01944

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_154 :
    (triangleStep triangleLocal189 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal113.state := by
  decide +kernel

theorem triangle_update_154 :
    triangleStep triangleLocal189 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal113 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_154 triangle_mirror_04211

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_155 :
    (triangleStep triangleLocal189 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal052.state := by
  decide +kernel

theorem triangle_update_155 :
    triangleStep triangleLocal189 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal052 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_155 triangle_mirror_00897

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_156 :
    (triangleStep triangleLocal190 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal072.state := by
  decide +kernel

theorem triangle_update_156 :
    triangleStep triangleLocal190 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal072 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_156 triangle_mirror_02999

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_157 :
    (triangleStep triangleLocal190 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal068.state := by
  decide +kernel

theorem triangle_update_157 :
    triangleStep triangleLocal190 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal068 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_157 triangle_mirror_02406

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_158 :
    (triangleStep triangleLocal190 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal129.state := by
  decide +kernel

theorem triangle_update_158 :
    triangleStep triangleLocal190 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal129 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_158 triangle_mirror_04526

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_159 :
    (triangleStep triangleLocal190 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal053.state := by
  decide +kernel

theorem triangle_update_159 :
    triangleStep triangleLocal190 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal053 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_159 triangle_mirror_00897

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_160 :
    (triangleStep triangleLocal191 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal057.state := by
  decide +kernel

theorem triangle_update_160 :
    triangleStep triangleLocal191 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal057 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_160 triangle_mirror_01313

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_161 :
    (triangleStep triangleLocal191 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal122.state := by
  decide +kernel

theorem triangle_update_161 :
    triangleStep triangleLocal191 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal122 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_161 triangle_mirror_04444

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_162 :
    (triangleStep triangleLocal191 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal118.state := by
  decide +kernel

theorem triangle_update_162 :
    triangleStep triangleLocal191 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal118 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_162 triangle_mirror_04291

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_163 :
    (triangleStep triangleLocal191 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal045.state := by
  decide +kernel

theorem triangle_update_163 :
    triangleStep triangleLocal191 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal045 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_163 triangle_mirror_00663

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_164 :
    (triangleStep triangleLocal192 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal059.state := by
  decide +kernel

theorem triangle_update_164 :
    triangleStep triangleLocal192 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal059 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_164 triangle_mirror_01431

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_165 :
    (triangleStep triangleLocal192 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal054.state := by
  decide +kernel

theorem triangle_update_165 :
    triangleStep triangleLocal192 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal054 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_165 triangle_mirror_01088

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_166 :
    (triangleStep triangleLocal192 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal119.state := by
  decide +kernel

theorem triangle_update_166 :
    triangleStep triangleLocal192 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal119 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_166 triangle_mirror_04324

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_167 :
    (triangleStep triangleLocal192 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal096.state := by
  decide +kernel

theorem triangle_update_167 :
    triangleStep triangleLocal192 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal096 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_167 triangle_mirror_04018

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_168 :
    (triangleStep triangleLocal193 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal078.state := by
  decide +kernel

theorem triangle_update_168 :
    triangleStep triangleLocal193 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal078 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_168 triangle_mirror_03299

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_169 :
    (triangleStep triangleLocal193 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal070.state := by
  decide +kernel

theorem triangle_update_169 :
    triangleStep triangleLocal193 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal070 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_169 triangle_mirror_02866

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_170 :
    (triangleStep triangleLocal193 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal055.state := by
  decide +kernel

theorem triangle_update_170 :
    triangleStep triangleLocal193 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal055 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_170 triangle_mirror_01168

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_171 :
    (triangleStep triangleLocal193 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal115.state := by
  decide +kernel

theorem triangle_update_171 :
    triangleStep triangleLocal193 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal115 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_171 triangle_mirror_04211

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_172 :
    (triangleStep triangleLocal194 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal074.state := by
  decide +kernel

theorem triangle_update_172 :
    triangleStep triangleLocal194 (⟨1, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal074 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_172 triangle_mirror_03157

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_173 :
    (triangleStep triangleLocal194 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal065.state := by
  decide +kernel

theorem triangle_update_173 :
    triangleStep triangleLocal194 (⟨1, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal065 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_173 triangle_mirror_02024

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_174 :
    (triangleStep triangleLocal194 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal056.state := by
  decide +kernel

theorem triangle_update_174 :
    triangleStep triangleLocal194 (⟨1, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal056 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_174 triangle_mirror_01168

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_175 :
    (triangleStep triangleLocal194 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal128.state := by
  decide +kernel

theorem triangle_update_175 :
    triangleStep triangleLocal194 (⟨1, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal128 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_175 triangle_mirror_04526

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_176 :
    (triangleStep triangleLocal195 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal139.state := by
  decide +kernel

theorem triangle_update_176 :
    triangleStep triangleLocal195 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal139 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_176 triangle_mirror_04634

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_177 :
    (triangleStep triangleLocal195 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal148.state := by
  decide +kernel

theorem triangle_update_177 :
    triangleStep triangleLocal195 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal148 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_177 triangle_mirror_04803

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_178 :
    (triangleStep triangleLocal195 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal142.state := by
  decide +kernel

theorem triangle_update_178 :
    triangleStep triangleLocal195 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal142 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_178 triangle_mirror_04726

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_179 :
    (triangleStep triangleLocal195 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal146.state := by
  decide +kernel

theorem triangle_update_179 :
    triangleStep triangleLocal195 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal146 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_179 triangle_mirror_04800

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_180 :
    (triangleStep triangleLocal196 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal140.state := by
  decide +kernel

theorem triangle_update_180 :
    triangleStep triangleLocal196 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal140 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_180 triangle_mirror_04634

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_181 :
    (triangleStep triangleLocal196 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal149.state := by
  decide +kernel

theorem triangle_update_181 :
    triangleStep triangleLocal196 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal149 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_181 triangle_mirror_04803

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_182 :
    (triangleStep triangleLocal196 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal147.state := by
  decide +kernel

theorem triangle_update_182 :
    triangleStep triangleLocal196 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal147 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_182 triangle_mirror_04800

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_183 :
    (triangleStep triangleLocal196 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal143.state := by
  decide +kernel

theorem triangle_update_183 :
    triangleStep triangleLocal196 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal143 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_183 triangle_mirror_04726

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_184 :
    (triangleStep triangleLocal197 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal145.state := by
  decide +kernel

theorem triangle_update_184 :
    triangleStep triangleLocal197 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal145 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_184 triangle_mirror_04774

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_185 :
    (triangleStep triangleLocal197 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal154.state := by
  decide +kernel

theorem triangle_update_185 :
    triangleStep triangleLocal197 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal154 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_185 triangle_mirror_04948

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_186 :
    (triangleStep triangleLocal197 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal153.state := by
  decide +kernel

theorem triangle_update_186 :
    triangleStep triangleLocal197 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal153 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_186 triangle_mirror_04944

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_187 :
    (triangleStep triangleLocal197 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal152.state := by
  decide +kernel

theorem triangle_update_187 :
    triangleStep triangleLocal197 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal152 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_187 triangle_mirror_04940

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_188 :
    (triangleStep triangleLocal197 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal141.state := by
  decide +kernel

theorem triangle_update_188 :
    triangleStep triangleLocal197 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal141 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_188 triangle_mirror_04684

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_189 :
    (triangleStep triangleLocal197 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal151.state := by
  decide +kernel

theorem triangle_update_189 :
    triangleStep triangleLocal197 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal151 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_189 triangle_mirror_04871

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_190 :
    (triangleStep triangleLocal197 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal150.state := by
  decide +kernel

theorem triangle_update_190 :
    triangleStep triangleLocal197 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal150 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_190 triangle_mirror_04841

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_191 :
    (triangleStep triangleLocal197 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal144.state := by
  decide +kernel

theorem triangle_update_191 :
    triangleStep triangleLocal197 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal144 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_191 triangle_mirror_04762

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_192 :
    (triangleStep triangleLocal198 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal155.state := by
  decide +kernel

theorem triangle_update_192 :
    triangleStep triangleLocal198 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal155 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_192 triangle_mirror_05140

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_193 :
    (triangleStep triangleLocal198 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal156.state := by
  decide +kernel

theorem triangle_update_193 :
    triangleStep triangleLocal198 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal156 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_193 triangle_mirror_05417

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_194 :
    (triangleStep triangleLocal198 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal158.state := by
  decide +kernel

theorem triangle_update_194 :
    triangleStep triangleLocal198 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal158 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_194 triangle_mirror_05499

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_195 :
    (triangleStep triangleLocal198 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal157.state := by
  decide +kernel

theorem triangle_update_195 :
    triangleStep triangleLocal198 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal157 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_195 triangle_mirror_05492

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_196 :
    (triangleStep triangleLocal199 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal165.state := by
  decide +kernel

theorem triangle_update_196 :
    triangleStep triangleLocal199 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal165 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_196 triangle_mirror_11315

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_197 :
    (triangleStep triangleLocal199 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal167.state := by
  decide +kernel

theorem triangle_update_197 :
    triangleStep triangleLocal199 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal167 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_197 triangle_mirror_11319

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_198 :
    (triangleStep triangleLocal199 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal160.state := by
  decide +kernel

theorem triangle_update_198 :
    triangleStep triangleLocal199 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal160 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_198 triangle_mirror_10376

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_199 :
    (triangleStep triangleLocal199 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal169.state := by
  decide +kernel

theorem triangle_update_199 :
    triangleStep triangleLocal199 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal169 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_199 triangle_mirror_11323

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_200 :
    (triangleStep triangleLocal200 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal166.state := by
  decide +kernel

theorem triangle_update_200 :
    triangleStep triangleLocal200 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal166 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_200 triangle_mirror_11315

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_201 :
    (triangleStep triangleLocal200 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal168.state := by
  decide +kernel

theorem triangle_update_201 :
    triangleStep triangleLocal200 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal168 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_201 triangle_mirror_11319

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_202 :
    (triangleStep triangleLocal200 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal159.state := by
  decide +kernel

theorem triangle_update_202 :
    triangleStep triangleLocal200 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal159 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_202 triangle_mirror_10376

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_203 :
    (triangleStep triangleLocal200 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal170.state := by
  decide +kernel

theorem triangle_update_203 :
    triangleStep triangleLocal200 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal170 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_203 triangle_mirror_11323

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_204 :
    (triangleStep triangleLocal201 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal177.state := by
  decide +kernel

theorem triangle_update_204 :
    triangleStep triangleLocal201 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal177 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_204 triangle_mirror_11977

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_205 :
    (triangleStep triangleLocal201 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal162.state := by
  decide +kernel

theorem triangle_update_205 :
    triangleStep triangleLocal201 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal162 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_205 triangle_mirror_11067

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_206 :
    (triangleStep triangleLocal201 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal178.state := by
  decide +kernel

theorem triangle_update_206 :
    triangleStep triangleLocal201 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal178 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_206 triangle_mirror_12000

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_207 :
    (triangleStep triangleLocal201 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal172.state := by
  decide +kernel

theorem triangle_update_207 :
    triangleStep triangleLocal201 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal172 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_207 triangle_mirror_11806

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_208 :
    (triangleStep triangleLocal201 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal175.state := by
  decide +kernel

theorem triangle_update_208 :
    triangleStep triangleLocal201 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal175 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_208 triangle_mirror_11958

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_209 :
    (triangleStep triangleLocal201 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal171.state := by
  decide +kernel

theorem triangle_update_209 :
    triangleStep triangleLocal201 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal171 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_209 triangle_mirror_11707

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_210 :
    (triangleStep triangleLocal201 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal176.state := by
  decide +kernel

theorem triangle_update_210 :
    triangleStep triangleLocal201 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal176 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_210 triangle_mirror_11974

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_211 :
    (triangleStep triangleLocal201 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal161.state := by
  decide +kernel

theorem triangle_update_211 :
    triangleStep triangleLocal201 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal161 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_211 triangle_mirror_10893

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_212 :
    (triangleStep triangleLocal202 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal181.state := by
  decide +kernel

theorem triangle_update_212 :
    triangleStep triangleLocal202 (⟨5, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal181 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_212 triangle_mirror_12042

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_213 :
    (triangleStep triangleLocal202 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal179.state := by
  decide +kernel

theorem triangle_update_213 :
    triangleStep triangleLocal202 (⟨5, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal179 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_213 triangle_mirror_12033

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_214 :
    (triangleStep triangleLocal202 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal163.state := by
  decide +kernel

theorem triangle_update_214 :
    triangleStep triangleLocal202 (⟨5, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal163 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_214 triangle_mirror_11302

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_215 :
    (triangleStep triangleLocal202 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal173.state := by
  decide +kernel

theorem triangle_update_215 :
    triangleStep triangleLocal202 (⟨5, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal173 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_215 triangle_mirror_11917

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_216 :
    (triangleStep triangleLocal203 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal182.state := by
  decide +kernel

theorem triangle_update_216 :
    triangleStep triangleLocal203 (⟨8, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal182 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_216 triangle_mirror_12042

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_217 :
    (triangleStep triangleLocal203 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal180.state := by
  decide +kernel

theorem triangle_update_217 :
    triangleStep triangleLocal203 (⟨8, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal180 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_217 triangle_mirror_12033

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_218 :
    (triangleStep triangleLocal203 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal164.state := by
  decide +kernel

theorem triangle_update_218 :
    triangleStep triangleLocal203 (⟨8, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal164 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_218 triangle_mirror_11302

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_219 :
    (triangleStep triangleLocal203 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal174.state := by
  decide +kernel

theorem triangle_update_219 :
    triangleStep triangleLocal203 (⟨8, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal174 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_219 triangle_mirror_11917

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_220 :
    (triangleStep triangleLocal204 (⟨0, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal183.state := by
  decide +kernel

theorem triangle_update_220 :
    triangleStep triangleLocal204 (⟨0, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal183 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_220 triangle_mirror_13020

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_221 :
    (triangleStep triangleLocal204 (⟨0, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal192.state := by
  decide +kernel

theorem triangle_update_221 :
    triangleStep triangleLocal204 (⟨0, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal192 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_221 triangle_mirror_14697

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_222 :
    (triangleStep triangleLocal204 (⟨0, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal187.state := by
  decide +kernel

theorem triangle_update_222 :
    triangleStep triangleLocal204 (⟨0, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal187 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_222 triangle_mirror_13592

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_223 :
    (triangleStep triangleLocal204 (⟨0, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal191.state := by
  decide +kernel

theorem triangle_update_223 :
    triangleStep triangleLocal204 (⟨0, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal191 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_223 triangle_mirror_14680

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_224 :
    (triangleStep triangleLocal205 (⟨0, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal186.state := by
  decide +kernel

theorem triangle_update_224 :
    triangleStep triangleLocal205 (⟨0, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal186 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_224 triangle_mirror_13545

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_225 :
    (triangleStep triangleLocal205 (⟨0, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal184.state := by
  decide +kernel

theorem triangle_update_225 :
    triangleStep triangleLocal205 (⟨0, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal184 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_225 triangle_mirror_13076

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_226 :
    (triangleStep triangleLocal205 (⟨0, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal193.state := by
  decide +kernel

theorem triangle_update_226 :
    triangleStep triangleLocal205 (⟨0, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal193 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_226 triangle_mirror_14783

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_227 :
    (triangleStep triangleLocal205 (⟨0, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal190.state := by
  decide +kernel

theorem triangle_update_227 :
    triangleStep triangleLocal205 (⟨0, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal190 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_227 triangle_mirror_14663

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_228 :
    (triangleStep triangleLocal206 (⟨0, by decide⟩ : Fin 10) ⟨0, by decide⟩).state =
      triangleLocal188.state := by
  decide +kernel

theorem triangle_update_228 :
    triangleStep triangleLocal206 (⟨0, by decide⟩ : Fin 10) ⟨0, by decide⟩ = triangleLocal188 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_228 triangle_mirror_13631

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_229 :
    (triangleStep triangleLocal206 (⟨0, by decide⟩ : Fin 10) ⟨1, by decide⟩).state =
      triangleLocal185.state := by
  decide +kernel

theorem triangle_update_229 :
    triangleStep triangleLocal206 (⟨0, by decide⟩ : Fin 10) ⟨1, by decide⟩ = triangleLocal185 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_229 triangle_mirror_13346

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_230 :
    (triangleStep triangleLocal206 (⟨0, by decide⟩ : Fin 10) ⟨2, by decide⟩).state =
      triangleLocal194.state := by
  decide +kernel

theorem triangle_update_230 :
    triangleStep triangleLocal206 (⟨0, by decide⟩ : Fin 10) ⟨2, by decide⟩ = triangleLocal194 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_230 triangle_mirror_15127

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem triangle_state_231 :
    (triangleStep triangleLocal206 (⟨0, by decide⟩ : Fin 10) ⟨3, by decide⟩).state =
      triangleLocal189.state := by
  decide +kernel

theorem triangle_update_231 :
    triangleStep triangleLocal206 (⟨0, by decide⟩ : Fin 10) ⟨3, by decide⟩ = triangleLocal189 :=
  CanonicalCacheStateEqualityCandidate.triangleStep_eq_of_state_and_mirror _ _ _ _
    triangle_state_231 triangle_mirror_14201

def singletonLocal000 : CachedLocal 8689 :=
  ⟨(14, (0, 3)), ⟨18750, (3044532442067025), 0x0, 0x0⟩⟩

def singletonLocal001 : CachedLocal 8689 :=
  ⟨(14, (1, 3)), ⟨18750, (3044532442067025), 0x0, 0x0⟩⟩

def singletonLocal002 : CachedLocal 8689 :=
  ⟨(19, (0, 3)), ⟨956250, (4109339758928040), 0x0, 0x0⟩⟩

def singletonLocal003 : CachedLocal 8689 :=
  ⟨(19, (1, 3)), ⟨956250, (4109339758928040), 0x0, 0x0⟩⟩

def singletonLocal004 : CachedLocal 8689 :=
  ⟨(58, (1, 3)), ⟨19375, (2497112013709950), 0x0, 0x0⟩⟩

def singletonLocal005 : CachedLocal 8689 :=
  ⟨(58, (7, 3)), ⟨19375, (2497112013709950), 0x0, 0x0⟩⟩

def singletonLocal006 : CachedLocal 8689 :=
  ⟨(66, (1, 3)), ⟨956875, (-248521828135035), 0x0, 0x0⟩⟩

def singletonLocal007 : CachedLocal 8689 :=
  ⟨(66, (7, 3)), ⟨956875, (-248521828135035), 0x0, 0x0⟩⟩

def singletonLocal008 : CachedLocal 8689 :=
  ⟨(76, (7, 2)), ⟨191250, (-600117259449435), 0x0, 0x0⟩⟩

def singletonLocal009 : CachedLocal 8689 :=
  ⟨(96, (0, 2)), ⟨803750, (745552641499575), 0x0, 0x0⟩⟩

def singletonLocal010 : CachedLocal 8689 :=
  ⟨(98, (7, 0)), ⟨100625, (382814892610605), 0x0, 0x0⟩⟩

def singletonLocal011 : CachedLocal 8689 :=
  ⟨(110, (1, 1)), ⟨38125, (2280259602747945), 0x0, 0x0⟩⟩

def singletonLocal012 : CachedLocal 8689 :=
  ⟨(110, (1, 4)), ⟨38125, (2280259602747945), 0x0, 0x0⟩⟩

def singletonLocal013 : CachedLocal 8689 :=
  ⟨(110, (7, 1)), ⟨38125, (2280259602747945), 0x0, 0x0⟩⟩

def singletonLocal014 : CachedLocal 8689 :=
  ⟨(110, (7, 4)), ⟨38125, (2280259602747945), 0x0, 0x0⟩⟩

def singletonLocal015 : CachedLocal 8689 :=
  ⟨(115, (1, 1)), ⟨506875, (1071562126174995), 0x0, 0x0⟩⟩

def singletonLocal016 : CachedLocal 8689 :=
  ⟨(115, (7, 1)), ⟨506875, (1071562126174995), 0x0, 0x0⟩⟩

def singletonLocal017 : CachedLocal 8689 :=
  ⟨(125, (1, 4)), ⟨1444375, (-254342200779030), 0x0, 0x0⟩⟩

def singletonLocal018 : CachedLocal 8689 :=
  ⟨(125, (7, 4)), ⟨1444375, (-254342200779030), 0x0, 0x0⟩⟩

def singletonLocal019 : CachedLocal 8689 :=
  ⟨(138, (7, 5)), ⟨288125, (-1325334257069550), 0x0, 0x0⟩⟩

def singletonLocal020 : CachedLocal 8689 :=
  ⟨(142, (0, 3)), ⟨19500, (2843808400622280), 0x0, 0x0⟩⟩

def singletonLocal021 : CachedLocal 8689 :=
  ⟨(142, (4, 6)), ⟨19500, (2843808400622280), 0x0, 0x0⟩⟩

def singletonLocal022 : CachedLocal 8689 :=
  ⟨(145, (4, 8)), ⟨488250, (-749342940678150), 0x0, 0x0⟩⟩

def singletonLocal023 : CachedLocal 8689 :=
  ⟨(145, (4, 9)), ⟨488250, (-749342940678150), 0x0, 0x0⟩⟩

def singletonLocal024 : CachedLocal 8689 :=
  ⟨(147, (0, 3)), ⟨957000, (-2823845221965495), 0x0, 0x0⟩⟩

def singletonLocal025 : CachedLocal 8689 :=
  ⟨(147, (4, 9)), ⟨957000, (-2823845221965495), 0x0, 0x0⟩⟩

def singletonLocal026 : CachedLocal 8689 :=
  ⟨(149, (0, 3)), ⟨35125, (2574874744603980), 0x0, 0x0⟩⟩

def singletonLocal027 : CachedLocal 8689 :=
  ⟨(149, (0, 5)), ⟨35125, (2574874744603980), 0x0, 0x0⟩⟩

def singletonLocal028 : CachedLocal 8689 :=
  ⟨(149, (6, 3)), ⟨35125, (2574874744603980), 0x0, 0x0⟩⟩

def singletonLocal029 : CachedLocal 8689 :=
  ⟨(149, (6, 5)), ⟨35125, (2574874744603980), 0x0, 0x0⟩⟩

def singletonLocal030 : CachedLocal 8689 :=
  ⟨(150, (1, 0)), ⟨425750, (243138813022560), 0x0, 0x0⟩⟩

def singletonLocal031 : CachedLocal 8689 :=
  ⟨(156, (4, 11)), ⟨1285125, (618529171636740), 0x0, 0x0⟩⟩

def singletonLocal032 : CachedLocal 8689 :=
  ⟨(157, (7, 2)), ⟨191375, (519791355724095), 0x0, 0x0⟩⟩

def singletonLocal033 : CachedLocal 8689 :=
  ⟨(159, (0, 3)), ⟨972625, (-1403956526317800), 0x0, 0x0⟩⟩

def singletonLocal034 : CachedLocal 8689 :=
  ⟨(159, (6, 3)), ⟨972625, (-1403956526317800), 0x0, 0x0⟩⟩

def singletonLocal035 : CachedLocal 8689 :=
  ⟨(164, (0, 5)), ⟨1441375, (-2397996750533475), 0x0, 0x0⟩⟩

def singletonLocal036 : CachedLocal 8689 :=
  ⟨(164, (6, 5)), ⟨1441375, (-2397996750533475), 0x0, 0x0⟩⟩

def singletonLocal037 : CachedLocal 8689 :=
  ⟨(165, (0, 3)), ⟨38250, (2306063725057365), 0x0, 0x0⟩⟩

def singletonLocal038 : CachedLocal 8689 :=
  ⟨(165, (0, 5)), ⟨38250, (2306063725057365), 0x0, 0x0⟩⟩

def singletonLocal039 : CachedLocal 8689 :=
  ⟨(168, (1, 1)), ⟨507000, (-2088316202709555), 0x0, 0x0⟩⟩

def singletonLocal040 : CachedLocal 8689 :=
  ⟨(168, (4, 10)), ⟨507000, (-2088316202709555), 0x0, 0x0⟩⟩

def singletonLocal041 : CachedLocal 8689 :=
  ⟨(171, (0, 5)), ⟨1444500, (-2640919924324500), 0x0, 0x0⟩⟩

def singletonLocal042 : CachedLocal 8689 :=
  ⟨(172, (0, 3)), ⟨53875, (2306107857696825), 0x0, 0x0⟩⟩

def singletonLocal043 : CachedLocal 8689 :=
  ⟨(172, (0, 5)), ⟨53875, (2306107857696825), 0x0, 0x0⟩⟩

def singletonLocal044 : CachedLocal 8689 :=
  ⟨(174, (1, 3)), ⟨835125, (11073596151345), 0x0, 0x0⟩⟩

def singletonLocal045 : CachedLocal 8689 :=
  ⟨(179, (0, 3)), ⟨991375, (-285053766387390), 0x0, 0x0⟩⟩

def singletonLocal046 : CachedLocal 8689 :=
  ⟨(179, (6, 3)), ⟨991375, (-285053766387390), 0x0, 0x0⟩⟩

def singletonLocal047 : CachedLocal 8689 :=
  ⟨(183, (0, 0)), ⟨426375, (1372405588092630), 0x0, 0x0⟩⟩

def singletonLocal048 : CachedLocal 8689 :=
  ⟨(193, (0, 0)), ⟨442000, (2008923359129505), 0x0, 0x0⟩⟩

def singletonLocal049 : CachedLocal 8689 :=
  ⟨(198, (6, 2)), ⟨207625, (-95779776142050), 0x0, 0x0⟩⟩

def singletonLocal050 : CachedLocal 8689 :=
  ⟨(203, (0, 0)), ⟨413875, (1287055774501770), 0x0, 0x0⟩⟩

def singletonLocal051 : CachedLocal 8689 :=
  ⟨(210, (0, 0)), ⟨445125, (-379047749791620), 0x0, 0x0⟩⟩

def singletonLocal052 : CachedLocal 8689 :=
  ⟨(211, (1, 3)), ⟨835750, (-570628320280200), 0x0, 0x0⟩⟩

def singletonLocal053 : CachedLocal 8689 :=
  ⟨(375, (9, 8)), ⟨566900, (542978432078355), 0x0, 0x0⟩⟩

def singletonLocal054 : CachedLocal 8689 :=
  ⟨(465, (10, 2)), ⟨190775, (1320399989007645), 0x0, 0x0⟩⟩

def singletonLocal055 : CachedLocal 8689 :=
  ⟨(493, (4, 6)), ⟨19525, (1287735854562885), 0x0, 0x0⟩⟩

def singletonLocal056 : CachedLocal 8689 :=
  ⟨(493, (10, 6)), ⟨19525, (1287735854562885), 0x0, 0x0⟩⟩

def singletonLocal057 : CachedLocal 8689 :=
  ⟨(497, (4, 8)), ⟨488275, (-594470238080355), 0x0, 0x0⟩⟩

def singletonLocal058 : CachedLocal 8689 :=
  ⟨(497, (10, 8)), ⟨488275, (-594470238080355), 0x0, 0x0⟩⟩

def singletonLocal059 : CachedLocal 8689 :=
  ⟨(510, (4, 11)), ⟨1285150, (217171534105890), 0x0, 0x0⟩⟩

def singletonLocal060 : CachedLocal 8689 :=
  ⟨(537, (1, 2)), ⟨803900, (1708430708373480), 0x0, 0x0⟩⟩

def singletonLocal061 : CachedLocal 8689 :=
  ⟨(556, (4, 10)), ⟨507025, (-1379582934588495), 0x0, 0x0⟩⟩

def singletonLocal062 : CachedLocal 8689 :=
  ⟨(556, (10, 10)), ⟨507025, (-1379582934588495), 0x0, 0x0⟩⟩

def singletonLocal063 : CachedLocal 8689 :=
  ⟨(561, (5, 16)), ⟨975775, (-1667028171566940), 0x0, 0x0⟩⟩

def singletonLocal064 : CachedLocal 8689 :=
  ⟨(561, (11, 16)), ⟨975775, (-1667028171566940), 0x0, 0x0⟩⟩

def singletonLocal065 : CachedLocal 8689 :=
  ⟨(621, (1, 2)), ⟨804525, (2015366766415275), 0x0, 0x0⟩⟩

def singletonLocal066 : CachedLocal 8689 :=
  ⟨(649, (11, 17)), ⟨1054525, (-950098760977275), 0x0, 0x0⟩⟩

def singletonLocal067 : CachedLocal 8689 :=
  ⟨(686, (1, 4)), ⟨1198275, (1621720776585000), 0x0, 0x0⟩⟩

def singletonLocal068 : CachedLocal 8689 :=
  ⟨(733, (1, 2)), ⟨803400, (298096973729100), 0x0, 0x0⟩⟩

def singletonLocal069 : CachedLocal 8689 :=
  ⟨(753, (10, 5)), ⟨287775, (-831669947963400), 0x0, 0x0⟩⟩

def singletonLocal070 : CachedLocal 8689 :=
  ⟨(769, (0, 2)), ⟨804025, (2060520878035620), 0x0, 0x0⟩⟩

def singletonLocal071 : CachedLocal 8689 :=
  ⟨(785, (0, 2)), ⟨819650, (407858202034920), 0x0, 0x0⟩⟩

def singletonLocal072 : CachedLocal 8689 :=
  ⟨(791, (5, 12)), ⟨194650, (-1501634753612175), 0x0, 0x0⟩⟩

def singletonLocal073 : CachedLocal 8689 :=
  ⟨(794, (5, 17)), ⟨1366525, (76453180763505), 0x0, 0x0⟩⟩

def singletonLocal074 : CachedLocal 8689 :=
  ⟨(801, (0, 2)), ⟨835275, (1062458853932385), 0x0, 0x0⟩⟩

def singletonLocal075 : CachedLocal 8689 :=
  ⟨(817, (0, 2)), ⟨807150, (1494584781068925), 0x0, 0x0⟩⟩

def singletonLocal076 : CachedLocal 8689 :=
  ⟨(827, (0, 2)), ⟨822775, (-325806338977665), 0x0, 0x0⟩⟩

def singletonLocal077 : CachedLocal 8689 :=
  ⟨(843, (0, 2)), ⟨838400, (-368045628112890), 0x0, 0x0⟩⟩

def singletonLocal078 : CachedLocal 8689 :=
  ⟨(857, (4, 12)), ⟨39025, (196326233704965), 0x0, 0x0⟩⟩

def singletonLocal079 : CachedLocal 8689 :=
  ⟨(857, (4, 13)), ⟨39025, (196326233704965), 0x0, 0x0⟩⟩

def singletonLocal080 : CachedLocal 8689 :=
  ⟨(857, (10, 12)), ⟨39025, (196326233704965), 0x0, 0x0⟩⟩

def singletonLocal081 : CachedLocal 8689 :=
  ⟨(857, (10, 13)), ⟨39025, (196326233704965), 0x0, 0x0⟩⟩

def singletonLocal082 : CachedLocal 8689 :=
  ⟨(867, (4, 14)), ⟨976525, (-948365394964260), 0x0, 0x0⟩⟩

def singletonLocal083 : CachedLocal 8689 :=
  ⟨(867, (4, 16)), ⟨976525, (-948365394964260), 0x0, 0x0⟩⟩

def singletonLocal084 : CachedLocal 8689 :=
  ⟨(867, (10, 14)), ⟨976525, (-948365394964260), 0x0, 0x0⟩⟩

def singletonLocal085 : CachedLocal 8689 :=
  ⟨(867, (10, 16)), ⟨976525, (-948365394964260), 0x0, 0x0⟩⟩

def singletonLocal086 : CachedLocal 8689 :=
  ⟨(882, (4, 15)), ⟨601525, (-108237806764815), 0x0, 0x0⟩⟩

def singletonLocal087 : CachedLocal 8689 :=
  ⟨(895, (10, 15)), ⟨901525, (1107514372844880), 0x0, 0x0⟩⟩

def singletonLocal088 : CachedLocal 8689 :=
  ⟨(913, (4, 14)), ⟨995275, (-651058434611130), 0x0, 0x0⟩⟩

def singletonLocal089 : CachedLocal 8689 :=
  ⟨(913, (10, 14)), ⟨995275, (-651058434611130), 0x0, 0x0⟩⟩

def singletonLocal090 : CachedLocal 8689 :=
  ⟨(941, (0, 6)), ⟨19530, (1243398008111805), 0x0, 0x0⟩⟩

def singletonLocal091 : CachedLocal 8689 :=
  ⟨(944, (0, 8)), ⟨488280, (-114228225626970), 0x0, 0x0⟩⟩

def singletonLocal092 : CachedLocal 8689 :=
  ⟨(948, (0, 6)), ⟨35155, (382363804769310), 0x0, 0x0⟩⟩

def singletonLocal093 : CachedLocal 8689 :=
  ⟨(948, (0, 7)), ⟨35155, (382363804769310), 0x0, 0x0⟩⟩

def singletonLocal094 : CachedLocal 8689 :=
  ⟨(948, (6, 6)), ⟨35155, (382363804769310), 0x0, 0x0⟩⟩

def singletonLocal095 : CachedLocal 8689 :=
  ⟨(948, (6, 7)), ⟨35155, (382363804769310), 0x0, 0x0⟩⟩

def singletonLocal096 : CachedLocal 8689 :=
  ⟨(953, (0, 8)), ⟨503905, (-549565382241330), 0x0, 0x0⟩⟩

def singletonLocal097 : CachedLocal 8689 :=
  ⟨(953, (0, 10)), ⟨503905, (-549565382241330), 0x0, 0x0⟩⟩

def singletonLocal098 : CachedLocal 8689 :=
  ⟨(953, (6, 8)), ⟨503905, (-549565382241330), 0x0, 0x0⟩⟩

def singletonLocal099 : CachedLocal 8689 :=
  ⟨(953, (6, 10)), ⟨503905, (-549565382241330), 0x0, 0x0⟩⟩

def singletonLocal100 : CachedLocal 8689 :=
  ⟨(964, (0, 6)), ⟨38280, (-1730849495287185), 0x0, 0x0⟩⟩

def singletonLocal101 : CachedLocal 8689 :=
  ⟨(964, (0, 7)), ⟨38280, (-1730849495287185), 0x0, 0x0⟩⟩

def singletonLocal102 : CachedLocal 8689 :=
  ⟨(968, (0, 7)), ⟨507030, (-1147594754188155), 0x0, 0x0⟩⟩

def singletonLocal103 : CachedLocal 8689 :=
  ⟨(968, (0, 8)), ⟨507030, (-1147594754188155), 0x0, 0x0⟩⟩

def singletonLocal104 : CachedLocal 8689 :=
  ⟨(968, (0, 10)), ⟨507030, (-1147594754188155), 0x0, 0x0⟩⟩

def singletonLocal105 : CachedLocal 8689 :=
  ⟨(968, (1, 10)), ⟨507030, (-1147594754188155), 0x0, 0x0⟩⟩

def singletonLocal106 : CachedLocal 8689 :=
  ⟨(971, (3, 16)), ⟨975780, (-2221664782583610), 0x0, 0x0⟩⟩

def singletonLocal107 : CachedLocal 8689 :=
  ⟨(973, (0, 10)), ⟨1444530, (445354944349770), 0x0, 0x0⟩⟩

def singletonLocal108 : CachedLocal 8689 :=
  ⟨(974, (0, 6)), ⟨53905, (-646461464011545), 0x0, 0x0⟩⟩

def singletonLocal109 : CachedLocal 8689 :=
  ⟨(974, (0, 7)), ⟨53905, (-646461464011545), 0x0, 0x0⟩⟩

def singletonLocal110 : CachedLocal 8689 :=
  ⟨(978, (0, 8)), ⟨522655, (-1147801330716495), 0x0, 0x0⟩⟩

def singletonLocal111 : CachedLocal 8689 :=
  ⟨(978, (0, 10)), ⟨522655, (-1147801330716495), 0x0, 0x0⟩⟩

def singletonLocal112 : CachedLocal 8689 :=
  ⟨(1016, (0, 11)), ⟨1273280, (-236101648447665), 0x0, 0x0⟩⟩

def singletonLocal113 : CachedLocal 8689 :=
  ⟨(1024, (1, 10)), ⟨507655, (-1413962239765530), 0x0, 0x0⟩⟩

def singletonLocal114 : CachedLocal 8689 :=
  ⟨(1024, (7, 10)), ⟨507655, (-1413962239765530), 0x0, 0x0⟩⟩

def singletonLocal115 : CachedLocal 8689 :=
  ⟨(1026, (0, 11)), ⟨1288905, (-222186094783380), 0x0, 0x0⟩⟩

def singletonLocal116 : CachedLocal 8689 :=
  ⟨(1037, (0, 11)), ⟨1304530, (-1491883431710490), 0x0, 0x0⟩⟩

def singletonLocal117 : CachedLocal 8689 :=
  ⟨(1052, (0, 11)), ⟨1276405, (496518215132940), 0x0, 0x0⟩⟩

def singletonLocal118 : CachedLocal 8689 :=
  ⟨(1063, (0, 11)), ⟨1292030, (213103673046810), 0x0, 0x0⟩⟩

def singletonLocal119 : CachedLocal 8689 :=
  ⟨(1077, (1, 8)), ⟨526405, (298777528935795), 0x0, 0x0⟩⟩

def singletonLocal120 : CachedLocal 8689 :=
  ⟨(1077, (7, 8)), ⟨526405, (298777528935795), 0x0, 0x0⟩⟩

def singletonLocal121 : CachedLocal 8689 :=
  ⟨(1079, (0, 11)), ⟨1307655, (-606150161916390), 0x0, 0x0⟩⟩

def singletonLocal122 : CachedLocal 8689 :=
  ⟨(1087, (3, 22)), ⟨1463905, (-488583039386715), 0x0, 0x0⟩⟩

def singletonLocal123 : CachedLocal 8689 :=
  ⟨(1087, (9, 22)), ⟨1463905, (-488583039386715), 0x0, 0x0⟩⟩

def singletonLocal124 : CachedLocal 8689 :=
  ⟨(1090, (0, 10)), ⟨526530, (1870568673374310), 0x0, 0x0⟩⟩

def singletonLocal125 : CachedLocal 8689 :=
  ⟨(1351, (1, 3)), ⟨21250, (2280259602747945), 0x111100000, 0x1803700801b800007400000e⟩⟩

def singletonLocal126 : CachedLocal 8689 :=
  ⟨(1359, (1, 3)), ⟨958750, (-254342200779030), 0x111100000, 0x1803e80801cc000084000013⟩⟩

def singletonLocal127 : CachedLocal 8689 :=
  ⟨(1362, (1, 0)), ⟨427500, (414341703222720), 0x111100000, 0x18040008018000008a000016⟩⟩

def singletonLocal128 : CachedLocal 8689 :=
  ⟨(1388, (0, 3)), ⟨66375, (2497112013709950), 0x110000000, 0x804a800025400011ca8003a⟩⟩

def singletonLocal129 : CachedLocal 8689 :=
  ⟨(1396, (0, 3)), ⟨1003875, (-2823845221965495), 0x110000000, 0x8052000027c000126a80042⟩⟩

def singletonLocal130 : CachedLocal 8689 :=
  ⟨(1405, (0, 3)), ⟨69500, (2280259602747945), 0x110000000, 0x56000029520012aaa006e⟩⟩

def singletonLocal131 : CachedLocal 8689 :=
  ⟨(1405, (0, 5)), ⟨69500, (2280259602747945), 0x110000000, 0x56000029520012aaa006e⟩⟩

def singletonLocal132 : CachedLocal 8689 :=
  ⟨(1415, (0, 3)), ⟨1007000, (-2088316202709555), 0x110000000, 0x5986802a120013eaa0073⟩⟩

def singletonLocal133 : CachedLocal 8689 :=
  ⟨(1420, (0, 5)), ⟨1475750, (-2640919924324500), 0x110000000, 0x48805980002ad200148aa007d⟩⟩

def singletonLocal134 : CachedLocal 8689 :=
  ⟨(1432, (0, 0)), ⟨457625, (243138813022560), 0x110000000, 0x6080002dc30012ca80062⟩⟩

def singletonLocal135 : CachedLocal 8689 :=
  ⟨(1455, (0, 0)), ⟨460750, (-600117259449435), 0x110000000, 0x692a80274000196aa004c⟩⟩

def singletonLocal136 : CachedLocal 8689 :=
  ⟨(1471, (0, 0)), ⟨463875, (-1325334257069550), 0x110000000, 0xd805724803183601a6ad008a⟩⟩

def singletonLocal137 : CachedLocal 8689 :=
  ⟨(1806, (1, 2)), ⟨805650, (415508695704375), 0x111100000, 0x80d58c805fc000256300060⟩⟩

def singletonLocal138 : CachedLocal 8689 :=
  ⟨(2209, (1, 2)), ⟨805775, (1320399989007645), 0x111100000, 0x815700009b4000432c001d1⟩⟩

def singletonLocal139 : CachedLocal 8689 :=
  ⟨(2329, (0, 2)), ⟨850900, (298096973729100), 0x110000000, 0x1908000c440006021802dd⟩⟩

def singletonLocal140 : CachedLocal 8689 :=
  ⟨(2367, (0, 2)), ⟨854025, (-831669947963400), 0x110000000, 0x1a58000cec000662f302f1⟩⟩

def singletonLocal141 : CachedLocal 8689 :=
  ⟨(2681, (4, 6)), ⟨19600, (196326233704965), 0x111111000, 0x181ac8080d640003da00008e⟩⟩

def singletonLocal142 : CachedLocal 8689 :=
  ⟨(2685, (4, 8)), ⟨488350, (-948365394964260), 0x111111000, 0x181b18080d8c0003e2000091⟩⟩

def singletonLocal143 : CachedLocal 8689 :=
  ⟨(2698, (4, 11)), ⟨1285225, (-108237806764815), 0x111111000, 0x181b90680c680003fc00009c⟩⟩

def singletonLocal144 : CachedLocal 8689 :=
  ⟨(2727, (4, 10)), ⟨507100, (-2088316202709555), 0x111111000, 0x181c886808c40004580000a8⟩⟩

def singletonLocal145 : CachedLocal 8689 :=
  ⟨(2822, (0, 6)), ⟨66405, (382363804769310), 0x110000000, 0x81da0000ed000075af001ed⟩⟩

def singletonLocal146 : CachedLocal 8689 :=
  ⟨(2826, (0, 8)), ⟨535155, (-594470238080355), 0x110000000, 0x81dc8000ee4000760f001f1⟩⟩

def singletonLocal147 : CachedLocal 8689 :=
  ⟨(2840, (0, 6)), ⟨69530, (-1730849495287185), 0x110000000, 0x1e70000f11200768f20359⟩⟩

def singletonLocal148 : CachedLocal 8689 :=
  ⟨(2840, (0, 7)), ⟨69530, (-1730849495287185), 0x110000000, 0x1e70000f11200768f20359⟩⟩

def singletonLocal149 : CachedLocal 8689 :=
  ⟨(2845, (0, 8)), ⟨538280, (-1147801330716495), 0x110000000, 0x1e90000f21200772f20363⟩⟩

def singletonLocal150 : CachedLocal 8689 :=
  ⟨(2845, (0, 10)), ⟨538280, (-1147801330716495), 0x110000000, 0x1e90000f21200772f20363⟩⟩

def singletonLocal151 : CachedLocal 8689 :=
  ⟨(2877, (0, 11)), ⟨1317030, (-1080562864796415), 0x110000000, 0xc81f68000f7c300776f00224⟩⟩

def singletonLocal152 : CachedLocal 8689 :=
  ⟨(2909, (0, 11)), ⟨1320155, (-1491883431710490), 0x110000000, 0x20680010080007f10a0289⟩⟩

def singletonLocal153 : CachedLocal 8689 :=
  ⟨(2945, (0, 11)), ⟨1323280, (-606150161916390), 0x110000000, 0x21b800109c000838f3037f⟩⟩

def singletonLocal154 : CachedLocal 8689 :=
  ⟨(3007, (1, 10)), ⟨508905, (-1413962239765530), 0x111100000, 0x821a8001000000790c0022c⟩⟩

def singletonLocal155 : CachedLocal 8689 :=
  ⟨(3012, (3, 16)), ⟨977655, (-2221664782583610), 0x111100000, 0x821fc281000000796c00231⟩⟩

def singletonLocal156 : CachedLocal 8689 :=
  ⟨(3040, (0, 10)), ⟨542155, (-651058434611130), 0x110000000, 0x22137010fd52086af30391⟩⟩

def singletonLocal157 : CachedLocal 8689 :=
  ⟨(3311, (0, 3)), ⟨18754, (-1147594754188155), 0x111111110, 0x481e40200f20cc012200000e⟩⟩

def singletonLocal158 : CachedLocal 8689 :=
  ⟨(3316, (0, 3)), ⟨956254, (-2823845221965495), 0x111111110, 0x481e68200f10cc0126000013⟩⟩

def singletonLocal159 : CachedLocal 8689 :=
  ⟨(3390, (0, 2)), ⟨803754, (-1501634753612175), 0x111111110, 0x48213a180c5dbc02ee000060⟩⟩

def singletonLocal160 : CachedLocal 8689 :=
  ⟨(3767, (0, 3)), ⟨75750, (2280259602747945), 0x221000000, 0x4882bea4015f5200ad8a805470082be80015f4000ad8180547⟩⟩

def singletonLocal161 : CachedLocal 8689 :=
  ⟨(3772, (0, 3)), ⟨1013250, (-2823845221965495), 0x221000000, 0x4882c6240161d200ae8a8054f0082c6000161c000ae818054f⟩⟩

def singletonLocal162 : CachedLocal 8689 :=
  ⟨(3803, (0, 0)), ⟨467000, (-1325334257069550), 0x221000000, 0x4902e3248167d240b6caa05590002df80016bc000b30180552⟩⟩

def singletonLocal163 : CachedLocal 8689 :=
  ⟨(4426, (0, 2)), ⟨857150, (-831669947963400), 0x221000000, 0x4bf80025bc0012be00094f00049f800246430114218070e⟩⟩

def singletonLocal164 : CachedLocal 8689 :=
  ⟨(5031, (0, 6)), ⟨75780, (-1730849495287185), 0x221000000, 0x48858c2402c6120160cf00a7900858c0002c6000160c600a79⟩⟩

def singletonLocal165 : CachedLocal 8689 :=
  ⟨(5034, (0, 8)), ⟨544530, (-1147801330716495), 0x221000000, 0x48858ea402c75201614f00a7d00858e8002c74001614600a7d⟩⟩

def singletonLocal166 : CachedLocal 8689 :=
  ⟨(5101, (0, 11)), ⟨1326405, (-1491883431710490), 0x221000000, 0x5d88002e84001722f00aa00005c08002d7400167a600a8a⟩⟩

def singletonLocal167 : CachedLocal 8689 :=
  ⟨(5185, (0, 10)), ⟨545280, (-2221664782583610), 0x221000000, 0x4805f03682f1150177ef00aa70005f01282f1030177e600aa7⟩⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00014 :
    singletonLocal000.row = EJMSingletonCacheData.mirror singletonLocal000.state.1 := by
  have fields : FullLocalFields singletonLocal000
      ⟨singletonLocal000.state, EJMSingletonCacheData.mirror singletonLocal000.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00019 :
    singletonLocal002.row = EJMSingletonCacheData.mirror singletonLocal002.state.1 := by
  have fields : FullLocalFields singletonLocal002
      ⟨singletonLocal002.state, EJMSingletonCacheData.mirror singletonLocal002.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00058 :
    singletonLocal004.row = EJMSingletonCacheData.mirror singletonLocal004.state.1 := by
  have fields : FullLocalFields singletonLocal004
      ⟨singletonLocal004.state, EJMSingletonCacheData.mirror singletonLocal004.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00066 :
    singletonLocal006.row = EJMSingletonCacheData.mirror singletonLocal006.state.1 := by
  have fields : FullLocalFields singletonLocal006
      ⟨singletonLocal006.state, EJMSingletonCacheData.mirror singletonLocal006.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00076 :
    singletonLocal008.row = EJMSingletonCacheData.mirror singletonLocal008.state.1 := by
  have fields : FullLocalFields singletonLocal008
      ⟨singletonLocal008.state, EJMSingletonCacheData.mirror singletonLocal008.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00096 :
    singletonLocal009.row = EJMSingletonCacheData.mirror singletonLocal009.state.1 := by
  have fields : FullLocalFields singletonLocal009
      ⟨singletonLocal009.state, EJMSingletonCacheData.mirror singletonLocal009.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00098 :
    singletonLocal010.row = EJMSingletonCacheData.mirror singletonLocal010.state.1 := by
  have fields : FullLocalFields singletonLocal010
      ⟨singletonLocal010.state, EJMSingletonCacheData.mirror singletonLocal010.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00110 :
    singletonLocal011.row = EJMSingletonCacheData.mirror singletonLocal011.state.1 := by
  have fields : FullLocalFields singletonLocal011
      ⟨singletonLocal011.state, EJMSingletonCacheData.mirror singletonLocal011.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00115 :
    singletonLocal015.row = EJMSingletonCacheData.mirror singletonLocal015.state.1 := by
  have fields : FullLocalFields singletonLocal015
      ⟨singletonLocal015.state, EJMSingletonCacheData.mirror singletonLocal015.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00125 :
    singletonLocal017.row = EJMSingletonCacheData.mirror singletonLocal017.state.1 := by
  have fields : FullLocalFields singletonLocal017
      ⟨singletonLocal017.state, EJMSingletonCacheData.mirror singletonLocal017.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00138 :
    singletonLocal019.row = EJMSingletonCacheData.mirror singletonLocal019.state.1 := by
  have fields : FullLocalFields singletonLocal019
      ⟨singletonLocal019.state, EJMSingletonCacheData.mirror singletonLocal019.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00142 :
    singletonLocal021.row = EJMSingletonCacheData.mirror singletonLocal021.state.1 := by
  have fields : FullLocalFields singletonLocal021
      ⟨singletonLocal021.state, EJMSingletonCacheData.mirror singletonLocal021.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00145 :
    singletonLocal023.row = EJMSingletonCacheData.mirror singletonLocal023.state.1 := by
  have fields : FullLocalFields singletonLocal023
      ⟨singletonLocal023.state, EJMSingletonCacheData.mirror singletonLocal023.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00147 :
    singletonLocal024.row = EJMSingletonCacheData.mirror singletonLocal024.state.1 := by
  have fields : FullLocalFields singletonLocal024
      ⟨singletonLocal024.state, EJMSingletonCacheData.mirror singletonLocal024.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00149 :
    singletonLocal028.row = EJMSingletonCacheData.mirror singletonLocal028.state.1 := by
  have fields : FullLocalFields singletonLocal028
      ⟨singletonLocal028.state, EJMSingletonCacheData.mirror singletonLocal028.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00150 :
    singletonLocal030.row = EJMSingletonCacheData.mirror singletonLocal030.state.1 := by
  have fields : FullLocalFields singletonLocal030
      ⟨singletonLocal030.state, EJMSingletonCacheData.mirror singletonLocal030.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00156 :
    singletonLocal031.row = EJMSingletonCacheData.mirror singletonLocal031.state.1 := by
  have fields : FullLocalFields singletonLocal031
      ⟨singletonLocal031.state, EJMSingletonCacheData.mirror singletonLocal031.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00157 :
    singletonLocal032.row = EJMSingletonCacheData.mirror singletonLocal032.state.1 := by
  have fields : FullLocalFields singletonLocal032
      ⟨singletonLocal032.state, EJMSingletonCacheData.mirror singletonLocal032.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00159 :
    singletonLocal034.row = EJMSingletonCacheData.mirror singletonLocal034.state.1 := by
  have fields : FullLocalFields singletonLocal034
      ⟨singletonLocal034.state, EJMSingletonCacheData.mirror singletonLocal034.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00164 :
    singletonLocal036.row = EJMSingletonCacheData.mirror singletonLocal036.state.1 := by
  have fields : FullLocalFields singletonLocal036
      ⟨singletonLocal036.state, EJMSingletonCacheData.mirror singletonLocal036.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00165 :
    singletonLocal037.row = EJMSingletonCacheData.mirror singletonLocal037.state.1 := by
  have fields : FullLocalFields singletonLocal037
      ⟨singletonLocal037.state, EJMSingletonCacheData.mirror singletonLocal037.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00168 :
    singletonLocal039.row = EJMSingletonCacheData.mirror singletonLocal039.state.1 := by
  have fields : FullLocalFields singletonLocal039
      ⟨singletonLocal039.state, EJMSingletonCacheData.mirror singletonLocal039.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00171 :
    singletonLocal041.row = EJMSingletonCacheData.mirror singletonLocal041.state.1 := by
  have fields : FullLocalFields singletonLocal041
      ⟨singletonLocal041.state, EJMSingletonCacheData.mirror singletonLocal041.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00172 :
    singletonLocal042.row = EJMSingletonCacheData.mirror singletonLocal042.state.1 := by
  have fields : FullLocalFields singletonLocal042
      ⟨singletonLocal042.state, EJMSingletonCacheData.mirror singletonLocal042.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00174 :
    singletonLocal044.row = EJMSingletonCacheData.mirror singletonLocal044.state.1 := by
  have fields : FullLocalFields singletonLocal044
      ⟨singletonLocal044.state, EJMSingletonCacheData.mirror singletonLocal044.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00179 :
    singletonLocal045.row = EJMSingletonCacheData.mirror singletonLocal045.state.1 := by
  have fields : FullLocalFields singletonLocal045
      ⟨singletonLocal045.state, EJMSingletonCacheData.mirror singletonLocal045.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00183 :
    singletonLocal047.row = EJMSingletonCacheData.mirror singletonLocal047.state.1 := by
  have fields : FullLocalFields singletonLocal047
      ⟨singletonLocal047.state, EJMSingletonCacheData.mirror singletonLocal047.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00193 :
    singletonLocal048.row = EJMSingletonCacheData.mirror singletonLocal048.state.1 := by
  have fields : FullLocalFields singletonLocal048
      ⟨singletonLocal048.state, EJMSingletonCacheData.mirror singletonLocal048.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00198 :
    singletonLocal049.row = EJMSingletonCacheData.mirror singletonLocal049.state.1 := by
  have fields : FullLocalFields singletonLocal049
      ⟨singletonLocal049.state, EJMSingletonCacheData.mirror singletonLocal049.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00203 :
    singletonLocal050.row = EJMSingletonCacheData.mirror singletonLocal050.state.1 := by
  have fields : FullLocalFields singletonLocal050
      ⟨singletonLocal050.state, EJMSingletonCacheData.mirror singletonLocal050.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00210 :
    singletonLocal051.row = EJMSingletonCacheData.mirror singletonLocal051.state.1 := by
  have fields : FullLocalFields singletonLocal051
      ⟨singletonLocal051.state, EJMSingletonCacheData.mirror singletonLocal051.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00211 :
    singletonLocal052.row = EJMSingletonCacheData.mirror singletonLocal052.state.1 := by
  have fields : FullLocalFields singletonLocal052
      ⟨singletonLocal052.state, EJMSingletonCacheData.mirror singletonLocal052.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00375 :
    singletonLocal053.row = EJMSingletonCacheData.mirror singletonLocal053.state.1 := by
  have fields : FullLocalFields singletonLocal053
      ⟨singletonLocal053.state, EJMSingletonCacheData.mirror singletonLocal053.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00465 :
    singletonLocal054.row = EJMSingletonCacheData.mirror singletonLocal054.state.1 := by
  have fields : FullLocalFields singletonLocal054
      ⟨singletonLocal054.state, EJMSingletonCacheData.mirror singletonLocal054.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00493 :
    singletonLocal056.row = EJMSingletonCacheData.mirror singletonLocal056.state.1 := by
  have fields : FullLocalFields singletonLocal056
      ⟨singletonLocal056.state, EJMSingletonCacheData.mirror singletonLocal056.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00497 :
    singletonLocal058.row = EJMSingletonCacheData.mirror singletonLocal058.state.1 := by
  have fields : FullLocalFields singletonLocal058
      ⟨singletonLocal058.state, EJMSingletonCacheData.mirror singletonLocal058.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00510 :
    singletonLocal059.row = EJMSingletonCacheData.mirror singletonLocal059.state.1 := by
  have fields : FullLocalFields singletonLocal059
      ⟨singletonLocal059.state, EJMSingletonCacheData.mirror singletonLocal059.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00537 :
    singletonLocal060.row = EJMSingletonCacheData.mirror singletonLocal060.state.1 := by
  have fields : FullLocalFields singletonLocal060
      ⟨singletonLocal060.state, EJMSingletonCacheData.mirror singletonLocal060.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00556 :
    singletonLocal062.row = EJMSingletonCacheData.mirror singletonLocal062.state.1 := by
  have fields : FullLocalFields singletonLocal062
      ⟨singletonLocal062.state, EJMSingletonCacheData.mirror singletonLocal062.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00561 :
    singletonLocal063.row = EJMSingletonCacheData.mirror singletonLocal063.state.1 := by
  have fields : FullLocalFields singletonLocal063
      ⟨singletonLocal063.state, EJMSingletonCacheData.mirror singletonLocal063.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00621 :
    singletonLocal065.row = EJMSingletonCacheData.mirror singletonLocal065.state.1 := by
  have fields : FullLocalFields singletonLocal065
      ⟨singletonLocal065.state, EJMSingletonCacheData.mirror singletonLocal065.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00649 :
    singletonLocal066.row = EJMSingletonCacheData.mirror singletonLocal066.state.1 := by
  have fields : FullLocalFields singletonLocal066
      ⟨singletonLocal066.state, EJMSingletonCacheData.mirror singletonLocal066.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00686 :
    singletonLocal067.row = EJMSingletonCacheData.mirror singletonLocal067.state.1 := by
  have fields : FullLocalFields singletonLocal067
      ⟨singletonLocal067.state, EJMSingletonCacheData.mirror singletonLocal067.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00733 :
    singletonLocal068.row = EJMSingletonCacheData.mirror singletonLocal068.state.1 := by
  have fields : FullLocalFields singletonLocal068
      ⟨singletonLocal068.state, EJMSingletonCacheData.mirror singletonLocal068.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00753 :
    singletonLocal069.row = EJMSingletonCacheData.mirror singletonLocal069.state.1 := by
  have fields : FullLocalFields singletonLocal069
      ⟨singletonLocal069.state, EJMSingletonCacheData.mirror singletonLocal069.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00769 :
    singletonLocal070.row = EJMSingletonCacheData.mirror singletonLocal070.state.1 := by
  have fields : FullLocalFields singletonLocal070
      ⟨singletonLocal070.state, EJMSingletonCacheData.mirror singletonLocal070.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00785 :
    singletonLocal071.row = EJMSingletonCacheData.mirror singletonLocal071.state.1 := by
  have fields : FullLocalFields singletonLocal071
      ⟨singletonLocal071.state, EJMSingletonCacheData.mirror singletonLocal071.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00791 :
    singletonLocal072.row = EJMSingletonCacheData.mirror singletonLocal072.state.1 := by
  have fields : FullLocalFields singletonLocal072
      ⟨singletonLocal072.state, EJMSingletonCacheData.mirror singletonLocal072.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00794 :
    singletonLocal073.row = EJMSingletonCacheData.mirror singletonLocal073.state.1 := by
  have fields : FullLocalFields singletonLocal073
      ⟨singletonLocal073.state, EJMSingletonCacheData.mirror singletonLocal073.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00801 :
    singletonLocal074.row = EJMSingletonCacheData.mirror singletonLocal074.state.1 := by
  have fields : FullLocalFields singletonLocal074
      ⟨singletonLocal074.state, EJMSingletonCacheData.mirror singletonLocal074.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00817 :
    singletonLocal075.row = EJMSingletonCacheData.mirror singletonLocal075.state.1 := by
  have fields : FullLocalFields singletonLocal075
      ⟨singletonLocal075.state, EJMSingletonCacheData.mirror singletonLocal075.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00827 :
    singletonLocal076.row = EJMSingletonCacheData.mirror singletonLocal076.state.1 := by
  have fields : FullLocalFields singletonLocal076
      ⟨singletonLocal076.state, EJMSingletonCacheData.mirror singletonLocal076.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00843 :
    singletonLocal077.row = EJMSingletonCacheData.mirror singletonLocal077.state.1 := by
  have fields : FullLocalFields singletonLocal077
      ⟨singletonLocal077.state, EJMSingletonCacheData.mirror singletonLocal077.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00857 :
    singletonLocal078.row = EJMSingletonCacheData.mirror singletonLocal078.state.1 := by
  have fields : FullLocalFields singletonLocal078
      ⟨singletonLocal078.state, EJMSingletonCacheData.mirror singletonLocal078.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00867 :
    singletonLocal084.row = EJMSingletonCacheData.mirror singletonLocal084.state.1 := by
  have fields : FullLocalFields singletonLocal084
      ⟨singletonLocal084.state, EJMSingletonCacheData.mirror singletonLocal084.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00882 :
    singletonLocal086.row = EJMSingletonCacheData.mirror singletonLocal086.state.1 := by
  have fields : FullLocalFields singletonLocal086
      ⟨singletonLocal086.state, EJMSingletonCacheData.mirror singletonLocal086.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00895 :
    singletonLocal087.row = EJMSingletonCacheData.mirror singletonLocal087.state.1 := by
  have fields : FullLocalFields singletonLocal087
      ⟨singletonLocal087.state, EJMSingletonCacheData.mirror singletonLocal087.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00913 :
    singletonLocal089.row = EJMSingletonCacheData.mirror singletonLocal089.state.1 := by
  have fields : FullLocalFields singletonLocal089
      ⟨singletonLocal089.state, EJMSingletonCacheData.mirror singletonLocal089.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00941 :
    singletonLocal090.row = EJMSingletonCacheData.mirror singletonLocal090.state.1 := by
  have fields : FullLocalFields singletonLocal090
      ⟨singletonLocal090.state, EJMSingletonCacheData.mirror singletonLocal090.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00944 :
    singletonLocal091.row = EJMSingletonCacheData.mirror singletonLocal091.state.1 := by
  have fields : FullLocalFields singletonLocal091
      ⟨singletonLocal091.state, EJMSingletonCacheData.mirror singletonLocal091.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00948 :
    singletonLocal092.row = EJMSingletonCacheData.mirror singletonLocal092.state.1 := by
  have fields : FullLocalFields singletonLocal092
      ⟨singletonLocal092.state, EJMSingletonCacheData.mirror singletonLocal092.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00953 :
    singletonLocal096.row = EJMSingletonCacheData.mirror singletonLocal096.state.1 := by
  have fields : FullLocalFields singletonLocal096
      ⟨singletonLocal096.state, EJMSingletonCacheData.mirror singletonLocal096.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00964 :
    singletonLocal101.row = EJMSingletonCacheData.mirror singletonLocal101.state.1 := by
  have fields : FullLocalFields singletonLocal101
      ⟨singletonLocal101.state, EJMSingletonCacheData.mirror singletonLocal101.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00968 :
    singletonLocal102.row = EJMSingletonCacheData.mirror singletonLocal102.state.1 := by
  have fields : FullLocalFields singletonLocal102
      ⟨singletonLocal102.state, EJMSingletonCacheData.mirror singletonLocal102.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00971 :
    singletonLocal106.row = EJMSingletonCacheData.mirror singletonLocal106.state.1 := by
  have fields : FullLocalFields singletonLocal106
      ⟨singletonLocal106.state, EJMSingletonCacheData.mirror singletonLocal106.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00973 :
    singletonLocal107.row = EJMSingletonCacheData.mirror singletonLocal107.state.1 := by
  have fields : FullLocalFields singletonLocal107
      ⟨singletonLocal107.state, EJMSingletonCacheData.mirror singletonLocal107.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00974 :
    singletonLocal108.row = EJMSingletonCacheData.mirror singletonLocal108.state.1 := by
  have fields : FullLocalFields singletonLocal108
      ⟨singletonLocal108.state, EJMSingletonCacheData.mirror singletonLocal108.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_00978 :
    singletonLocal110.row = EJMSingletonCacheData.mirror singletonLocal110.state.1 := by
  have fields : FullLocalFields singletonLocal110
      ⟨singletonLocal110.state, EJMSingletonCacheData.mirror singletonLocal110.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01016 :
    singletonLocal112.row = EJMSingletonCacheData.mirror singletonLocal112.state.1 := by
  have fields : FullLocalFields singletonLocal112
      ⟨singletonLocal112.state, EJMSingletonCacheData.mirror singletonLocal112.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01024 :
    singletonLocal113.row = EJMSingletonCacheData.mirror singletonLocal113.state.1 := by
  have fields : FullLocalFields singletonLocal113
      ⟨singletonLocal113.state, EJMSingletonCacheData.mirror singletonLocal113.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01026 :
    singletonLocal115.row = EJMSingletonCacheData.mirror singletonLocal115.state.1 := by
  have fields : FullLocalFields singletonLocal115
      ⟨singletonLocal115.state, EJMSingletonCacheData.mirror singletonLocal115.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01037 :
    singletonLocal116.row = EJMSingletonCacheData.mirror singletonLocal116.state.1 := by
  have fields : FullLocalFields singletonLocal116
      ⟨singletonLocal116.state, EJMSingletonCacheData.mirror singletonLocal116.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01052 :
    singletonLocal117.row = EJMSingletonCacheData.mirror singletonLocal117.state.1 := by
  have fields : FullLocalFields singletonLocal117
      ⟨singletonLocal117.state, EJMSingletonCacheData.mirror singletonLocal117.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01063 :
    singletonLocal118.row = EJMSingletonCacheData.mirror singletonLocal118.state.1 := by
  have fields : FullLocalFields singletonLocal118
      ⟨singletonLocal118.state, EJMSingletonCacheData.mirror singletonLocal118.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01077 :
    singletonLocal119.row = EJMSingletonCacheData.mirror singletonLocal119.state.1 := by
  have fields : FullLocalFields singletonLocal119
      ⟨singletonLocal119.state, EJMSingletonCacheData.mirror singletonLocal119.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01079 :
    singletonLocal121.row = EJMSingletonCacheData.mirror singletonLocal121.state.1 := by
  have fields : FullLocalFields singletonLocal121
      ⟨singletonLocal121.state, EJMSingletonCacheData.mirror singletonLocal121.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01087 :
    singletonLocal123.row = EJMSingletonCacheData.mirror singletonLocal123.state.1 := by
  have fields : FullLocalFields singletonLocal123
      ⟨singletonLocal123.state, EJMSingletonCacheData.mirror singletonLocal123.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01090 :
    singletonLocal124.row = EJMSingletonCacheData.mirror singletonLocal124.state.1 := by
  have fields : FullLocalFields singletonLocal124
      ⟨singletonLocal124.state, EJMSingletonCacheData.mirror singletonLocal124.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01351 :
    singletonLocal125.row = EJMSingletonCacheData.mirror singletonLocal125.state.1 := by
  have fields : FullLocalFields singletonLocal125
      ⟨singletonLocal125.state, EJMSingletonCacheData.mirror singletonLocal125.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01359 :
    singletonLocal126.row = EJMSingletonCacheData.mirror singletonLocal126.state.1 := by
  have fields : FullLocalFields singletonLocal126
      ⟨singletonLocal126.state, EJMSingletonCacheData.mirror singletonLocal126.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01362 :
    singletonLocal127.row = EJMSingletonCacheData.mirror singletonLocal127.state.1 := by
  have fields : FullLocalFields singletonLocal127
      ⟨singletonLocal127.state, EJMSingletonCacheData.mirror singletonLocal127.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01388 :
    singletonLocal128.row = EJMSingletonCacheData.mirror singletonLocal128.state.1 := by
  have fields : FullLocalFields singletonLocal128
      ⟨singletonLocal128.state, EJMSingletonCacheData.mirror singletonLocal128.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01396 :
    singletonLocal129.row = EJMSingletonCacheData.mirror singletonLocal129.state.1 := by
  have fields : FullLocalFields singletonLocal129
      ⟨singletonLocal129.state, EJMSingletonCacheData.mirror singletonLocal129.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01405 :
    singletonLocal130.row = EJMSingletonCacheData.mirror singletonLocal130.state.1 := by
  have fields : FullLocalFields singletonLocal130
      ⟨singletonLocal130.state, EJMSingletonCacheData.mirror singletonLocal130.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01415 :
    singletonLocal132.row = EJMSingletonCacheData.mirror singletonLocal132.state.1 := by
  have fields : FullLocalFields singletonLocal132
      ⟨singletonLocal132.state, EJMSingletonCacheData.mirror singletonLocal132.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01420 :
    singletonLocal133.row = EJMSingletonCacheData.mirror singletonLocal133.state.1 := by
  have fields : FullLocalFields singletonLocal133
      ⟨singletonLocal133.state, EJMSingletonCacheData.mirror singletonLocal133.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01432 :
    singletonLocal134.row = EJMSingletonCacheData.mirror singletonLocal134.state.1 := by
  have fields : FullLocalFields singletonLocal134
      ⟨singletonLocal134.state, EJMSingletonCacheData.mirror singletonLocal134.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01455 :
    singletonLocal135.row = EJMSingletonCacheData.mirror singletonLocal135.state.1 := by
  have fields : FullLocalFields singletonLocal135
      ⟨singletonLocal135.state, EJMSingletonCacheData.mirror singletonLocal135.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01471 :
    singletonLocal136.row = EJMSingletonCacheData.mirror singletonLocal136.state.1 := by
  have fields : FullLocalFields singletonLocal136
      ⟨singletonLocal136.state, EJMSingletonCacheData.mirror singletonLocal136.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_01806 :
    singletonLocal137.row = EJMSingletonCacheData.mirror singletonLocal137.state.1 := by
  have fields : FullLocalFields singletonLocal137
      ⟨singletonLocal137.state, EJMSingletonCacheData.mirror singletonLocal137.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02209 :
    singletonLocal138.row = EJMSingletonCacheData.mirror singletonLocal138.state.1 := by
  have fields : FullLocalFields singletonLocal138
      ⟨singletonLocal138.state, EJMSingletonCacheData.mirror singletonLocal138.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02329 :
    singletonLocal139.row = EJMSingletonCacheData.mirror singletonLocal139.state.1 := by
  have fields : FullLocalFields singletonLocal139
      ⟨singletonLocal139.state, EJMSingletonCacheData.mirror singletonLocal139.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02367 :
    singletonLocal140.row = EJMSingletonCacheData.mirror singletonLocal140.state.1 := by
  have fields : FullLocalFields singletonLocal140
      ⟨singletonLocal140.state, EJMSingletonCacheData.mirror singletonLocal140.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02681 :
    singletonLocal141.row = EJMSingletonCacheData.mirror singletonLocal141.state.1 := by
  have fields : FullLocalFields singletonLocal141
      ⟨singletonLocal141.state, EJMSingletonCacheData.mirror singletonLocal141.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02685 :
    singletonLocal142.row = EJMSingletonCacheData.mirror singletonLocal142.state.1 := by
  have fields : FullLocalFields singletonLocal142
      ⟨singletonLocal142.state, EJMSingletonCacheData.mirror singletonLocal142.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02698 :
    singletonLocal143.row = EJMSingletonCacheData.mirror singletonLocal143.state.1 := by
  have fields : FullLocalFields singletonLocal143
      ⟨singletonLocal143.state, EJMSingletonCacheData.mirror singletonLocal143.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02727 :
    singletonLocal144.row = EJMSingletonCacheData.mirror singletonLocal144.state.1 := by
  have fields : FullLocalFields singletonLocal144
      ⟨singletonLocal144.state, EJMSingletonCacheData.mirror singletonLocal144.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02822 :
    singletonLocal145.row = EJMSingletonCacheData.mirror singletonLocal145.state.1 := by
  have fields : FullLocalFields singletonLocal145
      ⟨singletonLocal145.state, EJMSingletonCacheData.mirror singletonLocal145.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02826 :
    singletonLocal146.row = EJMSingletonCacheData.mirror singletonLocal146.state.1 := by
  have fields : FullLocalFields singletonLocal146
      ⟨singletonLocal146.state, EJMSingletonCacheData.mirror singletonLocal146.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02840 :
    singletonLocal147.row = EJMSingletonCacheData.mirror singletonLocal147.state.1 := by
  have fields : FullLocalFields singletonLocal147
      ⟨singletonLocal147.state, EJMSingletonCacheData.mirror singletonLocal147.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02845 :
    singletonLocal149.row = EJMSingletonCacheData.mirror singletonLocal149.state.1 := by
  have fields : FullLocalFields singletonLocal149
      ⟨singletonLocal149.state, EJMSingletonCacheData.mirror singletonLocal149.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02877 :
    singletonLocal151.row = EJMSingletonCacheData.mirror singletonLocal151.state.1 := by
  have fields : FullLocalFields singletonLocal151
      ⟨singletonLocal151.state, EJMSingletonCacheData.mirror singletonLocal151.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02909 :
    singletonLocal152.row = EJMSingletonCacheData.mirror singletonLocal152.state.1 := by
  have fields : FullLocalFields singletonLocal152
      ⟨singletonLocal152.state, EJMSingletonCacheData.mirror singletonLocal152.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_02945 :
    singletonLocal153.row = EJMSingletonCacheData.mirror singletonLocal153.state.1 := by
  have fields : FullLocalFields singletonLocal153
      ⟨singletonLocal153.state, EJMSingletonCacheData.mirror singletonLocal153.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_03007 :
    singletonLocal154.row = EJMSingletonCacheData.mirror singletonLocal154.state.1 := by
  have fields : FullLocalFields singletonLocal154
      ⟨singletonLocal154.state, EJMSingletonCacheData.mirror singletonLocal154.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_03012 :
    singletonLocal155.row = EJMSingletonCacheData.mirror singletonLocal155.state.1 := by
  have fields : FullLocalFields singletonLocal155
      ⟨singletonLocal155.state, EJMSingletonCacheData.mirror singletonLocal155.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_mirror_03040 :
    singletonLocal156.row = EJMSingletonCacheData.mirror singletonLocal156.state.1 := by
  have fields : FullLocalFields singletonLocal156
      ⟨singletonLocal156.state, EJMSingletonCacheData.mirror singletonLocal156.state.1⟩ := by
    decide +kernel
  exact congrArg (fun x : CachedLocal 8689 => x.row)
    (cachedLocal_eq_of_fields _ _ fields)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_000 :
    (singletonStep singletonLocal125 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal001.state := by
  decide +kernel

theorem singleton_update_000 :
    singletonStep singletonLocal125 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal001 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_000 singleton_mirror_00014

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_001 :
    (singletonStep singletonLocal125 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal011.state := by
  decide +kernel

theorem singleton_update_001 :
    singletonStep singletonLocal125 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal011 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_001 singleton_mirror_00110

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_002 :
    (singletonStep singletonLocal125 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal012.state := by
  decide +kernel

theorem singleton_update_002 :
    singletonStep singletonLocal125 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal012 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_002 singleton_mirror_00110

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_003 :
    (singletonStep singletonLocal125 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal004.state := by
  decide +kernel

theorem singleton_update_003 :
    singletonStep singletonLocal125 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal004 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_003 singleton_mirror_00058

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_004 :
    (singletonStep singletonLocal126 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal003.state := by
  decide +kernel

theorem singleton_update_004 :
    singletonStep singletonLocal126 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal003 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_004 singleton_mirror_00019

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_005 :
    (singletonStep singletonLocal126 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal015.state := by
  decide +kernel

theorem singleton_update_005 :
    singletonStep singletonLocal126 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal015 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_005 singleton_mirror_00115

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_006 :
    (singletonStep singletonLocal126 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal017.state := by
  decide +kernel

theorem singleton_update_006 :
    singletonStep singletonLocal126 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal017 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_006 singleton_mirror_00125

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_007 :
    (singletonStep singletonLocal126 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal006.state := by
  decide +kernel

theorem singleton_update_007 :
    singletonStep singletonLocal126 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal006 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_007 singleton_mirror_00066

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_008 :
    (singletonStep singletonLocal128 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal005.state := by
  decide +kernel

theorem singleton_update_008 :
    singletonStep singletonLocal128 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal005 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_008 singleton_mirror_00058

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_009 :
    (singletonStep singletonLocal128 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal026.state := by
  decide +kernel

theorem singleton_update_009 :
    singletonStep singletonLocal128 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal026 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_009 singleton_mirror_00149

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_010 :
    (singletonStep singletonLocal128 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal027.state := by
  decide +kernel

theorem singleton_update_010 :
    singletonStep singletonLocal128 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal027 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_010 singleton_mirror_00149

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_011 :
    (singletonStep singletonLocal128 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal020.state := by
  decide +kernel

theorem singleton_update_011 :
    singletonStep singletonLocal128 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal020 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_011 singleton_mirror_00142

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_012 :
    (singletonStep singletonLocal129 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal007.state := by
  decide +kernel

theorem singleton_update_012 :
    singletonStep singletonLocal129 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal007 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_012 singleton_mirror_00066

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_013 :
    (singletonStep singletonLocal129 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal033.state := by
  decide +kernel

theorem singleton_update_013 :
    singletonStep singletonLocal129 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal033 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_013 singleton_mirror_00159

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_014 :
    (singletonStep singletonLocal129 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal035.state := by
  decide +kernel

theorem singleton_update_014 :
    singletonStep singletonLocal129 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal035 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_014 singleton_mirror_00164

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_015 :
    (singletonStep singletonLocal129 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal024.state := by
  decide +kernel

theorem singleton_update_015 :
    singletonStep singletonLocal129 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal024 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_015 singleton_mirror_00147

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_016 :
    (singletonStep singletonLocal130 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal013.state := by
  decide +kernel

theorem singleton_update_016 :
    singletonStep singletonLocal130 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal013 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_016 singleton_mirror_00110

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_017 :
    (singletonStep singletonLocal130 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal037.state := by
  decide +kernel

theorem singleton_update_017 :
    singletonStep singletonLocal130 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal037 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_017 singleton_mirror_00165

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_018 :
    (singletonStep singletonLocal130 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal042.state := by
  decide +kernel

theorem singleton_update_018 :
    singletonStep singletonLocal130 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal042 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_018 singleton_mirror_00172

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_019 :
    (singletonStep singletonLocal130 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal028.state := by
  decide +kernel

theorem singleton_update_019 :
    singletonStep singletonLocal130 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal028 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_019 singleton_mirror_00149

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_020 :
    (singletonStep singletonLocal131 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal014.state := by
  decide +kernel

theorem singleton_update_020 :
    singletonStep singletonLocal131 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal014 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_020 singleton_mirror_00110

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_021 :
    (singletonStep singletonLocal131 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal043.state := by
  decide +kernel

theorem singleton_update_021 :
    singletonStep singletonLocal131 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal043 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_021 singleton_mirror_00172

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_022 :
    (singletonStep singletonLocal131 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal038.state := by
  decide +kernel

theorem singleton_update_022 :
    singletonStep singletonLocal131 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal038 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_022 singleton_mirror_00165

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_023 :
    (singletonStep singletonLocal131 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal029.state := by
  decide +kernel

theorem singleton_update_023 :
    singletonStep singletonLocal131 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal029 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_023 singleton_mirror_00149

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_024 :
    (singletonStep singletonLocal132 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal016.state := by
  decide +kernel

theorem singleton_update_024 :
    singletonStep singletonLocal132 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal016 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_024 singleton_mirror_00115

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_025 :
    (singletonStep singletonLocal132 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal039.state := by
  decide +kernel

theorem singleton_update_025 :
    singletonStep singletonLocal132 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal039 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_025 singleton_mirror_00168

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_026 :
    (singletonStep singletonLocal132 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal045.state := by
  decide +kernel

theorem singleton_update_026 :
    singletonStep singletonLocal132 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal045 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_026 singleton_mirror_00179

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_027 :
    (singletonStep singletonLocal132 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal034.state := by
  decide +kernel

theorem singleton_update_027 :
    singletonStep singletonLocal132 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal034 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_027 singleton_mirror_00159

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_028 :
    (singletonStep singletonLocal133 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal018.state := by
  decide +kernel

theorem singleton_update_028 :
    singletonStep singletonLocal133 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal018 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_028 singleton_mirror_00125

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_029 :
    (singletonStep singletonLocal133 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal046.state := by
  decide +kernel

theorem singleton_update_029 :
    singletonStep singletonLocal133 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal046 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_029 singleton_mirror_00179

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_030 :
    (singletonStep singletonLocal133 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal041.state := by
  decide +kernel

theorem singleton_update_030 :
    singletonStep singletonLocal133 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal041 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_030 singleton_mirror_00171

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_031 :
    (singletonStep singletonLocal133 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal036.state := by
  decide +kernel

theorem singleton_update_031 :
    singletonStep singletonLocal133 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal036 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_031 singleton_mirror_00164

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_032 :
    (singletonStep singletonLocal134 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal010.state := by
  decide +kernel

theorem singleton_update_032 :
    singletonStep singletonLocal134 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal010 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_032 singleton_mirror_00098

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_033 :
    (singletonStep singletonLocal134 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal030.state := by
  decide +kernel

theorem singleton_update_033 :
    singletonStep singletonLocal134 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal030 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_033 singleton_mirror_00150

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_034 :
    (singletonStep singletonLocal134 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal047.state := by
  decide +kernel

theorem singleton_update_034 :
    singletonStep singletonLocal134 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal047 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_034 singleton_mirror_00183

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_035 :
    (singletonStep singletonLocal134 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal048.state := by
  decide +kernel

theorem singleton_update_035 :
    singletonStep singletonLocal134 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal048 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_035 singleton_mirror_00193

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_036 :
    (singletonStep singletonLocal135 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal008.state := by
  decide +kernel

theorem singleton_update_036 :
    singletonStep singletonLocal135 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal008 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_036 singleton_mirror_00076

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_037 :
    (singletonStep singletonLocal135 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal050.state := by
  decide +kernel

theorem singleton_update_037 :
    singletonStep singletonLocal135 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal050 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_037 singleton_mirror_00203

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_038 :
    (singletonStep singletonLocal135 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal032.state := by
  decide +kernel

theorem singleton_update_038 :
    singletonStep singletonLocal135 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal032 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_038 singleton_mirror_00157

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_039 :
    (singletonStep singletonLocal135 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal051.state := by
  decide +kernel

theorem singleton_update_039 :
    singletonStep singletonLocal135 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal051 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_039 singleton_mirror_00210

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_040 :
    (singletonStep singletonLocal136 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal019.state := by
  decide +kernel

theorem singleton_update_040 :
    singletonStep singletonLocal136 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal019 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_040 singleton_mirror_00138

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_041 :
    (singletonStep singletonLocal136 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal052.state := by
  decide +kernel

theorem singleton_update_041 :
    singletonStep singletonLocal136 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal052 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_041 singleton_mirror_00211

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_042 :
    (singletonStep singletonLocal136 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal049.state := by
  decide +kernel

theorem singleton_update_042 :
    singletonStep singletonLocal136 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal049 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_042 singleton_mirror_00198

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_043 :
    (singletonStep singletonLocal136 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal044.state := by
  decide +kernel

theorem singleton_update_043 :
    singletonStep singletonLocal136 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal044 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_043 singleton_mirror_00174

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_044 :
    (singletonStep singletonLocal138 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal054.state := by
  decide +kernel

theorem singleton_update_044 :
    singletonStep singletonLocal138 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal054 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_044 singleton_mirror_00465

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_045 :
    (singletonStep singletonLocal138 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal065.state := by
  decide +kernel

theorem singleton_update_045 :
    singletonStep singletonLocal138 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal065 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_045 singleton_mirror_00621

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_046 :
    (singletonStep singletonLocal138 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal060.state := by
  decide +kernel

theorem singleton_update_046 :
    singletonStep singletonLocal138 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal060 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_046 singleton_mirror_00537

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_047 :
    (singletonStep singletonLocal138 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal067.state := by
  decide +kernel

theorem singleton_update_047 :
    singletonStep singletonLocal138 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal067 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_047 singleton_mirror_00686

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_048 :
    (singletonStep singletonLocal139 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal068.state := by
  decide +kernel

theorem singleton_update_048 :
    singletonStep singletonLocal139 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal068 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_048 singleton_mirror_00733

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_049 :
    (singletonStep singletonLocal139 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal071.state := by
  decide +kernel

theorem singleton_update_049 :
    singletonStep singletonLocal139 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal071 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_049 singleton_mirror_00785

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_050 :
    (singletonStep singletonLocal139 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal070.state := by
  decide +kernel

theorem singleton_update_050 :
    singletonStep singletonLocal139 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal070 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_050 singleton_mirror_00769

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_051 :
    (singletonStep singletonLocal139 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal074.state := by
  decide +kernel

theorem singleton_update_051 :
    singletonStep singletonLocal139 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal074 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_051 singleton_mirror_00801

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_052 :
    (singletonStep singletonLocal140 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal069.state := by
  decide +kernel

theorem singleton_update_052 :
    singletonStep singletonLocal140 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal069 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_052 singleton_mirror_00753

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_053 :
    (singletonStep singletonLocal140 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal076.state := by
  decide +kernel

theorem singleton_update_053 :
    singletonStep singletonLocal140 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal076 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_053 singleton_mirror_00827

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_054 :
    (singletonStep singletonLocal140 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal075.state := by
  decide +kernel

theorem singleton_update_054 :
    singletonStep singletonLocal140 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal075 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_054 singleton_mirror_00817

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_055 :
    (singletonStep singletonLocal140 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal077.state := by
  decide +kernel

theorem singleton_update_055 :
    singletonStep singletonLocal140 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal077 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_055 singleton_mirror_00843

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_056 :
    (singletonStep singletonLocal141 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal055.state := by
  decide +kernel

theorem singleton_update_056 :
    singletonStep singletonLocal141 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal055 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_056 singleton_mirror_00493

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_057 :
    (singletonStep singletonLocal141 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal021.state := by
  decide +kernel

theorem singleton_update_057 :
    singletonStep singletonLocal141 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal021 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_057 singleton_mirror_00142

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_058 :
    (singletonStep singletonLocal141 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal078.state := by
  decide +kernel

theorem singleton_update_058 :
    singletonStep singletonLocal141 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal078 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_058 singleton_mirror_00857

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_059 :
    (singletonStep singletonLocal141 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal079.state := by
  decide +kernel

theorem singleton_update_059 :
    singletonStep singletonLocal141 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal079 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_059 singleton_mirror_00857

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_060 :
    (singletonStep singletonLocal142 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal057.state := by
  decide +kernel

theorem singleton_update_060 :
    singletonStep singletonLocal142 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal057 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_060 singleton_mirror_00497

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_061 :
    (singletonStep singletonLocal142 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal082.state := by
  decide +kernel

theorem singleton_update_061 :
    singletonStep singletonLocal142 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal082 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_061 singleton_mirror_00867

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_062 :
    (singletonStep singletonLocal142 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal022.state := by
  decide +kernel

theorem singleton_update_062 :
    singletonStep singletonLocal142 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal022 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_062 singleton_mirror_00145

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_063 :
    (singletonStep singletonLocal142 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal083.state := by
  decide +kernel

theorem singleton_update_063 :
    singletonStep singletonLocal142 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal083 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_063 singleton_mirror_00867

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_064 :
    (singletonStep singletonLocal143 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal059.state := by
  decide +kernel

theorem singleton_update_064 :
    singletonStep singletonLocal143 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal059 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_064 singleton_mirror_00510

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_065 :
    (singletonStep singletonLocal143 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal086.state := by
  decide +kernel

theorem singleton_update_065 :
    singletonStep singletonLocal143 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal086 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_065 singleton_mirror_00882

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_066 :
    (singletonStep singletonLocal143 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal073.state := by
  decide +kernel

theorem singleton_update_066 :
    singletonStep singletonLocal143 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal073 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_066 singleton_mirror_00794

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_067 :
    (singletonStep singletonLocal143 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal031.state := by
  decide +kernel

theorem singleton_update_067 :
    singletonStep singletonLocal143 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal031 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_067 singleton_mirror_00156

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_068 :
    (singletonStep singletonLocal144 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal061.state := by
  decide +kernel

theorem singleton_update_068 :
    singletonStep singletonLocal144 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal061 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_068 singleton_mirror_00556

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_069 :
    (singletonStep singletonLocal144 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal088.state := by
  decide +kernel

theorem singleton_update_069 :
    singletonStep singletonLocal144 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal088 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_069 singleton_mirror_00913

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_070 :
    (singletonStep singletonLocal144 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal040.state := by
  decide +kernel

theorem singleton_update_070 :
    singletonStep singletonLocal144 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal040 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_070 singleton_mirror_00168

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_071 :
    (singletonStep singletonLocal144 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal063.state := by
  decide +kernel

theorem singleton_update_071 :
    singletonStep singletonLocal144 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal063 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_071 singleton_mirror_00561

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_072 :
    (singletonStep singletonLocal145 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal090.state := by
  decide +kernel

theorem singleton_update_072 :
    singletonStep singletonLocal145 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal090 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_072 singleton_mirror_00941

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_073 :
    (singletonStep singletonLocal145 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal056.state := by
  decide +kernel

theorem singleton_update_073 :
    singletonStep singletonLocal145 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal056 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_073 singleton_mirror_00493

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_074 :
    (singletonStep singletonLocal145 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal092.state := by
  decide +kernel

theorem singleton_update_074 :
    singletonStep singletonLocal145 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal092 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_074 singleton_mirror_00948

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_075 :
    (singletonStep singletonLocal145 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal093.state := by
  decide +kernel

theorem singleton_update_075 :
    singletonStep singletonLocal145 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal093 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_075 singleton_mirror_00948

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_076 :
    (singletonStep singletonLocal146 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal091.state := by
  decide +kernel

theorem singleton_update_076 :
    singletonStep singletonLocal146 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal091 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_076 singleton_mirror_00944

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_077 :
    (singletonStep singletonLocal146 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal096.state := by
  decide +kernel

theorem singleton_update_077 :
    singletonStep singletonLocal146 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal096 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_077 singleton_mirror_00953

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_078 :
    (singletonStep singletonLocal146 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal058.state := by
  decide +kernel

theorem singleton_update_078 :
    singletonStep singletonLocal146 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal058 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_078 singleton_mirror_00497

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_079 :
    (singletonStep singletonLocal146 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal097.state := by
  decide +kernel

theorem singleton_update_079 :
    singletonStep singletonLocal146 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal097 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_079 singleton_mirror_00953

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_080 :
    (singletonStep singletonLocal147 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal094.state := by
  decide +kernel

theorem singleton_update_080 :
    singletonStep singletonLocal147 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal094 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_080 singleton_mirror_00948

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_081 :
    (singletonStep singletonLocal147 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal080.state := by
  decide +kernel

theorem singleton_update_081 :
    singletonStep singletonLocal147 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal080 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_081 singleton_mirror_00857

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_082 :
    (singletonStep singletonLocal147 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal100.state := by
  decide +kernel

theorem singleton_update_082 :
    singletonStep singletonLocal147 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal100 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_082 singleton_mirror_00964

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_083 :
    (singletonStep singletonLocal147 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal108.state := by
  decide +kernel

theorem singleton_update_083 :
    singletonStep singletonLocal147 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal108 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_083 singleton_mirror_00974

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_084 :
    (singletonStep singletonLocal148 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal095.state := by
  decide +kernel

theorem singleton_update_084 :
    singletonStep singletonLocal148 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal095 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_084 singleton_mirror_00948

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_085 :
    (singletonStep singletonLocal148 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal081.state := by
  decide +kernel

theorem singleton_update_085 :
    singletonStep singletonLocal148 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal081 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_085 singleton_mirror_00857

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_086 :
    (singletonStep singletonLocal148 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal109.state := by
  decide +kernel

theorem singleton_update_086 :
    singletonStep singletonLocal148 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal109 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_086 singleton_mirror_00974

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_087 :
    (singletonStep singletonLocal148 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal101.state := by
  decide +kernel

theorem singleton_update_087 :
    singletonStep singletonLocal148 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal101 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_087 singleton_mirror_00964

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_088 :
    (singletonStep singletonLocal149 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal098.state := by
  decide +kernel

theorem singleton_update_088 :
    singletonStep singletonLocal149 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal098 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_088 singleton_mirror_00953

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_089 :
    (singletonStep singletonLocal149 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal103.state := by
  decide +kernel

theorem singleton_update_089 :
    singletonStep singletonLocal149 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal103 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_089 singleton_mirror_00968

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_090 :
    (singletonStep singletonLocal149 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal084.state := by
  decide +kernel

theorem singleton_update_090 :
    singletonStep singletonLocal149 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal084 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_090 singleton_mirror_00867

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_091 :
    (singletonStep singletonLocal149 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal110.state := by
  decide +kernel

theorem singleton_update_091 :
    singletonStep singletonLocal149 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal110 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_091 singleton_mirror_00978

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_092 :
    (singletonStep singletonLocal150 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal099.state := by
  decide +kernel

theorem singleton_update_092 :
    singletonStep singletonLocal150 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal099 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_092 singleton_mirror_00953

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_093 :
    (singletonStep singletonLocal150 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal111.state := by
  decide +kernel

theorem singleton_update_093 :
    singletonStep singletonLocal150 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal111 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_093 singleton_mirror_00978

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_094 :
    (singletonStep singletonLocal150 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal085.state := by
  decide +kernel

theorem singleton_update_094 :
    singletonStep singletonLocal150 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal085 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_094 singleton_mirror_00867

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_095 :
    (singletonStep singletonLocal150 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal104.state := by
  decide +kernel

theorem singleton_update_095 :
    singletonStep singletonLocal150 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal104 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_095 singleton_mirror_00968

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_096 :
    (singletonStep singletonLocal152 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal112.state := by
  decide +kernel

theorem singleton_update_096 :
    singletonStep singletonLocal152 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal112 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_096 singleton_mirror_01016

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_097 :
    (singletonStep singletonLocal152 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal116.state := by
  decide +kernel

theorem singleton_update_097 :
    singletonStep singletonLocal152 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal116 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_097 singleton_mirror_01037

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_098 :
    (singletonStep singletonLocal152 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal115.state := by
  decide +kernel

theorem singleton_update_098 :
    singletonStep singletonLocal152 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal115 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_098 singleton_mirror_01026

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_099 :
    (singletonStep singletonLocal152 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal066.state := by
  decide +kernel

theorem singleton_update_099 :
    singletonStep singletonLocal152 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal066 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_099 singleton_mirror_00649

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_100 :
    (singletonStep singletonLocal153 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal117.state := by
  decide +kernel

theorem singleton_update_100 :
    singletonStep singletonLocal153 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal117 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_100 singleton_mirror_01052

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_101 :
    (singletonStep singletonLocal153 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal121.state := by
  decide +kernel

theorem singleton_update_101 :
    singletonStep singletonLocal153 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal121 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_101 singleton_mirror_01079

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_102 :
    (singletonStep singletonLocal153 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal118.state := by
  decide +kernel

theorem singleton_update_102 :
    singletonStep singletonLocal153 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal118 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_102 singleton_mirror_01063

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_103 :
    (singletonStep singletonLocal153 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal087.state := by
  decide +kernel

theorem singleton_update_103 :
    singletonStep singletonLocal153 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal087 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_103 singleton_mirror_00895

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_104 :
    (singletonStep singletonLocal154 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal105.state := by
  decide +kernel

theorem singleton_update_104 :
    singletonStep singletonLocal154 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal105 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_104 singleton_mirror_00968

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_105 :
    (singletonStep singletonLocal154 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal119.state := by
  decide +kernel

theorem singleton_update_105 :
    singletonStep singletonLocal154 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal119 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_105 singleton_mirror_01077

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_106 :
    (singletonStep singletonLocal154 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal062.state := by
  decide +kernel

theorem singleton_update_106 :
    singletonStep singletonLocal154 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal062 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_106 singleton_mirror_00556

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_107 :
    (singletonStep singletonLocal154 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal113.state := by
  decide +kernel

theorem singleton_update_107 :
    singletonStep singletonLocal154 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal113 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_107 singleton_mirror_01024

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_108 :
    (singletonStep singletonLocal155 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal114.state := by
  decide +kernel

theorem singleton_update_108 :
    singletonStep singletonLocal155 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal114 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_108 singleton_mirror_01024

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_109 :
    (singletonStep singletonLocal155 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal122.state := by
  decide +kernel

theorem singleton_update_109 :
    singletonStep singletonLocal155 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal122 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_109 singleton_mirror_01087

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_110 :
    (singletonStep singletonLocal155 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal064.state := by
  decide +kernel

theorem singleton_update_110 :
    singletonStep singletonLocal155 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal064 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_110 singleton_mirror_00561

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_111 :
    (singletonStep singletonLocal155 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal106.state := by
  decide +kernel

theorem singleton_update_111 :
    singletonStep singletonLocal155 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal106 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_111 singleton_mirror_00971

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_112 :
    (singletonStep singletonLocal156 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal120.state := by
  decide +kernel

theorem singleton_update_112 :
    singletonStep singletonLocal156 (⟨6, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal120 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_112 singleton_mirror_01077

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_113 :
    (singletonStep singletonLocal156 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal124.state := by
  decide +kernel

theorem singleton_update_113 :
    singletonStep singletonLocal156 (⟨6, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal124 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_113 singleton_mirror_01090

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_114 :
    (singletonStep singletonLocal156 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal089.state := by
  decide +kernel

theorem singleton_update_114 :
    singletonStep singletonLocal156 (⟨6, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal089 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_114 singleton_mirror_00913

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_115 :
    (singletonStep singletonLocal156 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal123.state := by
  decide +kernel

theorem singleton_update_115 :
    singletonStep singletonLocal156 (⟨6, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal123 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_115 singleton_mirror_01087

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_116 :
    (singletonStep singletonLocal157 (⟨0, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal000.state := by
  decide +kernel

theorem singleton_update_116 :
    singletonStep singletonLocal157 (⟨0, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal000 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_116 singleton_mirror_00014

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_117 :
    (singletonStep singletonLocal157 (⟨0, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal102.state := by
  decide +kernel

theorem singleton_update_117 :
    singletonStep singletonLocal157 (⟨0, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal102 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_117 singleton_mirror_00968

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_118 :
    (singletonStep singletonLocal157 (⟨0, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal104.state := by
  decide +kernel

theorem singleton_update_118 :
    singletonStep singletonLocal157 (⟨0, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal104 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_118 singleton_mirror_00968

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_119 :
    (singletonStep singletonLocal157 (⟨0, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal023.state := by
  decide +kernel

theorem singleton_update_119 :
    singletonStep singletonLocal157 (⟨0, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal023 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_119 singleton_mirror_00145

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_120 :
    (singletonStep singletonLocal158 (⟨0, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal002.state := by
  decide +kernel

theorem singleton_update_120 :
    singletonStep singletonLocal158 (⟨0, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal002 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_120 singleton_mirror_00019

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_121 :
    (singletonStep singletonLocal158 (⟨0, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal101.state := by
  decide +kernel

theorem singleton_update_121 :
    singletonStep singletonLocal158 (⟨0, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal101 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_121 singleton_mirror_00964

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_122 :
    (singletonStep singletonLocal158 (⟨0, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal107.state := by
  decide +kernel

theorem singleton_update_122 :
    singletonStep singletonLocal158 (⟨0, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal107 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_122 singleton_mirror_00973

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_123 :
    (singletonStep singletonLocal158 (⟨0, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal025.state := by
  decide +kernel

theorem singleton_update_123 :
    singletonStep singletonLocal158 (⟨0, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal025 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_123 singleton_mirror_00147

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_124 :
    (singletonStep singletonLocal159 (⟨0, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal009.state := by
  decide +kernel

theorem singleton_update_124 :
    singletonStep singletonLocal159 (⟨0, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal009 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_124 singleton_mirror_00096

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_125 :
    (singletonStep singletonLocal159 (⟨0, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal072.state := by
  decide +kernel

theorem singleton_update_125 :
    singletonStep singletonLocal159 (⟨0, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal072 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_125 singleton_mirror_00791

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_126 :
    (singletonStep singletonLocal159 (⟨0, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal053.state := by
  decide +kernel

theorem singleton_update_126 :
    singletonStep singletonLocal159 (⟨0, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal053 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_126 singleton_mirror_00375

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_127 :
    (singletonStep singletonLocal159 (⟨0, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal118.state := by
  decide +kernel

theorem singleton_update_127 :
    singletonStep singletonLocal159 (⟨0, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal118 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_127 singleton_mirror_01063

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_128 :
    (singletonStep singletonLocal160 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal125.state := by
  decide +kernel

theorem singleton_update_128 :
    singletonStep singletonLocal160 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal125 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_128 singleton_mirror_01351

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_129 :
    (singletonStep singletonLocal160 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal130.state := by
  decide +kernel

theorem singleton_update_129 :
    singletonStep singletonLocal160 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal130 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_129 singleton_mirror_01405

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_130 :
    (singletonStep singletonLocal160 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal131.state := by
  decide +kernel

theorem singleton_update_130 :
    singletonStep singletonLocal160 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal131 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_130 singleton_mirror_01405

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_131 :
    (singletonStep singletonLocal160 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal128.state := by
  decide +kernel

theorem singleton_update_131 :
    singletonStep singletonLocal160 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal128 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_131 singleton_mirror_01388

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_132 :
    (singletonStep singletonLocal161 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal126.state := by
  decide +kernel

theorem singleton_update_132 :
    singletonStep singletonLocal161 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal126 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_132 singleton_mirror_01359

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_133 :
    (singletonStep singletonLocal161 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal132.state := by
  decide +kernel

theorem singleton_update_133 :
    singletonStep singletonLocal161 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal132 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_133 singleton_mirror_01415

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_134 :
    (singletonStep singletonLocal161 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal133.state := by
  decide +kernel

theorem singleton_update_134 :
    singletonStep singletonLocal161 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal133 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_134 singleton_mirror_01420

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_135 :
    (singletonStep singletonLocal161 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal129.state := by
  decide +kernel

theorem singleton_update_135 :
    singletonStep singletonLocal161 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal129 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_135 singleton_mirror_01396

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_136 :
    (singletonStep singletonLocal162 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal127.state := by
  decide +kernel

theorem singleton_update_136 :
    singletonStep singletonLocal162 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal127 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_136 singleton_mirror_01362

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_137 :
    (singletonStep singletonLocal162 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal134.state := by
  decide +kernel

theorem singleton_update_137 :
    singletonStep singletonLocal162 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal134 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_137 singleton_mirror_01432

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_138 :
    (singletonStep singletonLocal162 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal135.state := by
  decide +kernel

theorem singleton_update_138 :
    singletonStep singletonLocal162 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal135 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_138 singleton_mirror_01455

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_139 :
    (singletonStep singletonLocal162 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal136.state := by
  decide +kernel

theorem singleton_update_139 :
    singletonStep singletonLocal162 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal136 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_139 singleton_mirror_01471

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_140 :
    (singletonStep singletonLocal163 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal137.state := by
  decide +kernel

theorem singleton_update_140 :
    singletonStep singletonLocal163 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal137 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_140 singleton_mirror_01806

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_141 :
    (singletonStep singletonLocal163 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal139.state := by
  decide +kernel

theorem singleton_update_141 :
    singletonStep singletonLocal163 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal139 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_141 singleton_mirror_02329

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_142 :
    (singletonStep singletonLocal163 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal138.state := by
  decide +kernel

theorem singleton_update_142 :
    singletonStep singletonLocal163 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal138 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_142 singleton_mirror_02209

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_143 :
    (singletonStep singletonLocal163 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal140.state := by
  decide +kernel

theorem singleton_update_143 :
    singletonStep singletonLocal163 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal140 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_143 singleton_mirror_02367

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_144 :
    (singletonStep singletonLocal164 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal145.state := by
  decide +kernel

theorem singleton_update_144 :
    singletonStep singletonLocal164 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal145 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_144 singleton_mirror_02822

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_145 :
    (singletonStep singletonLocal164 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal141.state := by
  decide +kernel

theorem singleton_update_145 :
    singletonStep singletonLocal164 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal141 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_145 singleton_mirror_02681

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_146 :
    (singletonStep singletonLocal164 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal147.state := by
  decide +kernel

theorem singleton_update_146 :
    singletonStep singletonLocal164 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal147 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_146 singleton_mirror_02840

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_147 :
    (singletonStep singletonLocal164 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal148.state := by
  decide +kernel

theorem singleton_update_147 :
    singletonStep singletonLocal164 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal148 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_147 singleton_mirror_02840

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_148 :
    (singletonStep singletonLocal165 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal146.state := by
  decide +kernel

theorem singleton_update_148 :
    singletonStep singletonLocal165 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal146 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_148 singleton_mirror_02826

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_149 :
    (singletonStep singletonLocal165 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal149.state := by
  decide +kernel

theorem singleton_update_149 :
    singletonStep singletonLocal165 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal149 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_149 singleton_mirror_02845

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_150 :
    (singletonStep singletonLocal165 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal142.state := by
  decide +kernel

theorem singleton_update_150 :
    singletonStep singletonLocal165 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal142 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_150 singleton_mirror_02685

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_151 :
    (singletonStep singletonLocal165 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal150.state := by
  decide +kernel

theorem singleton_update_151 :
    singletonStep singletonLocal165 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal150 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_151 singleton_mirror_02845

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_152 :
    (singletonStep singletonLocal166 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal151.state := by
  decide +kernel

theorem singleton_update_152 :
    singletonStep singletonLocal166 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal151 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_152 singleton_mirror_02877

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_153 :
    (singletonStep singletonLocal166 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal153.state := by
  decide +kernel

theorem singleton_update_153 :
    singletonStep singletonLocal166 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal153 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_153 singleton_mirror_02945

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_154 :
    (singletonStep singletonLocal166 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal152.state := by
  decide +kernel

theorem singleton_update_154 :
    singletonStep singletonLocal166 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal152 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_154 singleton_mirror_02909

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_155 :
    (singletonStep singletonLocal166 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal143.state := by
  decide +kernel

theorem singleton_update_155 :
    singletonStep singletonLocal166 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal143 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_155 singleton_mirror_02698

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_156 :
    (singletonStep singletonLocal167 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩).state =
      singletonLocal154.state := by
  decide +kernel

theorem singleton_update_156 :
    singletonStep singletonLocal167 (⟨5, by decide⟩ : Fin 9) ⟨0, by decide⟩ = singletonLocal154 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_156 singleton_mirror_03007

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_157 :
    (singletonStep singletonLocal167 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩).state =
      singletonLocal156.state := by
  decide +kernel

theorem singleton_update_157 :
    singletonStep singletonLocal167 (⟨5, by decide⟩ : Fin 9) ⟨1, by decide⟩ = singletonLocal156 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_157 singleton_mirror_03040

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_158 :
    (singletonStep singletonLocal167 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩).state =
      singletonLocal144.state := by
  decide +kernel

theorem singleton_update_158 :
    singletonStep singletonLocal167 (⟨5, by decide⟩ : Fin 9) ⟨2, by decide⟩ = singletonLocal144 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_158 singleton_mirror_02727

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem singleton_state_159 :
    (singletonStep singletonLocal167 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩).state =
      singletonLocal155.state := by
  decide +kernel

theorem singleton_update_159 :
    singletonStep singletonLocal167 (⟨5, by decide⟩ : Fin 9) ⟨3, by decide⟩ = singletonLocal155 :=
  CanonicalCacheStateEqualityCandidate.singletonStep_eq_of_state_and_mirror _ _ _ _
    singleton_state_159 singleton_mirror_03012

-- Actual context d=16, fullcode=329851, node=15878.
def cache000 : Cache :=
  ⟨![triangleLocal197, triangleLocal197, triangleLocal198, triangleLocal198, triangleLocal195, triangleLocal196, triangleLocal199, triangleLocal200, triangleLocal201, triangleLocal201, triangleLocal203, triangleLocal202, triangleLocal204, triangleLocal204, triangleLocal206, triangleLocal205],
   ![singletonLocal161, singletonLocal163, singletonLocal163, singletonLocal160, singletonLocal161, singletonLocal162, singletonLocal167, singletonLocal162, singletonLocal164, singletonLocal166, singletonLocal165, singletonLocal166, singletonLocal158, singletonLocal159, singletonLocal157, singletonLocal159]⟩

-- Actual context d=17, fullcode=1319404, node=295.
def cache001 : Cache :=
  ⟨![triangleLocal197, triangleLocal197, triangleLocal155, triangleLocal155, triangleLocal195, triangleLocal196, triangleLocal165, triangleLocal166, triangleLocal201, triangleLocal201, triangleLocal182, triangleLocal181, triangleLocal183, triangleLocal183, triangleLocal206, triangleLocal205],
   ![singletonLocal161, singletonLocal137, singletonLocal137, singletonLocal160, singletonLocal161, singletonLocal127, singletonLocal167, singletonLocal127, singletonLocal164, singletonLocal151, singletonLocal165, singletonLocal151, singletonLocal002, singletonLocal159, singletonLocal157, singletonLocal159]⟩

-- Actual context d=17, fullcode=1319405, node=1175.
def cache002 : Cache :=
  ⟨![triangleLocal197, triangleLocal197, triangleLocal156, triangleLocal156, triangleLocal195, triangleLocal196, triangleLocal167, triangleLocal168, triangleLocal201, triangleLocal201, triangleLocal180, triangleLocal179, triangleLocal192, triangleLocal192, triangleLocal206, triangleLocal205],
   ![singletonLocal161, singletonLocal139, singletonLocal139, singletonLocal160, singletonLocal161, singletonLocal134, singletonLocal167, singletonLocal134, singletonLocal164, singletonLocal153, singletonLocal165, singletonLocal153, singletonLocal101, singletonLocal159, singletonLocal157, singletonLocal159]⟩

-- Actual context d=18, fullcode=5277620, node=112.
def cache003 : Cache :=
  ⟨![triangleLocal197, triangleLocal141, triangleLocal156, triangleLocal039, triangleLocal195, triangleLocal140, triangleLocal167, triangleLocal081, triangleLocal201, triangleLocal175, triangleLocal180, triangleLocal138, triangleLocal059, triangleLocal192, triangleLocal188, triangleLocal205],
   ![singletonLocal126, singletonLocal139, singletonLocal139, singletonLocal125, singletonLocal126, singletonLocal134, singletonLocal154, singletonLocal134, singletonLocal145, singletonLocal153, singletonLocal146, singletonLocal153, singletonLocal101, singletonLocal009, singletonLocal157, singletonLocal159]⟩

-- Actual context d=18, fullcode=5277621, node=112.
def cache004 : Cache :=
  ⟨![triangleLocal197, triangleLocal151, triangleLocal156, triangleLocal042, triangleLocal195, triangleLocal149, triangleLocal167, triangleLocal098, triangleLocal201, triangleLocal171, triangleLocal180, triangleLocal137, triangleLocal054, triangleLocal192, triangleLocal185, triangleLocal205],
   ![singletonLocal132, singletonLocal139, singletonLocal139, singletonLocal130, singletonLocal132, singletonLocal134, singletonLocal156, singletonLocal134, singletonLocal141, singletonLocal153, singletonLocal149, singletonLocal153, singletonLocal101, singletonLocal072, singletonLocal157, singletonLocal159]⟩

-- Actual context d=18, fullcode=5277622, node=112.
def cache005 : Cache :=
  ⟨![triangleLocal197, triangleLocal150, triangleLocal156, triangleLocal044, triangleLocal195, triangleLocal147, triangleLocal167, triangleLocal090, triangleLocal201, triangleLocal176, triangleLocal180, triangleLocal130, triangleLocal119, triangleLocal192, triangleLocal194, triangleLocal205],
   ![singletonLocal133, singletonLocal139, singletonLocal139, singletonLocal131, singletonLocal133, singletonLocal134, singletonLocal144, singletonLocal134, singletonLocal147, singletonLocal153, singletonLocal142, singletonLocal153, singletonLocal101, singletonLocal053, singletonLocal157, singletonLocal159]⟩

-- Actual context d=18, fullcode=5277623, node=455.
def cache006 : Cache :=
  ⟨![triangleLocal197, triangleLocal144, triangleLocal156, triangleLocal043, triangleLocal195, triangleLocal143, triangleLocal167, triangleLocal103, triangleLocal201, triangleLocal161, triangleLocal180, triangleLocal115, triangleLocal096, triangleLocal192, triangleLocal189, triangleLocal205],
   ![singletonLocal129, singletonLocal139, singletonLocal139, singletonLocal128, singletonLocal129, singletonLocal134, singletonLocal155, singletonLocal134, singletonLocal148, singletonLocal153, singletonLocal150, singletonLocal153, singletonLocal101, singletonLocal118, singletonLocal157, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110492, node=57.
def cache007 : Cache :=
  ⟨![triangleLocal145, triangleLocal018, triangleLocal156, triangleLocal043, triangleLocal139, triangleLocal003, triangleLocal167, triangleLocal103, triangleLocal177, triangleLocal095, triangleLocal180, triangleLocal115, triangleLocal096, triangleLocal192, triangleLocal073, triangleLocal186],
   ![singletonLocal129, singletonLocal068, singletonLocal068, singletonLocal128, singletonLocal129, singletonLocal010, singletonLocal155, singletonLocal010, singletonLocal148, singletonLocal117, singletonLocal150, singletonLocal117, singletonLocal101, singletonLocal118, singletonLocal000, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110493, node=57.
def cache008 : Cache :=
  ⟨![triangleLocal154, triangleLocal024, triangleLocal156, triangleLocal043, triangleLocal148, triangleLocal016, triangleLocal167, triangleLocal103, triangleLocal162, triangleLocal094, triangleLocal180, triangleLocal115, triangleLocal096, triangleLocal192, triangleLocal063, triangleLocal184],
   ![singletonLocal129, singletonLocal071, singletonLocal071, singletonLocal128, singletonLocal129, singletonLocal030, singletonLocal155, singletonLocal030, singletonLocal148, singletonLocal121, singletonLocal150, singletonLocal121, singletonLocal101, singletonLocal118, singletonLocal102, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110494, node=0.
def cache009 : Cache :=
  ⟨![triangleLocal153, triangleLocal023, triangleLocal156, triangleLocal043, triangleLocal142, triangleLocal014, triangleLocal167, triangleLocal103, triangleLocal178, triangleLocal096, triangleLocal180, triangleLocal115, triangleLocal096, triangleLocal192, triangleLocal113, triangleLocal193],
   ![singletonLocal129, singletonLocal070, singletonLocal070, singletonLocal128, singletonLocal129, singletonLocal047, singletonLocal155, singletonLocal047, singletonLocal148, singletonLocal118, singletonLocal150, singletonLocal118, singletonLocal101, singletonLocal118, singletonLocal104, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110495, node=0.
def cache010 : Cache :=
  ⟨![triangleLocal152, triangleLocal022, triangleLocal156, triangleLocal043, triangleLocal146, triangleLocal012, triangleLocal167, triangleLocal103, triangleLocal172, triangleLocal093, triangleLocal180, triangleLocal115, triangleLocal096, triangleLocal192, triangleLocal052, triangleLocal190],
   ![singletonLocal129, singletonLocal074, singletonLocal074, singletonLocal128, singletonLocal129, singletonLocal048, singletonLocal155, singletonLocal048, singletonLocal148, singletonLocal087, singletonLocal150, singletonLocal087, singletonLocal101, singletonLocal118, singletonLocal023, singletonLocal159]⟩

-- Actual context d=17, fullcode=1319406, node=15876.
def cache011 : Cache :=
  ⟨![triangleLocal197, triangleLocal197, triangleLocal158, triangleLocal158, triangleLocal195, triangleLocal196, triangleLocal160, triangleLocal159, triangleLocal201, triangleLocal201, triangleLocal164, triangleLocal163, triangleLocal187, triangleLocal187, triangleLocal206, triangleLocal205],
   ![singletonLocal161, singletonLocal138, singletonLocal138, singletonLocal160, singletonLocal161, singletonLocal135, singletonLocal167, singletonLocal135, singletonLocal164, singletonLocal152, singletonLocal165, singletonLocal152, singletonLocal107, singletonLocal159, singletonLocal157, singletonLocal159]⟩

-- Actual context d=18, fullcode=5277624, node=1045.
def cache012 : Cache :=
  ⟨![triangleLocal197, triangleLocal141, triangleLocal158, triangleLocal041, triangleLocal195, triangleLocal140, triangleLocal160, triangleLocal080, triangleLocal201, triangleLocal175, triangleLocal164, triangleLocal116, triangleLocal058, triangleLocal187, triangleLocal188, triangleLocal205],
   ![singletonLocal126, singletonLocal138, singletonLocal138, singletonLocal125, singletonLocal126, singletonLocal135, singletonLocal154, singletonLocal135, singletonLocal145, singletonLocal152, singletonLocal146, singletonLocal152, singletonLocal107, singletonLocal009, singletonLocal157, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110496, node=0.
def cache013 : Cache :=
  ⟨![triangleLocal145, triangleLocal005, triangleLocal158, triangleLocal041, triangleLocal139, triangleLocal000, triangleLocal160, triangleLocal080, triangleLocal177, triangleLocal133, triangleLocal164, triangleLocal116, triangleLocal058, triangleLocal187, triangleLocal037, triangleLocal186],
   ![singletonLocal126, singletonLocal054, singletonLocal054, singletonLocal125, singletonLocal126, singletonLocal008, singletonLocal154, singletonLocal008, singletonLocal145, singletonLocal112, singletonLocal146, singletonLocal112, singletonLocal107, singletonLocal009, singletonLocal000, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110497, node=33.
def cache014 : Cache :=
  ⟨![triangleLocal154, triangleLocal010, triangleLocal158, triangleLocal041, triangleLocal148, triangleLocal007, triangleLocal160, triangleLocal080, triangleLocal162, triangleLocal101, triangleLocal164, triangleLocal116, triangleLocal058, triangleLocal187, triangleLocal061, triangleLocal184],
   ![singletonLocal126, singletonLocal065, singletonLocal065, singletonLocal125, singletonLocal126, singletonLocal050, singletonLocal154, singletonLocal050, singletonLocal145, singletonLocal116, singletonLocal146, singletonLocal116, singletonLocal107, singletonLocal009, singletonLocal102, singletonLocal159]⟩

-- Actual context d=20, fullcode=84441988, node=0.
def cache015 : Cache :=
  ⟨![triangleLocal010, triangleLocal010, triangleLocal041, triangleLocal041, triangleLocal007, triangleLocal007, triangleLocal079, triangleLocal080, triangleLocal101, triangleLocal101, triangleLocal117, triangleLocal116, triangleLocal058, triangleLocal058, triangleLocal061, triangleLocal060],
   ![singletonLocal003, singletonLocal065, singletonLocal065, singletonLocal001, singletonLocal003, singletonLocal050, singletonLocal105, singletonLocal050, singletonLocal090, singletonLocal116, singletonLocal091, singletonLocal116, singletonLocal107, singletonLocal009, singletonLocal102, singletonLocal009]⟩

-- Actual context d=20, fullcode=84441989, node=0.
def cache016 : Cache :=
  ⟨![triangleLocal034, triangleLocal010, triangleLocal049, triangleLocal041, triangleLocal025, triangleLocal007, triangleLocal087, triangleLocal080, triangleLocal097, triangleLocal101, triangleLocal114, triangleLocal116, triangleLocal058, triangleLocal076, triangleLocal061, triangleLocal020],
   ![singletonLocal015, singletonLocal065, singletonLocal065, singletonLocal011, singletonLocal015, singletonLocal050, singletonLocal119, singletonLocal050, singletonLocal056, singletonLocal116, singletonLocal096, singletonLocal116, singletonLocal107, singletonLocal009, singletonLocal102, singletonLocal072]⟩

-- Actual context d=20, fullcode=84441990, node=0.
def cache017 : Cache :=
  ⟨![triangleLocal033, triangleLocal010, triangleLocal050, triangleLocal041, triangleLocal029, triangleLocal007, triangleLocal085, triangleLocal080, triangleLocal102, triangleLocal101, triangleLocal108, triangleLocal116, triangleLocal058, triangleLocal038, triangleLocal061, triangleLocal064],
   ![singletonLocal017, singletonLocal065, singletonLocal065, singletonLocal012, singletonLocal017, singletonLocal050, singletonLocal062, singletonLocal050, singletonLocal092, singletonLocal116, singletonLocal058, singletonLocal116, singletonLocal107, singletonLocal009, singletonLocal102, singletonLocal053]⟩

-- Actual context d=20, fullcode=84441991, node=0.
def cache018 : Cache :=
  ⟨![triangleLocal024, triangleLocal010, triangleLocal051, triangleLocal041, triangleLocal016, triangleLocal007, triangleLocal089, triangleLocal080, triangleLocal094, triangleLocal101, triangleLocal111, triangleLocal116, triangleLocal058, triangleLocal075, triangleLocal061, triangleLocal062],
   ![singletonLocal006, singletonLocal065, singletonLocal065, singletonLocal004, singletonLocal006, singletonLocal050, singletonLocal113, singletonLocal050, singletonLocal093, singletonLocal116, singletonLocal097, singletonLocal116, singletonLocal107, singletonLocal009, singletonLocal102, singletonLocal118]⟩

-- Actual context d=19, fullcode=21110498, node=0.
def cache019 : Cache :=
  ⟨![triangleLocal153, triangleLocal009, triangleLocal158, triangleLocal041, triangleLocal142, triangleLocal004, triangleLocal160, triangleLocal080, triangleLocal178, triangleLocal134, triangleLocal164, triangleLocal116, triangleLocal058, triangleLocal187, triangleLocal077, triangleLocal193],
   ![singletonLocal126, singletonLocal060, singletonLocal060, singletonLocal125, singletonLocal126, singletonLocal032, singletonLocal154, singletonLocal032, singletonLocal145, singletonLocal115, singletonLocal146, singletonLocal115, singletonLocal107, singletonLocal009, singletonLocal104, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110499, node=33.
def cache020 : Cache :=
  ⟨![triangleLocal152, triangleLocal008, triangleLocal158, triangleLocal041, triangleLocal146, triangleLocal002, triangleLocal160, triangleLocal080, triangleLocal172, triangleLocal124, triangleLocal164, triangleLocal116, triangleLocal058, triangleLocal187, triangleLocal071, triangleLocal190],
   ![singletonLocal126, singletonLocal067, singletonLocal067, singletonLocal125, singletonLocal126, singletonLocal051, singletonLocal154, singletonLocal051, singletonLocal145, singletonLocal066, singletonLocal146, singletonLocal066, singletonLocal107, singletonLocal009, singletonLocal023, singletonLocal159]⟩

-- Actual context d=20, fullcode=84441996, node=0.
def cache021 : Cache :=
  ⟨![triangleLocal008, triangleLocal008, triangleLocal041, triangleLocal041, triangleLocal002, triangleLocal002, triangleLocal079, triangleLocal080, triangleLocal124, triangleLocal124, triangleLocal117, triangleLocal116, triangleLocal058, triangleLocal058, triangleLocal071, triangleLocal072],
   ![singletonLocal003, singletonLocal067, singletonLocal067, singletonLocal001, singletonLocal003, singletonLocal051, singletonLocal105, singletonLocal051, singletonLocal090, singletonLocal066, singletonLocal091, singletonLocal066, singletonLocal107, singletonLocal009, singletonLocal023, singletonLocal009]⟩

-- Actual context d=20, fullcode=84441997, node=0.
def cache022 : Cache :=
  ⟨![triangleLocal035, triangleLocal008, triangleLocal049, triangleLocal041, triangleLocal030, triangleLocal002, triangleLocal087, triangleLocal080, triangleLocal120, triangleLocal124, triangleLocal114, triangleLocal116, triangleLocal058, triangleLocal076, triangleLocal071, triangleLocal068],
   ![singletonLocal015, singletonLocal067, singletonLocal067, singletonLocal011, singletonLocal015, singletonLocal051, singletonLocal119, singletonLocal051, singletonLocal056, singletonLocal066, singletonLocal096, singletonLocal066, singletonLocal107, singletonLocal009, singletonLocal023, singletonLocal072]⟩

-- Actual context d=20, fullcode=84441998, node=0.
def cache023 : Cache :=
  ⟨![triangleLocal032, triangleLocal008, triangleLocal050, triangleLocal041, triangleLocal027, triangleLocal002, triangleLocal085, triangleLocal080, triangleLocal125, triangleLocal124, triangleLocal108, triangleLocal116, triangleLocal058, triangleLocal038, triangleLocal071, triangleLocal129],
   ![singletonLocal017, singletonLocal067, singletonLocal067, singletonLocal012, singletonLocal017, singletonLocal051, singletonLocal062, singletonLocal051, singletonLocal092, singletonLocal066, singletonLocal058, singletonLocal066, singletonLocal107, singletonLocal009, singletonLocal023, singletonLocal053]⟩

-- Actual context d=20, fullcode=84441999, node=0.
def cache024 : Cache :=
  ⟨![triangleLocal022, triangleLocal008, triangleLocal051, triangleLocal041, triangleLocal012, triangleLocal002, triangleLocal089, triangleLocal080, triangleLocal093, triangleLocal124, triangleLocal111, triangleLocal116, triangleLocal058, triangleLocal075, triangleLocal071, triangleLocal053],
   ![singletonLocal006, singletonLocal067, singletonLocal067, singletonLocal004, singletonLocal006, singletonLocal051, singletonLocal113, singletonLocal051, singletonLocal093, singletonLocal066, singletonLocal097, singletonLocal066, singletonLocal107, singletonLocal009, singletonLocal023, singletonLocal118]⟩

-- Actual context d=18, fullcode=5277625, node=15875.
def cache025 : Cache :=
  ⟨![triangleLocal197, triangleLocal151, triangleLocal158, triangleLocal049, triangleLocal195, triangleLocal149, triangleLocal160, triangleLocal086, triangleLocal201, triangleLocal171, triangleLocal164, triangleLocal112, triangleLocal076, triangleLocal187, triangleLocal185, triangleLocal205],
   ![singletonLocal132, singletonLocal138, singletonLocal138, singletonLocal130, singletonLocal132, singletonLocal135, singletonLocal156, singletonLocal135, singletonLocal141, singletonLocal152, singletonLocal149, singletonLocal152, singletonLocal107, singletonLocal072, singletonLocal157, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110500, node=0.
def cache026 : Cache :=
  ⟨![triangleLocal145, triangleLocal019, triangleLocal158, triangleLocal049, triangleLocal139, triangleLocal006, triangleLocal160, triangleLocal086, triangleLocal177, triangleLocal121, triangleLocal164, triangleLocal112, triangleLocal076, triangleLocal187, triangleLocal066, triangleLocal186],
   ![singletonLocal132, singletonLocal054, singletonLocal054, singletonLocal130, singletonLocal132, singletonLocal008, singletonLocal156, singletonLocal008, singletonLocal141, singletonLocal112, singletonLocal149, singletonLocal112, singletonLocal107, singletonLocal072, singletonLocal000, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110501, node=113.
def cache027 : Cache :=
  ⟨![triangleLocal154, triangleLocal034, triangleLocal158, triangleLocal049, triangleLocal148, triangleLocal026, triangleLocal160, triangleLocal086, triangleLocal162, triangleLocal097, triangleLocal164, triangleLocal112, triangleLocal076, triangleLocal187, triangleLocal021, triangleLocal184],
   ![singletonLocal132, singletonLocal065, singletonLocal065, singletonLocal130, singletonLocal132, singletonLocal050, singletonLocal156, singletonLocal050, singletonLocal141, singletonLocal116, singletonLocal149, singletonLocal116, singletonLocal107, singletonLocal072, singletonLocal102, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442004, node=9.
def cache028 : Cache :=
  ⟨![triangleLocal010, triangleLocal034, triangleLocal041, triangleLocal049, triangleLocal007, triangleLocal026, triangleLocal079, triangleLocal086, triangleLocal101, triangleLocal097, triangleLocal117, triangleLocal112, triangleLocal076, triangleLocal058, triangleLocal021, triangleLocal060],
   ![singletonLocal016, singletonLocal065, singletonLocal065, singletonLocal013, singletonLocal016, singletonLocal050, singletonLocal120, singletonLocal050, singletonLocal055, singletonLocal116, singletonLocal098, singletonLocal116, singletonLocal107, singletonLocal072, singletonLocal102, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442005, node=0.
def cache029 : Cache :=
  ⟨![triangleLocal034, triangleLocal034, triangleLocal049, triangleLocal049, triangleLocal025, triangleLocal026, triangleLocal087, triangleLocal086, triangleLocal097, triangleLocal097, triangleLocal114, triangleLocal112, triangleLocal076, triangleLocal076, triangleLocal021, triangleLocal020],
   ![singletonLocal039, singletonLocal065, singletonLocal065, singletonLocal037, singletonLocal039, singletonLocal050, singletonLocal124, singletonLocal050, singletonLocal021, singletonLocal116, singletonLocal103, singletonLocal116, singletonLocal107, singletonLocal072, singletonLocal102, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442006, node=0.
def cache030 : Cache :=
  ⟨![triangleLocal033, triangleLocal034, triangleLocal050, triangleLocal049, triangleLocal029, triangleLocal026, triangleLocal085, triangleLocal086, triangleLocal102, triangleLocal097, triangleLocal108, triangleLocal112, triangleLocal076, triangleLocal038, triangleLocal021, triangleLocal064],
   ![singletonLocal045, singletonLocal065, singletonLocal065, singletonLocal042, singletonLocal045, singletonLocal050, singletonLocal089, singletonLocal050, singletonLocal078, singletonLocal116, singletonLocal084, singletonLocal116, singletonLocal107, singletonLocal072, singletonLocal102, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442007, node=0.
def cache031 : Cache :=
  ⟨![triangleLocal024, triangleLocal034, triangleLocal051, triangleLocal049, triangleLocal016, triangleLocal026, triangleLocal089, triangleLocal086, triangleLocal094, triangleLocal097, triangleLocal111, triangleLocal112, triangleLocal076, triangleLocal075, triangleLocal021, triangleLocal062],
   ![singletonLocal034, singletonLocal065, singletonLocal065, singletonLocal028, singletonLocal034, singletonLocal050, singletonLocal123, singletonLocal050, singletonLocal079, singletonLocal116, singletonLocal110, singletonLocal116, singletonLocal107, singletonLocal072, singletonLocal102, singletonLocal118]⟩

-- Actual context d=19, fullcode=21110502, node=0.
def cache032 : Cache :=
  ⟨![triangleLocal153, triangleLocal036, triangleLocal158, triangleLocal049, triangleLocal142, triangleLocal015, triangleLocal160, triangleLocal086, triangleLocal178, triangleLocal123, triangleLocal164, triangleLocal112, triangleLocal076, triangleLocal187, triangleLocal069, triangleLocal193],
   ![singletonLocal132, singletonLocal060, singletonLocal060, singletonLocal130, singletonLocal132, singletonLocal032, singletonLocal156, singletonLocal032, singletonLocal141, singletonLocal115, singletonLocal149, singletonLocal115, singletonLocal107, singletonLocal072, singletonLocal104, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110503, node=113.
def cache033 : Cache :=
  ⟨![triangleLocal152, triangleLocal035, triangleLocal158, triangleLocal049, triangleLocal146, triangleLocal030, triangleLocal160, triangleLocal086, triangleLocal172, triangleLocal120, triangleLocal164, triangleLocal112, triangleLocal076, triangleLocal187, triangleLocal067, triangleLocal190],
   ![singletonLocal132, singletonLocal067, singletonLocal067, singletonLocal130, singletonLocal132, singletonLocal051, singletonLocal156, singletonLocal051, singletonLocal141, singletonLocal066, singletonLocal149, singletonLocal066, singletonLocal107, singletonLocal072, singletonLocal023, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442012, node=9.
def cache034 : Cache :=
  ⟨![triangleLocal008, triangleLocal035, triangleLocal041, triangleLocal049, triangleLocal002, triangleLocal030, triangleLocal079, triangleLocal086, triangleLocal124, triangleLocal120, triangleLocal117, triangleLocal112, triangleLocal076, triangleLocal058, triangleLocal067, triangleLocal072],
   ![singletonLocal016, singletonLocal067, singletonLocal067, singletonLocal013, singletonLocal016, singletonLocal051, singletonLocal120, singletonLocal051, singletonLocal055, singletonLocal066, singletonLocal098, singletonLocal066, singletonLocal107, singletonLocal072, singletonLocal023, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442013, node=0.
def cache035 : Cache :=
  ⟨![triangleLocal035, triangleLocal035, triangleLocal049, triangleLocal049, triangleLocal030, triangleLocal030, triangleLocal087, triangleLocal086, triangleLocal120, triangleLocal120, triangleLocal114, triangleLocal112, triangleLocal076, triangleLocal076, triangleLocal067, triangleLocal068],
   ![singletonLocal039, singletonLocal067, singletonLocal067, singletonLocal037, singletonLocal039, singletonLocal051, singletonLocal124, singletonLocal051, singletonLocal021, singletonLocal066, singletonLocal103, singletonLocal066, singletonLocal107, singletonLocal072, singletonLocal023, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442014, node=0.
def cache036 : Cache :=
  ⟨![triangleLocal032, triangleLocal035, triangleLocal050, triangleLocal049, triangleLocal027, triangleLocal030, triangleLocal085, triangleLocal086, triangleLocal125, triangleLocal120, triangleLocal108, triangleLocal112, triangleLocal076, triangleLocal038, triangleLocal067, triangleLocal129],
   ![singletonLocal045, singletonLocal067, singletonLocal067, singletonLocal042, singletonLocal045, singletonLocal051, singletonLocal089, singletonLocal051, singletonLocal078, singletonLocal066, singletonLocal084, singletonLocal066, singletonLocal107, singletonLocal072, singletonLocal023, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442015, node=0.
def cache037 : Cache :=
  ⟨![triangleLocal022, triangleLocal035, triangleLocal051, triangleLocal049, triangleLocal012, triangleLocal030, triangleLocal089, triangleLocal086, triangleLocal093, triangleLocal120, triangleLocal111, triangleLocal112, triangleLocal076, triangleLocal075, triangleLocal067, triangleLocal053],
   ![singletonLocal034, singletonLocal067, singletonLocal067, singletonLocal028, singletonLocal034, singletonLocal051, singletonLocal123, singletonLocal051, singletonLocal079, singletonLocal066, singletonLocal110, singletonLocal066, singletonLocal107, singletonLocal072, singletonLocal023, singletonLocal118]⟩

-- Actual context d=18, fullcode=5277626, node=3029.
def cache038 : Cache :=
  ⟨![triangleLocal197, triangleLocal150, triangleLocal158, triangleLocal050, triangleLocal195, triangleLocal147, triangleLocal160, triangleLocal084, triangleLocal201, triangleLocal176, triangleLocal164, triangleLocal106, triangleLocal038, triangleLocal187, triangleLocal194, triangleLocal205],
   ![singletonLocal133, singletonLocal138, singletonLocal138, singletonLocal131, singletonLocal133, singletonLocal135, singletonLocal144, singletonLocal135, singletonLocal147, singletonLocal152, singletonLocal142, singletonLocal152, singletonLocal107, singletonLocal053, singletonLocal157, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110504, node=0.
def cache039 : Cache :=
  ⟨![triangleLocal145, triangleLocal017, triangleLocal158, triangleLocal050, triangleLocal139, triangleLocal001, triangleLocal160, triangleLocal084, triangleLocal177, triangleLocal135, triangleLocal164, triangleLocal106, triangleLocal038, triangleLocal187, triangleLocal074, triangleLocal186],
   ![singletonLocal133, singletonLocal054, singletonLocal054, singletonLocal131, singletonLocal133, singletonLocal008, singletonLocal144, singletonLocal008, singletonLocal147, singletonLocal112, singletonLocal142, singletonLocal112, singletonLocal107, singletonLocal053, singletonLocal000, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110505, node=22.
def cache040 : Cache :=
  ⟨![triangleLocal154, triangleLocal033, triangleLocal158, triangleLocal050, triangleLocal148, triangleLocal029, triangleLocal160, triangleLocal084, triangleLocal162, triangleLocal102, triangleLocal164, triangleLocal106, triangleLocal038, triangleLocal187, triangleLocal065, triangleLocal184],
   ![singletonLocal133, singletonLocal065, singletonLocal065, singletonLocal131, singletonLocal133, singletonLocal050, singletonLocal144, singletonLocal050, singletonLocal147, singletonLocal116, singletonLocal142, singletonLocal116, singletonLocal107, singletonLocal053, singletonLocal102, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442020, node=9.
def cache041 : Cache :=
  ⟨![triangleLocal010, triangleLocal033, triangleLocal041, triangleLocal050, triangleLocal007, triangleLocal029, triangleLocal079, triangleLocal084, triangleLocal101, triangleLocal102, triangleLocal117, triangleLocal106, triangleLocal038, triangleLocal058, triangleLocal065, triangleLocal060],
   ![singletonLocal018, singletonLocal065, singletonLocal065, singletonLocal014, singletonLocal018, singletonLocal050, singletonLocal061, singletonLocal050, singletonLocal094, singletonLocal116, singletonLocal057, singletonLocal116, singletonLocal107, singletonLocal053, singletonLocal102, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442021, node=9.
def cache042 : Cache :=
  ⟨![triangleLocal034, triangleLocal033, triangleLocal049, triangleLocal050, triangleLocal025, triangleLocal029, triangleLocal087, triangleLocal084, triangleLocal097, triangleLocal102, triangleLocal114, triangleLocal106, triangleLocal038, triangleLocal076, triangleLocal065, triangleLocal020],
   ![singletonLocal046, singletonLocal065, singletonLocal065, singletonLocal043, singletonLocal046, singletonLocal050, singletonLocal088, singletonLocal050, singletonLocal080, singletonLocal116, singletonLocal082, singletonLocal116, singletonLocal107, singletonLocal053, singletonLocal102, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442022, node=0.
def cache043 : Cache :=
  ⟨![triangleLocal033, triangleLocal033, triangleLocal050, triangleLocal050, triangleLocal029, triangleLocal029, triangleLocal085, triangleLocal084, triangleLocal102, triangleLocal102, triangleLocal108, triangleLocal106, triangleLocal038, triangleLocal038, triangleLocal065, triangleLocal064],
   ![singletonLocal041, singletonLocal065, singletonLocal065, singletonLocal038, singletonLocal041, singletonLocal050, singletonLocal040, singletonLocal050, singletonLocal100, singletonLocal116, singletonLocal022, singletonLocal116, singletonLocal107, singletonLocal053, singletonLocal102, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442023, node=0.
def cache044 : Cache :=
  ⟨![triangleLocal024, triangleLocal033, triangleLocal051, triangleLocal050, triangleLocal016, triangleLocal029, triangleLocal089, triangleLocal084, triangleLocal094, triangleLocal102, triangleLocal111, triangleLocal106, triangleLocal038, triangleLocal075, triangleLocal065, triangleLocal062],
   ![singletonLocal036, singletonLocal065, singletonLocal065, singletonLocal029, singletonLocal036, singletonLocal050, singletonLocal063, singletonLocal050, singletonLocal108, singletonLocal116, singletonLocal083, singletonLocal116, singletonLocal107, singletonLocal053, singletonLocal102, singletonLocal118]⟩

-- Actual context d=19, fullcode=21110506, node=0.
def cache045 : Cache :=
  ⟨![triangleLocal153, triangleLocal031, triangleLocal158, triangleLocal050, triangleLocal142, triangleLocal011, triangleLocal160, triangleLocal084, triangleLocal178, triangleLocal136, triangleLocal164, triangleLocal106, triangleLocal038, triangleLocal187, triangleLocal056, triangleLocal193],
   ![singletonLocal133, singletonLocal060, singletonLocal060, singletonLocal131, singletonLocal133, singletonLocal032, singletonLocal144, singletonLocal032, singletonLocal147, singletonLocal115, singletonLocal142, singletonLocal115, singletonLocal107, singletonLocal053, singletonLocal104, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110507, node=22.
def cache046 : Cache :=
  ⟨![triangleLocal152, triangleLocal032, triangleLocal158, triangleLocal050, triangleLocal146, triangleLocal028, triangleLocal160, triangleLocal084, triangleLocal172, triangleLocal125, triangleLocal164, triangleLocal106, triangleLocal038, triangleLocal187, triangleLocal128, triangleLocal190],
   ![singletonLocal133, singletonLocal067, singletonLocal067, singletonLocal131, singletonLocal133, singletonLocal051, singletonLocal144, singletonLocal051, singletonLocal147, singletonLocal066, singletonLocal142, singletonLocal066, singletonLocal107, singletonLocal053, singletonLocal023, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442028, node=9.
def cache047 : Cache :=
  ⟨![triangleLocal008, triangleLocal032, triangleLocal041, triangleLocal050, triangleLocal002, triangleLocal028, triangleLocal079, triangleLocal084, triangleLocal124, triangleLocal125, triangleLocal117, triangleLocal106, triangleLocal038, triangleLocal058, triangleLocal128, triangleLocal072],
   ![singletonLocal018, singletonLocal067, singletonLocal067, singletonLocal014, singletonLocal018, singletonLocal051, singletonLocal061, singletonLocal051, singletonLocal094, singletonLocal066, singletonLocal057, singletonLocal066, singletonLocal107, singletonLocal053, singletonLocal023, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442029, node=9.
def cache048 : Cache :=
  ⟨![triangleLocal035, triangleLocal032, triangleLocal049, triangleLocal050, triangleLocal030, triangleLocal028, triangleLocal087, triangleLocal084, triangleLocal120, triangleLocal125, triangleLocal114, triangleLocal106, triangleLocal038, triangleLocal076, triangleLocal128, triangleLocal068],
   ![singletonLocal046, singletonLocal067, singletonLocal067, singletonLocal043, singletonLocal046, singletonLocal051, singletonLocal088, singletonLocal051, singletonLocal080, singletonLocal066, singletonLocal082, singletonLocal066, singletonLocal107, singletonLocal053, singletonLocal023, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442030, node=0.
def cache049 : Cache :=
  ⟨![triangleLocal032, triangleLocal032, triangleLocal050, triangleLocal050, triangleLocal027, triangleLocal028, triangleLocal085, triangleLocal084, triangleLocal125, triangleLocal125, triangleLocal108, triangleLocal106, triangleLocal038, triangleLocal038, triangleLocal128, triangleLocal129],
   ![singletonLocal041, singletonLocal067, singletonLocal067, singletonLocal038, singletonLocal041, singletonLocal051, singletonLocal040, singletonLocal051, singletonLocal100, singletonLocal066, singletonLocal022, singletonLocal066, singletonLocal107, singletonLocal053, singletonLocal023, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442031, node=0.
def cache050 : Cache :=
  ⟨![triangleLocal022, triangleLocal032, triangleLocal051, triangleLocal050, triangleLocal012, triangleLocal028, triangleLocal089, triangleLocal084, triangleLocal093, triangleLocal125, triangleLocal111, triangleLocal106, triangleLocal038, triangleLocal075, triangleLocal128, triangleLocal053],
   ![singletonLocal036, singletonLocal067, singletonLocal067, singletonLocal029, singletonLocal036, singletonLocal051, singletonLocal063, singletonLocal051, singletonLocal108, singletonLocal066, singletonLocal083, singletonLocal066, singletonLocal107, singletonLocal053, singletonLocal023, singletonLocal118]⟩

-- Actual context d=18, fullcode=5277627, node=14936.
def cache051 : Cache :=
  ⟨![triangleLocal197, triangleLocal144, triangleLocal158, triangleLocal051, triangleLocal195, triangleLocal143, triangleLocal160, triangleLocal088, triangleLocal201, triangleLocal161, triangleLocal164, triangleLocal110, triangleLocal075, triangleLocal187, triangleLocal189, triangleLocal205],
   ![singletonLocal129, singletonLocal138, singletonLocal138, singletonLocal128, singletonLocal129, singletonLocal135, singletonLocal155, singletonLocal135, singletonLocal148, singletonLocal152, singletonLocal150, singletonLocal152, singletonLocal107, singletonLocal118, singletonLocal157, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110508, node=0.
def cache052 : Cache :=
  ⟨![triangleLocal145, triangleLocal018, triangleLocal158, triangleLocal051, triangleLocal139, triangleLocal003, triangleLocal160, triangleLocal088, triangleLocal177, triangleLocal095, triangleLocal164, triangleLocal110, triangleLocal075, triangleLocal187, triangleLocal073, triangleLocal186],
   ![singletonLocal129, singletonLocal054, singletonLocal054, singletonLocal128, singletonLocal129, singletonLocal008, singletonLocal155, singletonLocal008, singletonLocal148, singletonLocal112, singletonLocal150, singletonLocal112, singletonLocal107, singletonLocal118, singletonLocal000, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110509, node=162.
def cache053 : Cache :=
  ⟨![triangleLocal154, triangleLocal024, triangleLocal158, triangleLocal051, triangleLocal148, triangleLocal016, triangleLocal160, triangleLocal088, triangleLocal162, triangleLocal094, triangleLocal164, triangleLocal110, triangleLocal075, triangleLocal187, triangleLocal063, triangleLocal184],
   ![singletonLocal129, singletonLocal065, singletonLocal065, singletonLocal128, singletonLocal129, singletonLocal050, singletonLocal155, singletonLocal050, singletonLocal148, singletonLocal116, singletonLocal150, singletonLocal116, singletonLocal107, singletonLocal118, singletonLocal102, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442036, node=9.
def cache054 : Cache :=
  ⟨![triangleLocal010, triangleLocal024, triangleLocal041, triangleLocal051, triangleLocal007, triangleLocal016, triangleLocal079, triangleLocal088, triangleLocal101, triangleLocal094, triangleLocal117, triangleLocal110, triangleLocal075, triangleLocal058, triangleLocal063, triangleLocal060],
   ![singletonLocal007, singletonLocal065, singletonLocal065, singletonLocal005, singletonLocal007, singletonLocal050, singletonLocal114, singletonLocal050, singletonLocal095, singletonLocal116, singletonLocal099, singletonLocal116, singletonLocal107, singletonLocal118, singletonLocal102, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442037, node=9.
def cache055 : Cache :=
  ⟨![triangleLocal034, triangleLocal024, triangleLocal049, triangleLocal051, triangleLocal025, triangleLocal016, triangleLocal087, triangleLocal088, triangleLocal097, triangleLocal094, triangleLocal114, triangleLocal110, triangleLocal075, triangleLocal076, triangleLocal063, triangleLocal020],
   ![singletonLocal033, singletonLocal065, singletonLocal065, singletonLocal026, singletonLocal033, singletonLocal050, singletonLocal122, singletonLocal050, singletonLocal081, singletonLocal116, singletonLocal111, singletonLocal116, singletonLocal107, singletonLocal118, singletonLocal102, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442038, node=9.
def cache056 : Cache :=
  ⟨![triangleLocal033, triangleLocal024, triangleLocal050, triangleLocal051, triangleLocal029, triangleLocal016, triangleLocal085, triangleLocal088, triangleLocal102, triangleLocal094, triangleLocal108, triangleLocal110, triangleLocal075, triangleLocal038, triangleLocal063, triangleLocal064],
   ![singletonLocal035, singletonLocal065, singletonLocal065, singletonLocal027, singletonLocal035, singletonLocal050, singletonLocal064, singletonLocal050, singletonLocal109, singletonLocal116, singletonLocal085, singletonLocal116, singletonLocal107, singletonLocal118, singletonLocal102, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442039, node=0.
def cache057 : Cache :=
  ⟨![triangleLocal024, triangleLocal024, triangleLocal051, triangleLocal051, triangleLocal016, triangleLocal016, triangleLocal089, triangleLocal088, triangleLocal094, triangleLocal094, triangleLocal111, triangleLocal110, triangleLocal075, triangleLocal075, triangleLocal063, triangleLocal062],
   ![singletonLocal024, singletonLocal065, singletonLocal065, singletonLocal020, singletonLocal024, singletonLocal050, singletonLocal106, singletonLocal050, singletonLocal101, singletonLocal116, singletonLocal104, singletonLocal116, singletonLocal107, singletonLocal118, singletonLocal102, singletonLocal118]⟩

-- Actual context d=19, fullcode=21110510, node=162.
def cache058 : Cache :=
  ⟨![triangleLocal153, triangleLocal023, triangleLocal158, triangleLocal051, triangleLocal142, triangleLocal014, triangleLocal160, triangleLocal088, triangleLocal178, triangleLocal096, triangleLocal164, triangleLocal110, triangleLocal075, triangleLocal187, triangleLocal113, triangleLocal193],
   ![singletonLocal129, singletonLocal060, singletonLocal060, singletonLocal128, singletonLocal129, singletonLocal032, singletonLocal155, singletonLocal032, singletonLocal148, singletonLocal115, singletonLocal150, singletonLocal115, singletonLocal107, singletonLocal118, singletonLocal104, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442040, node=9.
def cache059 : Cache :=
  ⟨![triangleLocal009, triangleLocal023, triangleLocal041, triangleLocal051, triangleLocal004, triangleLocal014, triangleLocal079, triangleLocal088, triangleLocal134, triangleLocal096, triangleLocal117, triangleLocal110, triangleLocal075, triangleLocal058, triangleLocal113, triangleLocal078],
   ![singletonLocal007, singletonLocal060, singletonLocal060, singletonLocal005, singletonLocal007, singletonLocal032, singletonLocal114, singletonLocal032, singletonLocal095, singletonLocal115, singletonLocal099, singletonLocal115, singletonLocal107, singletonLocal118, singletonLocal104, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442041, node=9.
def cache060 : Cache :=
  ⟨![triangleLocal036, triangleLocal023, triangleLocal049, triangleLocal051, triangleLocal015, triangleLocal014, triangleLocal087, triangleLocal088, triangleLocal123, triangleLocal096, triangleLocal114, triangleLocal110, triangleLocal075, triangleLocal076, triangleLocal113, triangleLocal070],
   ![singletonLocal033, singletonLocal060, singletonLocal060, singletonLocal026, singletonLocal033, singletonLocal032, singletonLocal122, singletonLocal032, singletonLocal081, singletonLocal115, singletonLocal111, singletonLocal115, singletonLocal107, singletonLocal118, singletonLocal104, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442042, node=9.
def cache061 : Cache :=
  ⟨![triangleLocal031, triangleLocal023, triangleLocal050, triangleLocal051, triangleLocal011, triangleLocal014, triangleLocal085, triangleLocal088, triangleLocal136, triangleLocal096, triangleLocal108, triangleLocal110, triangleLocal075, triangleLocal038, triangleLocal113, triangleLocal055],
   ![singletonLocal035, singletonLocal060, singletonLocal060, singletonLocal027, singletonLocal035, singletonLocal032, singletonLocal064, singletonLocal032, singletonLocal109, singletonLocal115, singletonLocal085, singletonLocal115, singletonLocal107, singletonLocal118, singletonLocal104, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442043, node=0.
def cache062 : Cache :=
  ⟨![triangleLocal023, triangleLocal023, triangleLocal051, triangleLocal051, triangleLocal013, triangleLocal014, triangleLocal089, triangleLocal088, triangleLocal096, triangleLocal096, triangleLocal111, triangleLocal110, triangleLocal075, triangleLocal075, triangleLocal113, triangleLocal115],
   ![singletonLocal024, singletonLocal060, singletonLocal060, singletonLocal020, singletonLocal024, singletonLocal032, singletonLocal106, singletonLocal032, singletonLocal101, singletonLocal115, singletonLocal104, singletonLocal115, singletonLocal107, singletonLocal118, singletonLocal104, singletonLocal118]⟩

-- Actual context d=19, fullcode=21110511, node=162.
def cache063 : Cache :=
  ⟨![triangleLocal152, triangleLocal022, triangleLocal158, triangleLocal051, triangleLocal146, triangleLocal012, triangleLocal160, triangleLocal088, triangleLocal172, triangleLocal093, triangleLocal164, triangleLocal110, triangleLocal075, triangleLocal187, triangleLocal052, triangleLocal190],
   ![singletonLocal129, singletonLocal067, singletonLocal067, singletonLocal128, singletonLocal129, singletonLocal051, singletonLocal155, singletonLocal051, singletonLocal148, singletonLocal066, singletonLocal150, singletonLocal066, singletonLocal107, singletonLocal118, singletonLocal023, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442044, node=9.
def cache064 : Cache :=
  ⟨![triangleLocal008, triangleLocal022, triangleLocal041, triangleLocal051, triangleLocal002, triangleLocal012, triangleLocal079, triangleLocal088, triangleLocal124, triangleLocal093, triangleLocal117, triangleLocal110, triangleLocal075, triangleLocal058, triangleLocal052, triangleLocal072],
   ![singletonLocal007, singletonLocal067, singletonLocal067, singletonLocal005, singletonLocal007, singletonLocal051, singletonLocal114, singletonLocal051, singletonLocal095, singletonLocal066, singletonLocal099, singletonLocal066, singletonLocal107, singletonLocal118, singletonLocal023, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442045, node=9.
def cache065 : Cache :=
  ⟨![triangleLocal035, triangleLocal022, triangleLocal049, triangleLocal051, triangleLocal030, triangleLocal012, triangleLocal087, triangleLocal088, triangleLocal120, triangleLocal093, triangleLocal114, triangleLocal110, triangleLocal075, triangleLocal076, triangleLocal052, triangleLocal068],
   ![singletonLocal033, singletonLocal067, singletonLocal067, singletonLocal026, singletonLocal033, singletonLocal051, singletonLocal122, singletonLocal051, singletonLocal081, singletonLocal066, singletonLocal111, singletonLocal066, singletonLocal107, singletonLocal118, singletonLocal023, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442046, node=9.
def cache066 : Cache :=
  ⟨![triangleLocal032, triangleLocal022, triangleLocal050, triangleLocal051, triangleLocal027, triangleLocal012, triangleLocal085, triangleLocal088, triangleLocal125, triangleLocal093, triangleLocal108, triangleLocal110, triangleLocal075, triangleLocal038, triangleLocal052, triangleLocal129],
   ![singletonLocal035, singletonLocal067, singletonLocal067, singletonLocal027, singletonLocal035, singletonLocal051, singletonLocal064, singletonLocal051, singletonLocal109, singletonLocal066, singletonLocal085, singletonLocal066, singletonLocal107, singletonLocal118, singletonLocal023, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442047, node=0.
def cache067 : Cache :=
  ⟨![triangleLocal022, triangleLocal022, triangleLocal051, triangleLocal051, triangleLocal012, triangleLocal012, triangleLocal089, triangleLocal088, triangleLocal093, triangleLocal093, triangleLocal111, triangleLocal110, triangleLocal075, triangleLocal075, triangleLocal052, triangleLocal053],
   ![singletonLocal024, singletonLocal067, singletonLocal067, singletonLocal020, singletonLocal024, singletonLocal051, singletonLocal106, singletonLocal051, singletonLocal101, singletonLocal066, singletonLocal104, singletonLocal066, singletonLocal107, singletonLocal118, singletonLocal023, singletonLocal118]⟩

-- Actual context d=17, fullcode=1319407, node=15877.
def cache068 : Cache :=
  ⟨![triangleLocal197, triangleLocal197, triangleLocal157, triangleLocal157, triangleLocal195, triangleLocal196, triangleLocal169, triangleLocal170, triangleLocal201, triangleLocal201, triangleLocal174, triangleLocal173, triangleLocal191, triangleLocal191, triangleLocal206, triangleLocal205],
   ![singletonLocal161, singletonLocal140, singletonLocal140, singletonLocal160, singletonLocal161, singletonLocal136, singletonLocal167, singletonLocal136, singletonLocal164, singletonLocal143, singletonLocal165, singletonLocal143, singletonLocal025, singletonLocal159, singletonLocal157, singletonLocal159]⟩

-- Actual context d=18, fullcode=5277628, node=1045.
def cache069 : Cache :=
  ⟨![triangleLocal197, triangleLocal141, triangleLocal157, triangleLocal040, triangleLocal195, triangleLocal140, triangleLocal169, triangleLocal083, triangleLocal201, triangleLocal175, triangleLocal174, triangleLocal131, triangleLocal057, triangleLocal191, triangleLocal188, triangleLocal205],
   ![singletonLocal126, singletonLocal140, singletonLocal140, singletonLocal125, singletonLocal126, singletonLocal136, singletonLocal154, singletonLocal136, singletonLocal145, singletonLocal143, singletonLocal146, singletonLocal143, singletonLocal025, singletonLocal009, singletonLocal157, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110512, node=0.
def cache070 : Cache :=
  ⟨![triangleLocal145, triangleLocal005, triangleLocal157, triangleLocal040, triangleLocal139, triangleLocal000, triangleLocal169, triangleLocal083, triangleLocal177, triangleLocal133, triangleLocal174, triangleLocal131, triangleLocal057, triangleLocal191, triangleLocal037, triangleLocal186],
   ![singletonLocal126, singletonLocal069, singletonLocal069, singletonLocal125, singletonLocal126, singletonLocal019, singletonLocal154, singletonLocal019, singletonLocal145, singletonLocal059, singletonLocal146, singletonLocal059, singletonLocal025, singletonLocal009, singletonLocal000, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110513, node=33.
def cache071 : Cache :=
  ⟨![triangleLocal154, triangleLocal010, triangleLocal157, triangleLocal040, triangleLocal148, triangleLocal007, triangleLocal169, triangleLocal083, triangleLocal162, triangleLocal101, triangleLocal174, triangleLocal131, triangleLocal057, triangleLocal191, triangleLocal061, triangleLocal184],
   ![singletonLocal126, singletonLocal076, singletonLocal076, singletonLocal125, singletonLocal126, singletonLocal052, singletonLocal154, singletonLocal052, singletonLocal145, singletonLocal086, singletonLocal146, singletonLocal086, singletonLocal025, singletonLocal009, singletonLocal102, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442052, node=0.
def cache072 : Cache :=
  ⟨![triangleLocal010, triangleLocal010, triangleLocal040, triangleLocal040, triangleLocal007, triangleLocal007, triangleLocal082, triangleLocal083, triangleLocal101, triangleLocal101, triangleLocal132, triangleLocal131, triangleLocal057, triangleLocal057, triangleLocal061, triangleLocal060],
   ![singletonLocal003, singletonLocal076, singletonLocal076, singletonLocal001, singletonLocal003, singletonLocal052, singletonLocal105, singletonLocal052, singletonLocal090, singletonLocal086, singletonLocal091, singletonLocal086, singletonLocal025, singletonLocal009, singletonLocal102, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442053, node=0.
def cache073 : Cache :=
  ⟨![triangleLocal034, triangleLocal010, triangleLocal046, triangleLocal040, triangleLocal025, triangleLocal007, triangleLocal099, triangleLocal083, triangleLocal097, triangleLocal101, triangleLocal129, triangleLocal131, triangleLocal057, triangleLocal122, triangleLocal061, triangleLocal020],
   ![singletonLocal015, singletonLocal076, singletonLocal076, singletonLocal011, singletonLocal015, singletonLocal052, singletonLocal119, singletonLocal052, singletonLocal056, singletonLocal086, singletonLocal096, singletonLocal086, singletonLocal025, singletonLocal009, singletonLocal102, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442054, node=0.
def cache074 : Cache :=
  ⟨![triangleLocal033, triangleLocal010, triangleLocal048, triangleLocal040, triangleLocal029, triangleLocal007, triangleLocal091, triangleLocal083, triangleLocal102, triangleLocal101, triangleLocal127, triangleLocal131, triangleLocal057, triangleLocal118, triangleLocal061, triangleLocal064],
   ![singletonLocal017, singletonLocal076, singletonLocal076, singletonLocal012, singletonLocal017, singletonLocal052, singletonLocal062, singletonLocal052, singletonLocal092, singletonLocal086, singletonLocal058, singletonLocal086, singletonLocal025, singletonLocal009, singletonLocal102, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442055, node=0.
def cache075 : Cache :=
  ⟨![triangleLocal024, triangleLocal010, triangleLocal047, triangleLocal040, triangleLocal016, triangleLocal007, triangleLocal104, triangleLocal083, triangleLocal094, triangleLocal101, triangleLocal107, triangleLocal131, triangleLocal057, triangleLocal045, triangleLocal061, triangleLocal062],
   ![singletonLocal006, singletonLocal076, singletonLocal076, singletonLocal004, singletonLocal006, singletonLocal052, singletonLocal113, singletonLocal052, singletonLocal093, singletonLocal086, singletonLocal097, singletonLocal086, singletonLocal025, singletonLocal009, singletonLocal102, singletonLocal118]⟩

-- Actual context d=19, fullcode=21110514, node=0.
def cache076 : Cache :=
  ⟨![triangleLocal153, triangleLocal009, triangleLocal157, triangleLocal040, triangleLocal142, triangleLocal004, triangleLocal169, triangleLocal083, triangleLocal178, triangleLocal134, triangleLocal174, triangleLocal131, triangleLocal057, triangleLocal191, triangleLocal077, triangleLocal193],
   ![singletonLocal126, singletonLocal075, singletonLocal075, singletonLocal125, singletonLocal126, singletonLocal049, singletonLocal154, singletonLocal049, singletonLocal145, singletonLocal073, singletonLocal146, singletonLocal073, singletonLocal025, singletonLocal009, singletonLocal104, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110515, node=33.
def cache077 : Cache :=
  ⟨![triangleLocal152, triangleLocal008, triangleLocal157, triangleLocal040, triangleLocal146, triangleLocal002, triangleLocal169, triangleLocal083, triangleLocal172, triangleLocal124, triangleLocal174, triangleLocal131, triangleLocal057, triangleLocal191, triangleLocal071, triangleLocal190],
   ![singletonLocal126, singletonLocal077, singletonLocal077, singletonLocal125, singletonLocal126, singletonLocal044, singletonLocal154, singletonLocal044, singletonLocal145, singletonLocal031, singletonLocal146, singletonLocal031, singletonLocal025, singletonLocal009, singletonLocal023, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442060, node=0.
def cache078 : Cache :=
  ⟨![triangleLocal008, triangleLocal008, triangleLocal040, triangleLocal040, triangleLocal002, triangleLocal002, triangleLocal082, triangleLocal083, triangleLocal124, triangleLocal124, triangleLocal132, triangleLocal131, triangleLocal057, triangleLocal057, triangleLocal071, triangleLocal072],
   ![singletonLocal003, singletonLocal077, singletonLocal077, singletonLocal001, singletonLocal003, singletonLocal044, singletonLocal105, singletonLocal044, singletonLocal090, singletonLocal031, singletonLocal091, singletonLocal031, singletonLocal025, singletonLocal009, singletonLocal023, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442061, node=0.
def cache079 : Cache :=
  ⟨![triangleLocal035, triangleLocal008, triangleLocal046, triangleLocal040, triangleLocal030, triangleLocal002, triangleLocal099, triangleLocal083, triangleLocal120, triangleLocal124, triangleLocal129, triangleLocal131, triangleLocal057, triangleLocal122, triangleLocal071, triangleLocal068],
   ![singletonLocal015, singletonLocal077, singletonLocal077, singletonLocal011, singletonLocal015, singletonLocal044, singletonLocal119, singletonLocal044, singletonLocal056, singletonLocal031, singletonLocal096, singletonLocal031, singletonLocal025, singletonLocal009, singletonLocal023, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442062, node=0.
def cache080 : Cache :=
  ⟨![triangleLocal032, triangleLocal008, triangleLocal048, triangleLocal040, triangleLocal027, triangleLocal002, triangleLocal091, triangleLocal083, triangleLocal125, triangleLocal124, triangleLocal127, triangleLocal131, triangleLocal057, triangleLocal118, triangleLocal071, triangleLocal129],
   ![singletonLocal017, singletonLocal077, singletonLocal077, singletonLocal012, singletonLocal017, singletonLocal044, singletonLocal062, singletonLocal044, singletonLocal092, singletonLocal031, singletonLocal058, singletonLocal031, singletonLocal025, singletonLocal009, singletonLocal023, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442063, node=0.
def cache081 : Cache :=
  ⟨![triangleLocal022, triangleLocal008, triangleLocal047, triangleLocal040, triangleLocal012, triangleLocal002, triangleLocal104, triangleLocal083, triangleLocal093, triangleLocal124, triangleLocal107, triangleLocal131, triangleLocal057, triangleLocal045, triangleLocal071, triangleLocal053],
   ![singletonLocal006, singletonLocal077, singletonLocal077, singletonLocal004, singletonLocal006, singletonLocal044, singletonLocal113, singletonLocal044, singletonLocal093, singletonLocal031, singletonLocal097, singletonLocal031, singletonLocal025, singletonLocal009, singletonLocal023, singletonLocal118]⟩

-- Actual context d=18, fullcode=5277629, node=14311.
def cache082 : Cache :=
  ⟨![triangleLocal197, triangleLocal151, triangleLocal157, triangleLocal046, triangleLocal195, triangleLocal149, triangleLocal169, triangleLocal100, triangleLocal201, triangleLocal171, triangleLocal174, triangleLocal128, triangleLocal122, triangleLocal191, triangleLocal185, triangleLocal205],
   ![singletonLocal132, singletonLocal140, singletonLocal140, singletonLocal130, singletonLocal132, singletonLocal136, singletonLocal156, singletonLocal136, singletonLocal141, singletonLocal143, singletonLocal149, singletonLocal143, singletonLocal025, singletonLocal072, singletonLocal157, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110516, node=0.
def cache083 : Cache :=
  ⟨![triangleLocal145, triangleLocal019, triangleLocal157, triangleLocal046, triangleLocal139, triangleLocal006, triangleLocal169, triangleLocal100, triangleLocal177, triangleLocal121, triangleLocal174, triangleLocal128, triangleLocal122, triangleLocal191, triangleLocal066, triangleLocal186],
   ![singletonLocal132, singletonLocal069, singletonLocal069, singletonLocal130, singletonLocal132, singletonLocal019, singletonLocal156, singletonLocal019, singletonLocal141, singletonLocal059, singletonLocal149, singletonLocal059, singletonLocal025, singletonLocal072, singletonLocal000, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110517, node=113.
def cache084 : Cache :=
  ⟨![triangleLocal154, triangleLocal034, triangleLocal157, triangleLocal046, triangleLocal148, triangleLocal026, triangleLocal169, triangleLocal100, triangleLocal162, triangleLocal097, triangleLocal174, triangleLocal128, triangleLocal122, triangleLocal191, triangleLocal021, triangleLocal184],
   ![singletonLocal132, singletonLocal076, singletonLocal076, singletonLocal130, singletonLocal132, singletonLocal052, singletonLocal156, singletonLocal052, singletonLocal141, singletonLocal086, singletonLocal149, singletonLocal086, singletonLocal025, singletonLocal072, singletonLocal102, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442068, node=9.
def cache085 : Cache :=
  ⟨![triangleLocal010, triangleLocal034, triangleLocal040, triangleLocal046, triangleLocal007, triangleLocal026, triangleLocal082, triangleLocal100, triangleLocal101, triangleLocal097, triangleLocal132, triangleLocal128, triangleLocal122, triangleLocal057, triangleLocal021, triangleLocal060],
   ![singletonLocal016, singletonLocal076, singletonLocal076, singletonLocal013, singletonLocal016, singletonLocal052, singletonLocal120, singletonLocal052, singletonLocal055, singletonLocal086, singletonLocal098, singletonLocal086, singletonLocal025, singletonLocal072, singletonLocal102, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442069, node=0.
def cache086 : Cache :=
  ⟨![triangleLocal034, triangleLocal034, triangleLocal046, triangleLocal046, triangleLocal025, triangleLocal026, triangleLocal099, triangleLocal100, triangleLocal097, triangleLocal097, triangleLocal129, triangleLocal128, triangleLocal122, triangleLocal122, triangleLocal021, triangleLocal020],
   ![singletonLocal039, singletonLocal076, singletonLocal076, singletonLocal037, singletonLocal039, singletonLocal052, singletonLocal124, singletonLocal052, singletonLocal021, singletonLocal086, singletonLocal103, singletonLocal086, singletonLocal025, singletonLocal072, singletonLocal102, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442070, node=0.
def cache087 : Cache :=
  ⟨![triangleLocal033, triangleLocal034, triangleLocal048, triangleLocal046, triangleLocal029, triangleLocal026, triangleLocal091, triangleLocal100, triangleLocal102, triangleLocal097, triangleLocal127, triangleLocal128, triangleLocal122, triangleLocal118, triangleLocal021, triangleLocal064],
   ![singletonLocal045, singletonLocal076, singletonLocal076, singletonLocal042, singletonLocal045, singletonLocal052, singletonLocal089, singletonLocal052, singletonLocal078, singletonLocal086, singletonLocal084, singletonLocal086, singletonLocal025, singletonLocal072, singletonLocal102, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442071, node=0.
def cache088 : Cache :=
  ⟨![triangleLocal024, triangleLocal034, triangleLocal047, triangleLocal046, triangleLocal016, triangleLocal026, triangleLocal104, triangleLocal100, triangleLocal094, triangleLocal097, triangleLocal107, triangleLocal128, triangleLocal122, triangleLocal045, triangleLocal021, triangleLocal062],
   ![singletonLocal034, singletonLocal076, singletonLocal076, singletonLocal028, singletonLocal034, singletonLocal052, singletonLocal123, singletonLocal052, singletonLocal079, singletonLocal086, singletonLocal110, singletonLocal086, singletonLocal025, singletonLocal072, singletonLocal102, singletonLocal118]⟩

-- Actual context d=19, fullcode=21110518, node=0.
def cache089 : Cache :=
  ⟨![triangleLocal153, triangleLocal036, triangleLocal157, triangleLocal046, triangleLocal142, triangleLocal015, triangleLocal169, triangleLocal100, triangleLocal178, triangleLocal123, triangleLocal174, triangleLocal128, triangleLocal122, triangleLocal191, triangleLocal069, triangleLocal193],
   ![singletonLocal132, singletonLocal075, singletonLocal075, singletonLocal130, singletonLocal132, singletonLocal049, singletonLocal156, singletonLocal049, singletonLocal141, singletonLocal073, singletonLocal149, singletonLocal073, singletonLocal025, singletonLocal072, singletonLocal104, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110519, node=0.
def cache090 : Cache :=
  ⟨![triangleLocal152, triangleLocal035, triangleLocal157, triangleLocal046, triangleLocal146, triangleLocal030, triangleLocal169, triangleLocal100, triangleLocal172, triangleLocal120, triangleLocal174, triangleLocal128, triangleLocal122, triangleLocal191, triangleLocal067, triangleLocal190],
   ![singletonLocal132, singletonLocal077, singletonLocal077, singletonLocal130, singletonLocal132, singletonLocal044, singletonLocal156, singletonLocal044, singletonLocal141, singletonLocal031, singletonLocal149, singletonLocal031, singletonLocal025, singletonLocal072, singletonLocal023, singletonLocal159]⟩

-- Actual context d=18, fullcode=5277630, node=2836.
def cache091 : Cache :=
  ⟨![triangleLocal197, triangleLocal150, triangleLocal157, triangleLocal048, triangleLocal195, triangleLocal147, triangleLocal169, triangleLocal092, triangleLocal201, triangleLocal176, triangleLocal174, triangleLocal126, triangleLocal118, triangleLocal191, triangleLocal194, triangleLocal205],
   ![singletonLocal133, singletonLocal140, singletonLocal140, singletonLocal131, singletonLocal133, singletonLocal136, singletonLocal144, singletonLocal136, singletonLocal147, singletonLocal143, singletonLocal142, singletonLocal143, singletonLocal025, singletonLocal053, singletonLocal157, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110520, node=0.
def cache092 : Cache :=
  ⟨![triangleLocal145, triangleLocal017, triangleLocal157, triangleLocal048, triangleLocal139, triangleLocal001, triangleLocal169, triangleLocal092, triangleLocal177, triangleLocal135, triangleLocal174, triangleLocal126, triangleLocal118, triangleLocal191, triangleLocal074, triangleLocal186],
   ![singletonLocal133, singletonLocal069, singletonLocal069, singletonLocal131, singletonLocal133, singletonLocal019, singletonLocal144, singletonLocal019, singletonLocal147, singletonLocal059, singletonLocal142, singletonLocal059, singletonLocal025, singletonLocal053, singletonLocal000, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110521, node=22.
def cache093 : Cache :=
  ⟨![triangleLocal154, triangleLocal033, triangleLocal157, triangleLocal048, triangleLocal148, triangleLocal029, triangleLocal169, triangleLocal092, triangleLocal162, triangleLocal102, triangleLocal174, triangleLocal126, triangleLocal118, triangleLocal191, triangleLocal065, triangleLocal184],
   ![singletonLocal133, singletonLocal076, singletonLocal076, singletonLocal131, singletonLocal133, singletonLocal052, singletonLocal144, singletonLocal052, singletonLocal147, singletonLocal086, singletonLocal142, singletonLocal086, singletonLocal025, singletonLocal053, singletonLocal102, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442084, node=9.
def cache094 : Cache :=
  ⟨![triangleLocal010, triangleLocal033, triangleLocal040, triangleLocal048, triangleLocal007, triangleLocal029, triangleLocal082, triangleLocal092, triangleLocal101, triangleLocal102, triangleLocal132, triangleLocal126, triangleLocal118, triangleLocal057, triangleLocal065, triangleLocal060],
   ![singletonLocal018, singletonLocal076, singletonLocal076, singletonLocal014, singletonLocal018, singletonLocal052, singletonLocal061, singletonLocal052, singletonLocal094, singletonLocal086, singletonLocal057, singletonLocal086, singletonLocal025, singletonLocal053, singletonLocal102, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442085, node=9.
def cache095 : Cache :=
  ⟨![triangleLocal034, triangleLocal033, triangleLocal046, triangleLocal048, triangleLocal025, triangleLocal029, triangleLocal099, triangleLocal092, triangleLocal097, triangleLocal102, triangleLocal129, triangleLocal126, triangleLocal118, triangleLocal122, triangleLocal065, triangleLocal020],
   ![singletonLocal046, singletonLocal076, singletonLocal076, singletonLocal043, singletonLocal046, singletonLocal052, singletonLocal088, singletonLocal052, singletonLocal080, singletonLocal086, singletonLocal082, singletonLocal086, singletonLocal025, singletonLocal053, singletonLocal102, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442086, node=0.
def cache096 : Cache :=
  ⟨![triangleLocal033, triangleLocal033, triangleLocal048, triangleLocal048, triangleLocal029, triangleLocal029, triangleLocal091, triangleLocal092, triangleLocal102, triangleLocal102, triangleLocal127, triangleLocal126, triangleLocal118, triangleLocal118, triangleLocal065, triangleLocal064],
   ![singletonLocal041, singletonLocal076, singletonLocal076, singletonLocal038, singletonLocal041, singletonLocal052, singletonLocal040, singletonLocal052, singletonLocal100, singletonLocal086, singletonLocal022, singletonLocal086, singletonLocal025, singletonLocal053, singletonLocal102, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442087, node=0.
def cache097 : Cache :=
  ⟨![triangleLocal024, triangleLocal033, triangleLocal047, triangleLocal048, triangleLocal016, triangleLocal029, triangleLocal104, triangleLocal092, triangleLocal094, triangleLocal102, triangleLocal107, triangleLocal126, triangleLocal118, triangleLocal045, triangleLocal065, triangleLocal062],
   ![singletonLocal036, singletonLocal076, singletonLocal076, singletonLocal029, singletonLocal036, singletonLocal052, singletonLocal063, singletonLocal052, singletonLocal108, singletonLocal086, singletonLocal083, singletonLocal086, singletonLocal025, singletonLocal053, singletonLocal102, singletonLocal118]⟩

-- Actual context d=19, fullcode=21110522, node=22.
def cache098 : Cache :=
  ⟨![triangleLocal153, triangleLocal031, triangleLocal157, triangleLocal048, triangleLocal142, triangleLocal011, triangleLocal169, triangleLocal092, triangleLocal178, triangleLocal136, triangleLocal174, triangleLocal126, triangleLocal118, triangleLocal191, triangleLocal056, triangleLocal193],
   ![singletonLocal133, singletonLocal075, singletonLocal075, singletonLocal131, singletonLocal133, singletonLocal049, singletonLocal144, singletonLocal049, singletonLocal147, singletonLocal073, singletonLocal142, singletonLocal073, singletonLocal025, singletonLocal053, singletonLocal104, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442088, node=9.
def cache099 : Cache :=
  ⟨![triangleLocal009, triangleLocal031, triangleLocal040, triangleLocal048, triangleLocal004, triangleLocal011, triangleLocal082, triangleLocal092, triangleLocal134, triangleLocal136, triangleLocal132, triangleLocal126, triangleLocal118, triangleLocal057, triangleLocal056, triangleLocal078],
   ![singletonLocal018, singletonLocal075, singletonLocal075, singletonLocal014, singletonLocal018, singletonLocal049, singletonLocal061, singletonLocal049, singletonLocal094, singletonLocal073, singletonLocal057, singletonLocal073, singletonLocal025, singletonLocal053, singletonLocal104, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442089, node=9.
def cache100 : Cache :=
  ⟨![triangleLocal036, triangleLocal031, triangleLocal046, triangleLocal048, triangleLocal015, triangleLocal011, triangleLocal099, triangleLocal092, triangleLocal123, triangleLocal136, triangleLocal129, triangleLocal126, triangleLocal118, triangleLocal122, triangleLocal056, triangleLocal070],
   ![singletonLocal046, singletonLocal075, singletonLocal075, singletonLocal043, singletonLocal046, singletonLocal049, singletonLocal088, singletonLocal049, singletonLocal080, singletonLocal073, singletonLocal082, singletonLocal073, singletonLocal025, singletonLocal053, singletonLocal104, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442090, node=0.
def cache101 : Cache :=
  ⟨![triangleLocal031, triangleLocal031, triangleLocal048, triangleLocal048, triangleLocal011, triangleLocal011, triangleLocal091, triangleLocal092, triangleLocal136, triangleLocal136, triangleLocal127, triangleLocal126, triangleLocal118, triangleLocal118, triangleLocal056, triangleLocal055],
   ![singletonLocal041, singletonLocal075, singletonLocal075, singletonLocal038, singletonLocal041, singletonLocal049, singletonLocal040, singletonLocal049, singletonLocal100, singletonLocal073, singletonLocal022, singletonLocal073, singletonLocal025, singletonLocal053, singletonLocal104, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442091, node=0.
def cache102 : Cache :=
  ⟨![triangleLocal023, triangleLocal031, triangleLocal047, triangleLocal048, triangleLocal013, triangleLocal011, triangleLocal104, triangleLocal092, triangleLocal096, triangleLocal136, triangleLocal107, triangleLocal126, triangleLocal118, triangleLocal045, triangleLocal056, triangleLocal115],
   ![singletonLocal036, singletonLocal075, singletonLocal075, singletonLocal029, singletonLocal036, singletonLocal049, singletonLocal063, singletonLocal049, singletonLocal108, singletonLocal073, singletonLocal083, singletonLocal073, singletonLocal025, singletonLocal053, singletonLocal104, singletonLocal118]⟩

-- Actual context d=19, fullcode=21110523, node=22.
def cache103 : Cache :=
  ⟨![triangleLocal152, triangleLocal032, triangleLocal157, triangleLocal048, triangleLocal146, triangleLocal028, triangleLocal169, triangleLocal092, triangleLocal172, triangleLocal125, triangleLocal174, triangleLocal126, triangleLocal118, triangleLocal191, triangleLocal128, triangleLocal190],
   ![singletonLocal133, singletonLocal077, singletonLocal077, singletonLocal131, singletonLocal133, singletonLocal044, singletonLocal144, singletonLocal044, singletonLocal147, singletonLocal031, singletonLocal142, singletonLocal031, singletonLocal025, singletonLocal053, singletonLocal023, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442092, node=9.
def cache104 : Cache :=
  ⟨![triangleLocal008, triangleLocal032, triangleLocal040, triangleLocal048, triangleLocal002, triangleLocal028, triangleLocal082, triangleLocal092, triangleLocal124, triangleLocal125, triangleLocal132, triangleLocal126, triangleLocal118, triangleLocal057, triangleLocal128, triangleLocal072],
   ![singletonLocal018, singletonLocal077, singletonLocal077, singletonLocal014, singletonLocal018, singletonLocal044, singletonLocal061, singletonLocal044, singletonLocal094, singletonLocal031, singletonLocal057, singletonLocal031, singletonLocal025, singletonLocal053, singletonLocal023, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442093, node=9.
def cache105 : Cache :=
  ⟨![triangleLocal035, triangleLocal032, triangleLocal046, triangleLocal048, triangleLocal030, triangleLocal028, triangleLocal099, triangleLocal092, triangleLocal120, triangleLocal125, triangleLocal129, triangleLocal126, triangleLocal118, triangleLocal122, triangleLocal128, triangleLocal068],
   ![singletonLocal046, singletonLocal077, singletonLocal077, singletonLocal043, singletonLocal046, singletonLocal044, singletonLocal088, singletonLocal044, singletonLocal080, singletonLocal031, singletonLocal082, singletonLocal031, singletonLocal025, singletonLocal053, singletonLocal023, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442094, node=0.
def cache106 : Cache :=
  ⟨![triangleLocal032, triangleLocal032, triangleLocal048, triangleLocal048, triangleLocal027, triangleLocal028, triangleLocal091, triangleLocal092, triangleLocal125, triangleLocal125, triangleLocal127, triangleLocal126, triangleLocal118, triangleLocal118, triangleLocal128, triangleLocal129],
   ![singletonLocal041, singletonLocal077, singletonLocal077, singletonLocal038, singletonLocal041, singletonLocal044, singletonLocal040, singletonLocal044, singletonLocal100, singletonLocal031, singletonLocal022, singletonLocal031, singletonLocal025, singletonLocal053, singletonLocal023, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442095, node=0.
def cache107 : Cache :=
  ⟨![triangleLocal022, triangleLocal032, triangleLocal047, triangleLocal048, triangleLocal012, triangleLocal028, triangleLocal104, triangleLocal092, triangleLocal093, triangleLocal125, triangleLocal107, triangleLocal126, triangleLocal118, triangleLocal045, triangleLocal128, triangleLocal053],
   ![singletonLocal036, singletonLocal077, singletonLocal077, singletonLocal029, singletonLocal036, singletonLocal044, singletonLocal063, singletonLocal044, singletonLocal108, singletonLocal031, singletonLocal083, singletonLocal031, singletonLocal025, singletonLocal053, singletonLocal023, singletonLocal118]⟩

-- Actual context d=18, fullcode=5277631, node=14936.
def cache108 : Cache :=
  ⟨![triangleLocal197, triangleLocal144, triangleLocal157, triangleLocal047, triangleLocal195, triangleLocal143, triangleLocal169, triangleLocal105, triangleLocal201, triangleLocal161, triangleLocal174, triangleLocal109, triangleLocal045, triangleLocal191, triangleLocal189, triangleLocal205],
   ![singletonLocal129, singletonLocal140, singletonLocal140, singletonLocal128, singletonLocal129, singletonLocal136, singletonLocal155, singletonLocal136, singletonLocal148, singletonLocal143, singletonLocal150, singletonLocal143, singletonLocal025, singletonLocal118, singletonLocal157, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110524, node=0.
def cache109 : Cache :=
  ⟨![triangleLocal145, triangleLocal018, triangleLocal157, triangleLocal047, triangleLocal139, triangleLocal003, triangleLocal169, triangleLocal105, triangleLocal177, triangleLocal095, triangleLocal174, triangleLocal109, triangleLocal045, triangleLocal191, triangleLocal073, triangleLocal186],
   ![singletonLocal129, singletonLocal069, singletonLocal069, singletonLocal128, singletonLocal129, singletonLocal019, singletonLocal155, singletonLocal019, singletonLocal148, singletonLocal059, singletonLocal150, singletonLocal059, singletonLocal025, singletonLocal118, singletonLocal000, singletonLocal159]⟩

-- Actual context d=19, fullcode=21110525, node=162.
def cache110 : Cache :=
  ⟨![triangleLocal154, triangleLocal024, triangleLocal157, triangleLocal047, triangleLocal148, triangleLocal016, triangleLocal169, triangleLocal105, triangleLocal162, triangleLocal094, triangleLocal174, triangleLocal109, triangleLocal045, triangleLocal191, triangleLocal063, triangleLocal184],
   ![singletonLocal129, singletonLocal076, singletonLocal076, singletonLocal128, singletonLocal129, singletonLocal052, singletonLocal155, singletonLocal052, singletonLocal148, singletonLocal086, singletonLocal150, singletonLocal086, singletonLocal025, singletonLocal118, singletonLocal102, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442100, node=9.
def cache111 : Cache :=
  ⟨![triangleLocal010, triangleLocal024, triangleLocal040, triangleLocal047, triangleLocal007, triangleLocal016, triangleLocal082, triangleLocal105, triangleLocal101, triangleLocal094, triangleLocal132, triangleLocal109, triangleLocal045, triangleLocal057, triangleLocal063, triangleLocal060],
   ![singletonLocal007, singletonLocal076, singletonLocal076, singletonLocal005, singletonLocal007, singletonLocal052, singletonLocal114, singletonLocal052, singletonLocal095, singletonLocal086, singletonLocal099, singletonLocal086, singletonLocal025, singletonLocal118, singletonLocal102, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442101, node=9.
def cache112 : Cache :=
  ⟨![triangleLocal034, triangleLocal024, triangleLocal046, triangleLocal047, triangleLocal025, triangleLocal016, triangleLocal099, triangleLocal105, triangleLocal097, triangleLocal094, triangleLocal129, triangleLocal109, triangleLocal045, triangleLocal122, triangleLocal063, triangleLocal020],
   ![singletonLocal033, singletonLocal076, singletonLocal076, singletonLocal026, singletonLocal033, singletonLocal052, singletonLocal122, singletonLocal052, singletonLocal081, singletonLocal086, singletonLocal111, singletonLocal086, singletonLocal025, singletonLocal118, singletonLocal102, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442102, node=9.
def cache113 : Cache :=
  ⟨![triangleLocal033, triangleLocal024, triangleLocal048, triangleLocal047, triangleLocal029, triangleLocal016, triangleLocal091, triangleLocal105, triangleLocal102, triangleLocal094, triangleLocal127, triangleLocal109, triangleLocal045, triangleLocal118, triangleLocal063, triangleLocal064],
   ![singletonLocal035, singletonLocal076, singletonLocal076, singletonLocal027, singletonLocal035, singletonLocal052, singletonLocal064, singletonLocal052, singletonLocal109, singletonLocal086, singletonLocal085, singletonLocal086, singletonLocal025, singletonLocal118, singletonLocal102, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442103, node=0.
def cache114 : Cache :=
  ⟨![triangleLocal024, triangleLocal024, triangleLocal047, triangleLocal047, triangleLocal016, triangleLocal016, triangleLocal104, triangleLocal105, triangleLocal094, triangleLocal094, triangleLocal107, triangleLocal109, triangleLocal045, triangleLocal045, triangleLocal063, triangleLocal062],
   ![singletonLocal024, singletonLocal076, singletonLocal076, singletonLocal020, singletonLocal024, singletonLocal052, singletonLocal106, singletonLocal052, singletonLocal101, singletonLocal086, singletonLocal104, singletonLocal086, singletonLocal025, singletonLocal118, singletonLocal102, singletonLocal118]⟩

-- Actual context d=19, fullcode=21110526, node=162.
def cache115 : Cache :=
  ⟨![triangleLocal153, triangleLocal023, triangleLocal157, triangleLocal047, triangleLocal142, triangleLocal014, triangleLocal169, triangleLocal105, triangleLocal178, triangleLocal096, triangleLocal174, triangleLocal109, triangleLocal045, triangleLocal191, triangleLocal113, triangleLocal193],
   ![singletonLocal129, singletonLocal075, singletonLocal075, singletonLocal128, singletonLocal129, singletonLocal049, singletonLocal155, singletonLocal049, singletonLocal148, singletonLocal073, singletonLocal150, singletonLocal073, singletonLocal025, singletonLocal118, singletonLocal104, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442104, node=9.
def cache116 : Cache :=
  ⟨![triangleLocal009, triangleLocal023, triangleLocal040, triangleLocal047, triangleLocal004, triangleLocal014, triangleLocal082, triangleLocal105, triangleLocal134, triangleLocal096, triangleLocal132, triangleLocal109, triangleLocal045, triangleLocal057, triangleLocal113, triangleLocal078],
   ![singletonLocal007, singletonLocal075, singletonLocal075, singletonLocal005, singletonLocal007, singletonLocal049, singletonLocal114, singletonLocal049, singletonLocal095, singletonLocal073, singletonLocal099, singletonLocal073, singletonLocal025, singletonLocal118, singletonLocal104, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442105, node=9.
def cache117 : Cache :=
  ⟨![triangleLocal036, triangleLocal023, triangleLocal046, triangleLocal047, triangleLocal015, triangleLocal014, triangleLocal099, triangleLocal105, triangleLocal123, triangleLocal096, triangleLocal129, triangleLocal109, triangleLocal045, triangleLocal122, triangleLocal113, triangleLocal070],
   ![singletonLocal033, singletonLocal075, singletonLocal075, singletonLocal026, singletonLocal033, singletonLocal049, singletonLocal122, singletonLocal049, singletonLocal081, singletonLocal073, singletonLocal111, singletonLocal073, singletonLocal025, singletonLocal118, singletonLocal104, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442106, node=9.
def cache118 : Cache :=
  ⟨![triangleLocal031, triangleLocal023, triangleLocal048, triangleLocal047, triangleLocal011, triangleLocal014, triangleLocal091, triangleLocal105, triangleLocal136, triangleLocal096, triangleLocal127, triangleLocal109, triangleLocal045, triangleLocal118, triangleLocal113, triangleLocal055],
   ![singletonLocal035, singletonLocal075, singletonLocal075, singletonLocal027, singletonLocal035, singletonLocal049, singletonLocal064, singletonLocal049, singletonLocal109, singletonLocal073, singletonLocal085, singletonLocal073, singletonLocal025, singletonLocal118, singletonLocal104, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442107, node=0.
def cache119 : Cache :=
  ⟨![triangleLocal023, triangleLocal023, triangleLocal047, triangleLocal047, triangleLocal013, triangleLocal014, triangleLocal104, triangleLocal105, triangleLocal096, triangleLocal096, triangleLocal107, triangleLocal109, triangleLocal045, triangleLocal045, triangleLocal113, triangleLocal115],
   ![singletonLocal024, singletonLocal075, singletonLocal075, singletonLocal020, singletonLocal024, singletonLocal049, singletonLocal106, singletonLocal049, singletonLocal101, singletonLocal073, singletonLocal104, singletonLocal073, singletonLocal025, singletonLocal118, singletonLocal104, singletonLocal118]⟩

-- Actual context d=19, fullcode=21110527, node=162.
def cache120 : Cache :=
  ⟨![triangleLocal152, triangleLocal022, triangleLocal157, triangleLocal047, triangleLocal146, triangleLocal012, triangleLocal169, triangleLocal105, triangleLocal172, triangleLocal093, triangleLocal174, triangleLocal109, triangleLocal045, triangleLocal191, triangleLocal052, triangleLocal190],
   ![singletonLocal129, singletonLocal077, singletonLocal077, singletonLocal128, singletonLocal129, singletonLocal044, singletonLocal155, singletonLocal044, singletonLocal148, singletonLocal031, singletonLocal150, singletonLocal031, singletonLocal025, singletonLocal118, singletonLocal023, singletonLocal159]⟩

-- Actual context d=20, fullcode=84442108, node=9.
def cache121 : Cache :=
  ⟨![triangleLocal008, triangleLocal022, triangleLocal040, triangleLocal047, triangleLocal002, triangleLocal012, triangleLocal082, triangleLocal105, triangleLocal124, triangleLocal093, triangleLocal132, triangleLocal109, triangleLocal045, triangleLocal057, triangleLocal052, triangleLocal072],
   ![singletonLocal007, singletonLocal077, singletonLocal077, singletonLocal005, singletonLocal007, singletonLocal044, singletonLocal114, singletonLocal044, singletonLocal095, singletonLocal031, singletonLocal099, singletonLocal031, singletonLocal025, singletonLocal118, singletonLocal023, singletonLocal009]⟩

-- Actual context d=20, fullcode=84442109, node=9.
def cache122 : Cache :=
  ⟨![triangleLocal035, triangleLocal022, triangleLocal046, triangleLocal047, triangleLocal030, triangleLocal012, triangleLocal099, triangleLocal105, triangleLocal120, triangleLocal093, triangleLocal129, triangleLocal109, triangleLocal045, triangleLocal122, triangleLocal052, triangleLocal068],
   ![singletonLocal033, singletonLocal077, singletonLocal077, singletonLocal026, singletonLocal033, singletonLocal044, singletonLocal122, singletonLocal044, singletonLocal081, singletonLocal031, singletonLocal111, singletonLocal031, singletonLocal025, singletonLocal118, singletonLocal023, singletonLocal072]⟩

-- Actual context d=20, fullcode=84442110, node=9.
def cache123 : Cache :=
  ⟨![triangleLocal032, triangleLocal022, triangleLocal048, triangleLocal047, triangleLocal027, triangleLocal012, triangleLocal091, triangleLocal105, triangleLocal125, triangleLocal093, triangleLocal127, triangleLocal109, triangleLocal045, triangleLocal118, triangleLocal052, triangleLocal129],
   ![singletonLocal035, singletonLocal077, singletonLocal077, singletonLocal027, singletonLocal035, singletonLocal044, singletonLocal064, singletonLocal044, singletonLocal109, singletonLocal031, singletonLocal085, singletonLocal031, singletonLocal025, singletonLocal118, singletonLocal023, singletonLocal053]⟩

-- Actual context d=20, fullcode=84442111, node=0.
def cache124 : Cache :=
  ⟨![triangleLocal022, triangleLocal022, triangleLocal047, triangleLocal047, triangleLocal012, triangleLocal012, triangleLocal104, triangleLocal105, triangleLocal093, triangleLocal093, triangleLocal107, triangleLocal109, triangleLocal045, triangleLocal045, triangleLocal052, triangleLocal053],
   ![singletonLocal024, singletonLocal077, singletonLocal077, singletonLocal020, singletonLocal024, singletonLocal044, singletonLocal106, singletonLocal044, singletonLocal101, singletonLocal031, singletonLocal104, singletonLocal031, singletonLocal025, singletonLocal118, singletonLocal023, singletonLocal118]⟩

theorem step_000_0 :
    step cache000 (coordinate 16) ⟨0, by decide⟩ = cache001 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · rfl
    · exact triangle_update_192
    · exact triangle_update_192
    · rfl
    · rfl
    · exact triangle_update_196
    · exact triangle_update_200
    · rfl
    · rfl
    · exact triangle_update_216
    · exact triangle_update_212
    · exact triangle_update_220
    · exact triangle_update_220
    · rfl
    · rfl
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_140
    · exact singleton_update_140
    · rfl
    · rfl
    · exact singleton_update_136
    · rfl
    · exact singleton_update_136
    · rfl
    · exact singleton_update_152
    · rfl
    · exact singleton_update_152
    · exact singleton_update_120
    · rfl
    · rfl
    · rfl

theorem step_000_1 :
    step cache000 (coordinate 16) ⟨1, by decide⟩ = cache002 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · rfl
    · exact triangle_update_193
    · exact triangle_update_193
    · rfl
    · rfl
    · exact triangle_update_197
    · exact triangle_update_201
    · rfl
    · rfl
    · exact triangle_update_217
    · exact triangle_update_213
    · exact triangle_update_221
    · exact triangle_update_221
    · rfl
    · rfl
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_141
    · exact singleton_update_141
    · rfl
    · rfl
    · exact singleton_update_137
    · rfl
    · exact singleton_update_137
    · rfl
    · exact singleton_update_153
    · rfl
    · exact singleton_update_153
    · exact singleton_update_121
    · rfl
    · rfl
    · rfl

theorem step_002_0 :
    step cache002 (coordinate 17) ⟨0, by decide⟩ = cache003 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · exact triangle_update_188
    · rfl
    · exact triangle_update_056
    · rfl
    · exact triangle_update_180
    · rfl
    · exact triangle_update_092
    · rfl
    · exact triangle_update_208
    · rfl
    · exact triangle_update_132
    · exact triangle_update_164
    · rfl
    · exact triangle_update_228
    · rfl
  · intro k
    fin_cases k
    · exact singleton_update_132
    · rfl
    · rfl
    · exact singleton_update_128
    · exact singleton_update_132
    · rfl
    · exact singleton_update_156
    · rfl
    · exact singleton_update_144
    · rfl
    · exact singleton_update_148
    · rfl
    · rfl
    · exact singleton_update_124
    · rfl
    · rfl

theorem step_002_1 :
    step cache002 (coordinate 17) ⟨1, by decide⟩ = cache004 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · exact triangle_update_189
    · rfl
    · exact triangle_update_057
    · rfl
    · exact triangle_update_181
    · rfl
    · exact triangle_update_093
    · rfl
    · exact triangle_update_209
    · rfl
    · exact triangle_update_133
    · exact triangle_update_165
    · rfl
    · exact triangle_update_229
    · rfl
  · intro k
    fin_cases k
    · exact singleton_update_133
    · rfl
    · rfl
    · exact singleton_update_129
    · exact singleton_update_133
    · rfl
    · exact singleton_update_157
    · rfl
    · exact singleton_update_145
    · rfl
    · exact singleton_update_149
    · rfl
    · rfl
    · exact singleton_update_125
    · rfl
    · rfl

theorem step_002_2 :
    step cache002 (coordinate 17) ⟨2, by decide⟩ = cache005 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · exact triangle_update_190
    · rfl
    · exact triangle_update_058
    · rfl
    · exact triangle_update_182
    · rfl
    · exact triangle_update_094
    · rfl
    · exact triangle_update_210
    · rfl
    · exact triangle_update_134
    · exact triangle_update_166
    · rfl
    · exact triangle_update_230
    · rfl
  · intro k
    fin_cases k
    · exact singleton_update_134
    · rfl
    · rfl
    · exact singleton_update_130
    · exact singleton_update_134
    · rfl
    · exact singleton_update_158
    · rfl
    · exact singleton_update_146
    · rfl
    · exact singleton_update_150
    · rfl
    · rfl
    · exact singleton_update_126
    · rfl
    · rfl

theorem step_002_3 :
    step cache002 (coordinate 17) ⟨3, by decide⟩ = cache006 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · exact triangle_update_191
    · rfl
    · exact triangle_update_059
    · rfl
    · exact triangle_update_183
    · rfl
    · exact triangle_update_095
    · rfl
    · exact triangle_update_211
    · rfl
    · exact triangle_update_135
    · exact triangle_update_167
    · rfl
    · exact triangle_update_231
    · rfl
  · intro k
    fin_cases k
    · exact singleton_update_135
    · rfl
    · rfl
    · exact singleton_update_131
    · exact singleton_update_135
    · rfl
    · exact singleton_update_159
    · rfl
    · exact singleton_update_147
    · rfl
    · exact singleton_update_151
    · rfl
    · rfl
    · exact singleton_update_127
    · rfl
    · rfl

theorem step_006_0 :
    step cache006 (coordinate 18) ⟨0, by decide⟩ = cache007 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_184
    · exact triangle_update_016
    · rfl
    · rfl
    · exact triangle_update_176
    · exact triangle_update_012
    · rfl
    · rfl
    · exact triangle_update_204
    · exact triangle_update_076
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_152
    · exact triangle_update_224
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_048
    · exact singleton_update_048
    · rfl
    · rfl
    · exact singleton_update_032
    · rfl
    · exact singleton_update_032
    · rfl
    · exact singleton_update_100
    · rfl
    · exact singleton_update_100
    · rfl
    · rfl
    · exact singleton_update_116
    · rfl

theorem step_006_1 :
    step cache006 (coordinate 18) ⟨1, by decide⟩ = cache008 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_185
    · exact triangle_update_017
    · rfl
    · rfl
    · exact triangle_update_177
    · exact triangle_update_013
    · rfl
    · rfl
    · exact triangle_update_205
    · exact triangle_update_077
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_153
    · exact triangle_update_225
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_049
    · exact singleton_update_049
    · rfl
    · rfl
    · exact singleton_update_033
    · rfl
    · exact singleton_update_033
    · rfl
    · exact singleton_update_101
    · rfl
    · exact singleton_update_101
    · rfl
    · rfl
    · exact singleton_update_117
    · rfl

theorem step_006_2 :
    step cache006 (coordinate 18) ⟨2, by decide⟩ = cache009 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_186
    · exact triangle_update_018
    · rfl
    · rfl
    · exact triangle_update_178
    · exact triangle_update_014
    · rfl
    · rfl
    · exact triangle_update_206
    · exact triangle_update_078
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_154
    · exact triangle_update_226
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_050
    · exact singleton_update_050
    · rfl
    · rfl
    · exact singleton_update_034
    · rfl
    · exact singleton_update_034
    · rfl
    · exact singleton_update_102
    · rfl
    · exact singleton_update_102
    · rfl
    · rfl
    · exact singleton_update_118
    · rfl

theorem step_006_3 :
    step cache006 (coordinate 18) ⟨3, by decide⟩ = cache010 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_187
    · exact triangle_update_019
    · rfl
    · rfl
    · exact triangle_update_179
    · exact triangle_update_015
    · rfl
    · rfl
    · exact triangle_update_207
    · exact triangle_update_079
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_155
    · exact triangle_update_227
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_051
    · exact singleton_update_051
    · rfl
    · rfl
    · exact singleton_update_035
    · rfl
    · exact singleton_update_035
    · rfl
    · exact singleton_update_103
    · rfl
    · exact singleton_update_103
    · rfl
    · rfl
    · exact singleton_update_119
    · rfl

theorem step_000_2 :
    step cache000 (coordinate 16) ⟨2, by decide⟩ = cache011 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · rfl
    · exact triangle_update_194
    · exact triangle_update_194
    · rfl
    · rfl
    · exact triangle_update_198
    · exact triangle_update_202
    · rfl
    · rfl
    · exact triangle_update_218
    · exact triangle_update_214
    · exact triangle_update_222
    · exact triangle_update_222
    · rfl
    · rfl
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_142
    · exact singleton_update_142
    · rfl
    · rfl
    · exact singleton_update_138
    · rfl
    · exact singleton_update_138
    · rfl
    · exact singleton_update_154
    · rfl
    · exact singleton_update_154
    · exact singleton_update_122
    · rfl
    · rfl
    · rfl

theorem step_011_0 :
    step cache011 (coordinate 17) ⟨0, by decide⟩ = cache012 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · exact triangle_update_188
    · rfl
    · exact triangle_update_064
    · rfl
    · exact triangle_update_180
    · rfl
    · exact triangle_update_068
    · rfl
    · exact triangle_update_208
    · rfl
    · exact triangle_update_084
    · exact triangle_update_144
    · rfl
    · exact triangle_update_228
    · rfl
  · intro k
    fin_cases k
    · exact singleton_update_132
    · rfl
    · rfl
    · exact singleton_update_128
    · exact singleton_update_132
    · rfl
    · exact singleton_update_156
    · rfl
    · exact singleton_update_144
    · rfl
    · exact singleton_update_148
    · rfl
    · rfl
    · exact singleton_update_124
    · rfl
    · rfl

theorem step_012_0 :
    step cache012 (coordinate 18) ⟨0, by decide⟩ = cache013 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_184
    · exact triangle_update_004
    · rfl
    · rfl
    · exact triangle_update_176
    · exact triangle_update_000
    · rfl
    · rfl
    · exact triangle_update_204
    · exact triangle_update_120
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_148
    · exact triangle_update_224
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_044
    · exact singleton_update_044
    · rfl
    · rfl
    · exact singleton_update_036
    · rfl
    · exact singleton_update_036
    · rfl
    · exact singleton_update_096
    · rfl
    · exact singleton_update_096
    · rfl
    · rfl
    · exact singleton_update_116
    · rfl

theorem step_012_1 :
    step cache012 (coordinate 18) ⟨1, by decide⟩ = cache014 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_185
    · exact triangle_update_005
    · rfl
    · rfl
    · exact triangle_update_177
    · exact triangle_update_001
    · rfl
    · rfl
    · exact triangle_update_205
    · exact triangle_update_121
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_149
    · exact triangle_update_225
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_045
    · exact singleton_update_045
    · rfl
    · rfl
    · exact singleton_update_037
    · rfl
    · exact singleton_update_037
    · rfl
    · exact singleton_update_097
    · rfl
    · exact singleton_update_097
    · rfl
    · rfl
    · exact singleton_update_117
    · rfl

theorem step_014_0 :
    step cache014 (coordinate 19) ⟨0, by decide⟩ = cache015 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_052
    · rfl
    · exact triangle_update_064
    · rfl
    · exact triangle_update_028
    · rfl
    · exact triangle_update_072
    · rfl
    · exact triangle_update_080
    · rfl
    · exact triangle_update_088
    · rfl
    · rfl
    · exact triangle_update_144
    · rfl
    · exact triangle_update_136
  · intro k
    fin_cases k
    · exact singleton_update_004
    · rfl
    · rfl
    · exact singleton_update_000
    · exact singleton_update_004
    · rfl
    · exact singleton_update_104
    · rfl
    · exact singleton_update_072
    · rfl
    · exact singleton_update_076
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_014_1 :
    step cache014 (coordinate 19) ⟨1, by decide⟩ = cache016 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_053
    · rfl
    · exact triangle_update_065
    · rfl
    · exact triangle_update_029
    · rfl
    · exact triangle_update_073
    · rfl
    · exact triangle_update_081
    · rfl
    · exact triangle_update_089
    · rfl
    · rfl
    · exact triangle_update_145
    · rfl
    · exact triangle_update_137
  · intro k
    fin_cases k
    · exact singleton_update_005
    · rfl
    · rfl
    · exact singleton_update_001
    · exact singleton_update_005
    · rfl
    · exact singleton_update_105
    · rfl
    · exact singleton_update_073
    · rfl
    · exact singleton_update_077
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_014_2 :
    step cache014 (coordinate 19) ⟨2, by decide⟩ = cache017 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_054
    · rfl
    · exact triangle_update_066
    · rfl
    · exact triangle_update_030
    · rfl
    · exact triangle_update_074
    · rfl
    · exact triangle_update_082
    · rfl
    · exact triangle_update_090
    · rfl
    · rfl
    · exact triangle_update_146
    · rfl
    · exact triangle_update_138
  · intro k
    fin_cases k
    · exact singleton_update_006
    · rfl
    · rfl
    · exact singleton_update_002
    · exact singleton_update_006
    · rfl
    · exact singleton_update_106
    · rfl
    · exact singleton_update_074
    · rfl
    · exact singleton_update_078
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_014_3 :
    step cache014 (coordinate 19) ⟨3, by decide⟩ = cache018 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_055
    · rfl
    · exact triangle_update_067
    · rfl
    · exact triangle_update_031
    · rfl
    · exact triangle_update_075
    · rfl
    · exact triangle_update_083
    · rfl
    · exact triangle_update_091
    · rfl
    · rfl
    · exact triangle_update_147
    · rfl
    · exact triangle_update_139
  · intro k
    fin_cases k
    · exact singleton_update_007
    · rfl
    · rfl
    · exact singleton_update_003
    · exact singleton_update_007
    · rfl
    · exact singleton_update_107
    · rfl
    · exact singleton_update_075
    · rfl
    · exact singleton_update_079
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_012_2 :
    step cache012 (coordinate 18) ⟨2, by decide⟩ = cache019 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_186
    · exact triangle_update_006
    · rfl
    · rfl
    · exact triangle_update_178
    · exact triangle_update_002
    · rfl
    · rfl
    · exact triangle_update_206
    · exact triangle_update_122
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_150
    · exact triangle_update_226
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_046
    · exact singleton_update_046
    · rfl
    · rfl
    · exact singleton_update_038
    · rfl
    · exact singleton_update_038
    · rfl
    · exact singleton_update_098
    · rfl
    · exact singleton_update_098
    · rfl
    · rfl
    · exact singleton_update_118
    · rfl

theorem step_012_3 :
    step cache012 (coordinate 18) ⟨3, by decide⟩ = cache020 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_187
    · exact triangle_update_007
    · rfl
    · rfl
    · exact triangle_update_179
    · exact triangle_update_003
    · rfl
    · rfl
    · exact triangle_update_207
    · exact triangle_update_123
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_151
    · exact triangle_update_227
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_047
    · exact singleton_update_047
    · rfl
    · rfl
    · exact singleton_update_039
    · rfl
    · exact singleton_update_039
    · rfl
    · exact singleton_update_099
    · rfl
    · exact singleton_update_099
    · rfl
    · rfl
    · exact singleton_update_119
    · rfl

theorem step_020_0 :
    step cache020 (coordinate 19) ⟨0, by decide⟩ = cache021 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_044
    · rfl
    · exact triangle_update_064
    · rfl
    · exact triangle_update_020
    · rfl
    · exact triangle_update_072
    · rfl
    · exact triangle_update_108
    · rfl
    · exact triangle_update_088
    · rfl
    · rfl
    · exact triangle_update_144
    · rfl
    · exact triangle_update_156
  · intro k
    fin_cases k
    · exact singleton_update_004
    · rfl
    · rfl
    · exact singleton_update_000
    · exact singleton_update_004
    · rfl
    · exact singleton_update_104
    · rfl
    · exact singleton_update_072
    · rfl
    · exact singleton_update_076
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_020_1 :
    step cache020 (coordinate 19) ⟨1, by decide⟩ = cache022 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_045
    · rfl
    · exact triangle_update_065
    · rfl
    · exact triangle_update_021
    · rfl
    · exact triangle_update_073
    · rfl
    · exact triangle_update_109
    · rfl
    · exact triangle_update_089
    · rfl
    · rfl
    · exact triangle_update_145
    · rfl
    · exact triangle_update_157
  · intro k
    fin_cases k
    · exact singleton_update_005
    · rfl
    · rfl
    · exact singleton_update_001
    · exact singleton_update_005
    · rfl
    · exact singleton_update_105
    · rfl
    · exact singleton_update_073
    · rfl
    · exact singleton_update_077
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_020_2 :
    step cache020 (coordinate 19) ⟨2, by decide⟩ = cache023 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_046
    · rfl
    · exact triangle_update_066
    · rfl
    · exact triangle_update_022
    · rfl
    · exact triangle_update_074
    · rfl
    · exact triangle_update_110
    · rfl
    · exact triangle_update_090
    · rfl
    · rfl
    · exact triangle_update_146
    · rfl
    · exact triangle_update_158
  · intro k
    fin_cases k
    · exact singleton_update_006
    · rfl
    · rfl
    · exact singleton_update_002
    · exact singleton_update_006
    · rfl
    · exact singleton_update_106
    · rfl
    · exact singleton_update_074
    · rfl
    · exact singleton_update_078
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_020_3 :
    step cache020 (coordinate 19) ⟨3, by decide⟩ = cache024 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_047
    · rfl
    · exact triangle_update_067
    · rfl
    · exact triangle_update_023
    · rfl
    · exact triangle_update_075
    · rfl
    · exact triangle_update_111
    · rfl
    · exact triangle_update_091
    · rfl
    · rfl
    · exact triangle_update_147
    · rfl
    · exact triangle_update_159
  · intro k
    fin_cases k
    · exact singleton_update_007
    · rfl
    · rfl
    · exact singleton_update_003
    · exact singleton_update_007
    · rfl
    · exact singleton_update_107
    · rfl
    · exact singleton_update_075
    · rfl
    · exact singleton_update_079
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_011_1 :
    step cache011 (coordinate 17) ⟨1, by decide⟩ = cache025 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · exact triangle_update_189
    · rfl
    · exact triangle_update_065
    · rfl
    · exact triangle_update_181
    · rfl
    · exact triangle_update_069
    · rfl
    · exact triangle_update_209
    · rfl
    · exact triangle_update_085
    · exact triangle_update_145
    · rfl
    · exact triangle_update_229
    · rfl
  · intro k
    fin_cases k
    · exact singleton_update_133
    · rfl
    · rfl
    · exact singleton_update_129
    · exact singleton_update_133
    · rfl
    · exact singleton_update_157
    · rfl
    · exact singleton_update_145
    · rfl
    · exact singleton_update_149
    · rfl
    · rfl
    · exact singleton_update_125
    · rfl
    · rfl

theorem step_025_0 :
    step cache025 (coordinate 18) ⟨0, by decide⟩ = cache026 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_184
    · exact triangle_update_040
    · rfl
    · rfl
    · exact triangle_update_176
    · exact triangle_update_032
    · rfl
    · rfl
    · exact triangle_update_204
    · exact triangle_update_104
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_140
    · exact triangle_update_224
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_044
    · exact singleton_update_044
    · rfl
    · rfl
    · exact singleton_update_036
    · rfl
    · exact singleton_update_036
    · rfl
    · exact singleton_update_096
    · rfl
    · exact singleton_update_096
    · rfl
    · rfl
    · exact singleton_update_116
    · rfl

theorem step_025_1 :
    step cache025 (coordinate 18) ⟨1, by decide⟩ = cache027 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_185
    · exact triangle_update_041
    · rfl
    · rfl
    · exact triangle_update_177
    · exact triangle_update_033
    · rfl
    · rfl
    · exact triangle_update_205
    · exact triangle_update_105
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_141
    · exact triangle_update_225
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_045
    · exact singleton_update_045
    · rfl
    · rfl
    · exact singleton_update_037
    · rfl
    · exact singleton_update_037
    · rfl
    · exact singleton_update_097
    · rfl
    · exact singleton_update_097
    · rfl
    · rfl
    · exact singleton_update_117
    · rfl

theorem step_027_0 :
    step cache027 (coordinate 19) ⟨0, by decide⟩ = cache028 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_052
    · rfl
    · exact triangle_update_064
    · rfl
    · exact triangle_update_028
    · rfl
    · exact triangle_update_072
    · rfl
    · exact triangle_update_080
    · rfl
    · exact triangle_update_088
    · rfl
    · rfl
    · exact triangle_update_144
    · rfl
    · exact triangle_update_136
  · intro k
    fin_cases k
    · exact singleton_update_024
    · rfl
    · rfl
    · exact singleton_update_016
    · exact singleton_update_024
    · rfl
    · exact singleton_update_112
    · rfl
    · exact singleton_update_056
    · rfl
    · exact singleton_update_088
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_027_1 :
    step cache027 (coordinate 19) ⟨1, by decide⟩ = cache029 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_053
    · rfl
    · exact triangle_update_065
    · rfl
    · exact triangle_update_029
    · rfl
    · exact triangle_update_073
    · rfl
    · exact triangle_update_081
    · rfl
    · exact triangle_update_089
    · rfl
    · rfl
    · exact triangle_update_145
    · rfl
    · exact triangle_update_137
  · intro k
    fin_cases k
    · exact singleton_update_025
    · rfl
    · rfl
    · exact singleton_update_017
    · exact singleton_update_025
    · rfl
    · exact singleton_update_113
    · rfl
    · exact singleton_update_057
    · rfl
    · exact singleton_update_089
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_027_2 :
    step cache027 (coordinate 19) ⟨2, by decide⟩ = cache030 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_054
    · rfl
    · exact triangle_update_066
    · rfl
    · exact triangle_update_030
    · rfl
    · exact triangle_update_074
    · rfl
    · exact triangle_update_082
    · rfl
    · exact triangle_update_090
    · rfl
    · rfl
    · exact triangle_update_146
    · rfl
    · exact triangle_update_138
  · intro k
    fin_cases k
    · exact singleton_update_026
    · rfl
    · rfl
    · exact singleton_update_018
    · exact singleton_update_026
    · rfl
    · exact singleton_update_114
    · rfl
    · exact singleton_update_058
    · rfl
    · exact singleton_update_090
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_027_3 :
    step cache027 (coordinate 19) ⟨3, by decide⟩ = cache031 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_055
    · rfl
    · exact triangle_update_067
    · rfl
    · exact triangle_update_031
    · rfl
    · exact triangle_update_075
    · rfl
    · exact triangle_update_083
    · rfl
    · exact triangle_update_091
    · rfl
    · rfl
    · exact triangle_update_147
    · rfl
    · exact triangle_update_139
  · intro k
    fin_cases k
    · exact singleton_update_027
    · rfl
    · rfl
    · exact singleton_update_019
    · exact singleton_update_027
    · rfl
    · exact singleton_update_115
    · rfl
    · exact singleton_update_059
    · rfl
    · exact singleton_update_091
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_025_2 :
    step cache025 (coordinate 18) ⟨2, by decide⟩ = cache032 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_186
    · exact triangle_update_042
    · rfl
    · rfl
    · exact triangle_update_178
    · exact triangle_update_034
    · rfl
    · rfl
    · exact triangle_update_206
    · exact triangle_update_106
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_142
    · exact triangle_update_226
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_046
    · exact singleton_update_046
    · rfl
    · rfl
    · exact singleton_update_038
    · rfl
    · exact singleton_update_038
    · rfl
    · exact singleton_update_098
    · rfl
    · exact singleton_update_098
    · rfl
    · rfl
    · exact singleton_update_118
    · rfl

theorem step_025_3 :
    step cache025 (coordinate 18) ⟨3, by decide⟩ = cache033 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_187
    · exact triangle_update_043
    · rfl
    · rfl
    · exact triangle_update_179
    · exact triangle_update_035
    · rfl
    · rfl
    · exact triangle_update_207
    · exact triangle_update_107
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_143
    · exact triangle_update_227
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_047
    · exact singleton_update_047
    · rfl
    · rfl
    · exact singleton_update_039
    · rfl
    · exact singleton_update_039
    · rfl
    · exact singleton_update_099
    · rfl
    · exact singleton_update_099
    · rfl
    · rfl
    · exact singleton_update_119
    · rfl

theorem step_033_0 :
    step cache033 (coordinate 19) ⟨0, by decide⟩ = cache034 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_044
    · rfl
    · exact triangle_update_064
    · rfl
    · exact triangle_update_020
    · rfl
    · exact triangle_update_072
    · rfl
    · exact triangle_update_108
    · rfl
    · exact triangle_update_088
    · rfl
    · rfl
    · exact triangle_update_144
    · rfl
    · exact triangle_update_156
  · intro k
    fin_cases k
    · exact singleton_update_024
    · rfl
    · rfl
    · exact singleton_update_016
    · exact singleton_update_024
    · rfl
    · exact singleton_update_112
    · rfl
    · exact singleton_update_056
    · rfl
    · exact singleton_update_088
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_033_1 :
    step cache033 (coordinate 19) ⟨1, by decide⟩ = cache035 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_045
    · rfl
    · exact triangle_update_065
    · rfl
    · exact triangle_update_021
    · rfl
    · exact triangle_update_073
    · rfl
    · exact triangle_update_109
    · rfl
    · exact triangle_update_089
    · rfl
    · rfl
    · exact triangle_update_145
    · rfl
    · exact triangle_update_157
  · intro k
    fin_cases k
    · exact singleton_update_025
    · rfl
    · rfl
    · exact singleton_update_017
    · exact singleton_update_025
    · rfl
    · exact singleton_update_113
    · rfl
    · exact singleton_update_057
    · rfl
    · exact singleton_update_089
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_033_2 :
    step cache033 (coordinate 19) ⟨2, by decide⟩ = cache036 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_046
    · rfl
    · exact triangle_update_066
    · rfl
    · exact triangle_update_022
    · rfl
    · exact triangle_update_074
    · rfl
    · exact triangle_update_110
    · rfl
    · exact triangle_update_090
    · rfl
    · rfl
    · exact triangle_update_146
    · rfl
    · exact triangle_update_158
  · intro k
    fin_cases k
    · exact singleton_update_026
    · rfl
    · rfl
    · exact singleton_update_018
    · exact singleton_update_026
    · rfl
    · exact singleton_update_114
    · rfl
    · exact singleton_update_058
    · rfl
    · exact singleton_update_090
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_033_3 :
    step cache033 (coordinate 19) ⟨3, by decide⟩ = cache037 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_047
    · rfl
    · exact triangle_update_067
    · rfl
    · exact triangle_update_023
    · rfl
    · exact triangle_update_075
    · rfl
    · exact triangle_update_111
    · rfl
    · exact triangle_update_091
    · rfl
    · rfl
    · exact triangle_update_147
    · rfl
    · exact triangle_update_159
  · intro k
    fin_cases k
    · exact singleton_update_027
    · rfl
    · rfl
    · exact singleton_update_019
    · exact singleton_update_027
    · rfl
    · exact singleton_update_115
    · rfl
    · exact singleton_update_059
    · rfl
    · exact singleton_update_091
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_011_2 :
    step cache011 (coordinate 17) ⟨2, by decide⟩ = cache038 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · exact triangle_update_190
    · rfl
    · exact triangle_update_066
    · rfl
    · exact triangle_update_182
    · rfl
    · exact triangle_update_070
    · rfl
    · exact triangle_update_210
    · rfl
    · exact triangle_update_086
    · exact triangle_update_146
    · rfl
    · exact triangle_update_230
    · rfl
  · intro k
    fin_cases k
    · exact singleton_update_134
    · rfl
    · rfl
    · exact singleton_update_130
    · exact singleton_update_134
    · rfl
    · exact singleton_update_158
    · rfl
    · exact singleton_update_146
    · rfl
    · exact singleton_update_150
    · rfl
    · rfl
    · exact singleton_update_126
    · rfl
    · rfl

theorem step_038_0 :
    step cache038 (coordinate 18) ⟨0, by decide⟩ = cache039 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_184
    · exact triangle_update_036
    · rfl
    · rfl
    · exact triangle_update_176
    · exact triangle_update_024
    · rfl
    · rfl
    · exact triangle_update_204
    · exact triangle_update_124
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_172
    · exact triangle_update_224
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_044
    · exact singleton_update_044
    · rfl
    · rfl
    · exact singleton_update_036
    · rfl
    · exact singleton_update_036
    · rfl
    · exact singleton_update_096
    · rfl
    · exact singleton_update_096
    · rfl
    · rfl
    · exact singleton_update_116
    · rfl

theorem step_038_1 :
    step cache038 (coordinate 18) ⟨1, by decide⟩ = cache040 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_185
    · exact triangle_update_037
    · rfl
    · rfl
    · exact triangle_update_177
    · exact triangle_update_025
    · rfl
    · rfl
    · exact triangle_update_205
    · exact triangle_update_125
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_173
    · exact triangle_update_225
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_045
    · exact singleton_update_045
    · rfl
    · rfl
    · exact singleton_update_037
    · rfl
    · exact singleton_update_037
    · rfl
    · exact singleton_update_097
    · rfl
    · exact singleton_update_097
    · rfl
    · rfl
    · exact singleton_update_117
    · rfl

theorem step_040_0 :
    step cache040 (coordinate 19) ⟨0, by decide⟩ = cache041 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_052
    · rfl
    · exact triangle_update_064
    · rfl
    · exact triangle_update_028
    · rfl
    · exact triangle_update_072
    · rfl
    · exact triangle_update_080
    · rfl
    · exact triangle_update_088
    · rfl
    · rfl
    · exact triangle_update_144
    · rfl
    · exact triangle_update_136
  · intro k
    fin_cases k
    · exact singleton_update_028
    · rfl
    · rfl
    · exact singleton_update_020
    · exact singleton_update_028
    · rfl
    · exact singleton_update_068
    · rfl
    · exact singleton_update_080
    · rfl
    · exact singleton_update_060
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_040_1 :
    step cache040 (coordinate 19) ⟨1, by decide⟩ = cache042 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_053
    · rfl
    · exact triangle_update_065
    · rfl
    · exact triangle_update_029
    · rfl
    · exact triangle_update_073
    · rfl
    · exact triangle_update_081
    · rfl
    · exact triangle_update_089
    · rfl
    · rfl
    · exact triangle_update_145
    · rfl
    · exact triangle_update_137
  · intro k
    fin_cases k
    · exact singleton_update_029
    · rfl
    · rfl
    · exact singleton_update_021
    · exact singleton_update_029
    · rfl
    · exact singleton_update_069
    · rfl
    · exact singleton_update_081
    · rfl
    · exact singleton_update_061
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_040_2 :
    step cache040 (coordinate 19) ⟨2, by decide⟩ = cache043 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_054
    · rfl
    · exact triangle_update_066
    · rfl
    · exact triangle_update_030
    · rfl
    · exact triangle_update_074
    · rfl
    · exact triangle_update_082
    · rfl
    · exact triangle_update_090
    · rfl
    · rfl
    · exact triangle_update_146
    · rfl
    · exact triangle_update_138
  · intro k
    fin_cases k
    · exact singleton_update_030
    · rfl
    · rfl
    · exact singleton_update_022
    · exact singleton_update_030
    · rfl
    · exact singleton_update_070
    · rfl
    · exact singleton_update_082
    · rfl
    · exact singleton_update_062
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_040_3 :
    step cache040 (coordinate 19) ⟨3, by decide⟩ = cache044 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_055
    · rfl
    · exact triangle_update_067
    · rfl
    · exact triangle_update_031
    · rfl
    · exact triangle_update_075
    · rfl
    · exact triangle_update_083
    · rfl
    · exact triangle_update_091
    · rfl
    · rfl
    · exact triangle_update_147
    · rfl
    · exact triangle_update_139
  · intro k
    fin_cases k
    · exact singleton_update_031
    · rfl
    · rfl
    · exact singleton_update_023
    · exact singleton_update_031
    · rfl
    · exact singleton_update_071
    · rfl
    · exact singleton_update_083
    · rfl
    · exact singleton_update_063
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_038_2 :
    step cache038 (coordinate 18) ⟨2, by decide⟩ = cache045 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_186
    · exact triangle_update_038
    · rfl
    · rfl
    · exact triangle_update_178
    · exact triangle_update_026
    · rfl
    · rfl
    · exact triangle_update_206
    · exact triangle_update_126
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_174
    · exact triangle_update_226
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_046
    · exact singleton_update_046
    · rfl
    · rfl
    · exact singleton_update_038
    · rfl
    · exact singleton_update_038
    · rfl
    · exact singleton_update_098
    · rfl
    · exact singleton_update_098
    · rfl
    · rfl
    · exact singleton_update_118
    · rfl

theorem step_038_3 :
    step cache038 (coordinate 18) ⟨3, by decide⟩ = cache046 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_187
    · exact triangle_update_039
    · rfl
    · rfl
    · exact triangle_update_179
    · exact triangle_update_027
    · rfl
    · rfl
    · exact triangle_update_207
    · exact triangle_update_127
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_175
    · exact triangle_update_227
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_047
    · exact singleton_update_047
    · rfl
    · rfl
    · exact singleton_update_039
    · rfl
    · exact singleton_update_039
    · rfl
    · exact singleton_update_099
    · rfl
    · exact singleton_update_099
    · rfl
    · rfl
    · exact singleton_update_119
    · rfl

theorem step_046_0 :
    step cache046 (coordinate 19) ⟨0, by decide⟩ = cache047 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_044
    · rfl
    · exact triangle_update_064
    · rfl
    · exact triangle_update_020
    · rfl
    · exact triangle_update_072
    · rfl
    · exact triangle_update_108
    · rfl
    · exact triangle_update_088
    · rfl
    · rfl
    · exact triangle_update_144
    · rfl
    · exact triangle_update_156
  · intro k
    fin_cases k
    · exact singleton_update_028
    · rfl
    · rfl
    · exact singleton_update_020
    · exact singleton_update_028
    · rfl
    · exact singleton_update_068
    · rfl
    · exact singleton_update_080
    · rfl
    · exact singleton_update_060
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_046_1 :
    step cache046 (coordinate 19) ⟨1, by decide⟩ = cache048 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_045
    · rfl
    · exact triangle_update_065
    · rfl
    · exact triangle_update_021
    · rfl
    · exact triangle_update_073
    · rfl
    · exact triangle_update_109
    · rfl
    · exact triangle_update_089
    · rfl
    · rfl
    · exact triangle_update_145
    · rfl
    · exact triangle_update_157
  · intro k
    fin_cases k
    · exact singleton_update_029
    · rfl
    · rfl
    · exact singleton_update_021
    · exact singleton_update_029
    · rfl
    · exact singleton_update_069
    · rfl
    · exact singleton_update_081
    · rfl
    · exact singleton_update_061
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_046_2 :
    step cache046 (coordinate 19) ⟨2, by decide⟩ = cache049 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_046
    · rfl
    · exact triangle_update_066
    · rfl
    · exact triangle_update_022
    · rfl
    · exact triangle_update_074
    · rfl
    · exact triangle_update_110
    · rfl
    · exact triangle_update_090
    · rfl
    · rfl
    · exact triangle_update_146
    · rfl
    · exact triangle_update_158
  · intro k
    fin_cases k
    · exact singleton_update_030
    · rfl
    · rfl
    · exact singleton_update_022
    · exact singleton_update_030
    · rfl
    · exact singleton_update_070
    · rfl
    · exact singleton_update_082
    · rfl
    · exact singleton_update_062
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_046_3 :
    step cache046 (coordinate 19) ⟨3, by decide⟩ = cache050 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_047
    · rfl
    · exact triangle_update_067
    · rfl
    · exact triangle_update_023
    · rfl
    · exact triangle_update_075
    · rfl
    · exact triangle_update_111
    · rfl
    · exact triangle_update_091
    · rfl
    · rfl
    · exact triangle_update_147
    · rfl
    · exact triangle_update_159
  · intro k
    fin_cases k
    · exact singleton_update_031
    · rfl
    · rfl
    · exact singleton_update_023
    · exact singleton_update_031
    · rfl
    · exact singleton_update_071
    · rfl
    · exact singleton_update_083
    · rfl
    · exact singleton_update_063
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_011_3 :
    step cache011 (coordinate 17) ⟨3, by decide⟩ = cache051 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · exact triangle_update_191
    · rfl
    · exact triangle_update_067
    · rfl
    · exact triangle_update_183
    · rfl
    · exact triangle_update_071
    · rfl
    · exact triangle_update_211
    · rfl
    · exact triangle_update_087
    · exact triangle_update_147
    · rfl
    · exact triangle_update_231
    · rfl
  · intro k
    fin_cases k
    · exact singleton_update_135
    · rfl
    · rfl
    · exact singleton_update_131
    · exact singleton_update_135
    · rfl
    · exact singleton_update_159
    · rfl
    · exact singleton_update_147
    · rfl
    · exact singleton_update_151
    · rfl
    · rfl
    · exact singleton_update_127
    · rfl
    · rfl

theorem step_051_0 :
    step cache051 (coordinate 18) ⟨0, by decide⟩ = cache052 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_184
    · exact triangle_update_016
    · rfl
    · rfl
    · exact triangle_update_176
    · exact triangle_update_012
    · rfl
    · rfl
    · exact triangle_update_204
    · exact triangle_update_076
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_152
    · exact triangle_update_224
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_044
    · exact singleton_update_044
    · rfl
    · rfl
    · exact singleton_update_036
    · rfl
    · exact singleton_update_036
    · rfl
    · exact singleton_update_096
    · rfl
    · exact singleton_update_096
    · rfl
    · rfl
    · exact singleton_update_116
    · rfl

theorem step_051_1 :
    step cache051 (coordinate 18) ⟨1, by decide⟩ = cache053 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_185
    · exact triangle_update_017
    · rfl
    · rfl
    · exact triangle_update_177
    · exact triangle_update_013
    · rfl
    · rfl
    · exact triangle_update_205
    · exact triangle_update_077
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_153
    · exact triangle_update_225
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_045
    · exact singleton_update_045
    · rfl
    · rfl
    · exact singleton_update_037
    · rfl
    · exact singleton_update_037
    · rfl
    · exact singleton_update_097
    · rfl
    · exact singleton_update_097
    · rfl
    · rfl
    · exact singleton_update_117
    · rfl

theorem step_053_0 :
    step cache053 (coordinate 19) ⟨0, by decide⟩ = cache054 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_052
    · rfl
    · exact triangle_update_064
    · rfl
    · exact triangle_update_028
    · rfl
    · exact triangle_update_072
    · rfl
    · exact triangle_update_080
    · rfl
    · exact triangle_update_088
    · rfl
    · rfl
    · exact triangle_update_144
    · rfl
    · exact triangle_update_136
  · intro k
    fin_cases k
    · exact singleton_update_012
    · rfl
    · rfl
    · exact singleton_update_008
    · exact singleton_update_012
    · rfl
    · exact singleton_update_108
    · rfl
    · exact singleton_update_084
    · rfl
    · exact singleton_update_092
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_053_1 :
    step cache053 (coordinate 19) ⟨1, by decide⟩ = cache055 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_053
    · rfl
    · exact triangle_update_065
    · rfl
    · exact triangle_update_029
    · rfl
    · exact triangle_update_073
    · rfl
    · exact triangle_update_081
    · rfl
    · exact triangle_update_089
    · rfl
    · rfl
    · exact triangle_update_145
    · rfl
    · exact triangle_update_137
  · intro k
    fin_cases k
    · exact singleton_update_013
    · rfl
    · rfl
    · exact singleton_update_009
    · exact singleton_update_013
    · rfl
    · exact singleton_update_109
    · rfl
    · exact singleton_update_085
    · rfl
    · exact singleton_update_093
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_053_2 :
    step cache053 (coordinate 19) ⟨2, by decide⟩ = cache056 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_054
    · rfl
    · exact triangle_update_066
    · rfl
    · exact triangle_update_030
    · rfl
    · exact triangle_update_074
    · rfl
    · exact triangle_update_082
    · rfl
    · exact triangle_update_090
    · rfl
    · rfl
    · exact triangle_update_146
    · rfl
    · exact triangle_update_138
  · intro k
    fin_cases k
    · exact singleton_update_014
    · rfl
    · rfl
    · exact singleton_update_010
    · exact singleton_update_014
    · rfl
    · exact singleton_update_110
    · rfl
    · exact singleton_update_086
    · rfl
    · exact singleton_update_094
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_053_3 :
    step cache053 (coordinate 19) ⟨3, by decide⟩ = cache057 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_055
    · rfl
    · exact triangle_update_067
    · rfl
    · exact triangle_update_031
    · rfl
    · exact triangle_update_075
    · rfl
    · exact triangle_update_083
    · rfl
    · exact triangle_update_091
    · rfl
    · rfl
    · exact triangle_update_147
    · rfl
    · exact triangle_update_139
  · intro k
    fin_cases k
    · exact singleton_update_015
    · rfl
    · rfl
    · exact singleton_update_011
    · exact singleton_update_015
    · rfl
    · exact singleton_update_111
    · rfl
    · exact singleton_update_087
    · rfl
    · exact singleton_update_095
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_051_2 :
    step cache051 (coordinate 18) ⟨2, by decide⟩ = cache058 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_186
    · exact triangle_update_018
    · rfl
    · rfl
    · exact triangle_update_178
    · exact triangle_update_014
    · rfl
    · rfl
    · exact triangle_update_206
    · exact triangle_update_078
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_154
    · exact triangle_update_226
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_046
    · exact singleton_update_046
    · rfl
    · rfl
    · exact singleton_update_038
    · rfl
    · exact singleton_update_038
    · rfl
    · exact singleton_update_098
    · rfl
    · exact singleton_update_098
    · rfl
    · rfl
    · exact singleton_update_118
    · rfl

theorem step_058_0 :
    step cache058 (coordinate 19) ⟨0, by decide⟩ = cache059 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_048
    · rfl
    · exact triangle_update_064
    · rfl
    · exact triangle_update_008
    · rfl
    · exact triangle_update_072
    · rfl
    · exact triangle_update_128
    · rfl
    · exact triangle_update_088
    · rfl
    · rfl
    · exact triangle_update_144
    · rfl
    · exact triangle_update_168
  · intro k
    fin_cases k
    · exact singleton_update_012
    · rfl
    · rfl
    · exact singleton_update_008
    · exact singleton_update_012
    · rfl
    · exact singleton_update_108
    · rfl
    · exact singleton_update_084
    · rfl
    · exact singleton_update_092
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_058_1 :
    step cache058 (coordinate 19) ⟨1, by decide⟩ = cache060 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_049
    · rfl
    · exact triangle_update_065
    · rfl
    · exact triangle_update_009
    · rfl
    · exact triangle_update_073
    · rfl
    · exact triangle_update_129
    · rfl
    · exact triangle_update_089
    · rfl
    · rfl
    · exact triangle_update_145
    · rfl
    · exact triangle_update_169
  · intro k
    fin_cases k
    · exact singleton_update_013
    · rfl
    · rfl
    · exact singleton_update_009
    · exact singleton_update_013
    · rfl
    · exact singleton_update_109
    · rfl
    · exact singleton_update_085
    · rfl
    · exact singleton_update_093
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_058_2 :
    step cache058 (coordinate 19) ⟨2, by decide⟩ = cache061 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_050
    · rfl
    · exact triangle_update_066
    · rfl
    · exact triangle_update_010
    · rfl
    · exact triangle_update_074
    · rfl
    · exact triangle_update_130
    · rfl
    · exact triangle_update_090
    · rfl
    · rfl
    · exact triangle_update_146
    · rfl
    · exact triangle_update_170
  · intro k
    fin_cases k
    · exact singleton_update_014
    · rfl
    · rfl
    · exact singleton_update_010
    · exact singleton_update_014
    · rfl
    · exact singleton_update_110
    · rfl
    · exact singleton_update_086
    · rfl
    · exact singleton_update_094
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_058_3 :
    step cache058 (coordinate 19) ⟨3, by decide⟩ = cache062 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_051
    · rfl
    · exact triangle_update_067
    · rfl
    · exact triangle_update_011
    · rfl
    · exact triangle_update_075
    · rfl
    · exact triangle_update_131
    · rfl
    · exact triangle_update_091
    · rfl
    · rfl
    · exact triangle_update_147
    · rfl
    · exact triangle_update_171
  · intro k
    fin_cases k
    · exact singleton_update_015
    · rfl
    · rfl
    · exact singleton_update_011
    · exact singleton_update_015
    · rfl
    · exact singleton_update_111
    · rfl
    · exact singleton_update_087
    · rfl
    · exact singleton_update_095
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_051_3 :
    step cache051 (coordinate 18) ⟨3, by decide⟩ = cache063 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_187
    · exact triangle_update_019
    · rfl
    · rfl
    · exact triangle_update_179
    · exact triangle_update_015
    · rfl
    · rfl
    · exact triangle_update_207
    · exact triangle_update_079
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_155
    · exact triangle_update_227
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_047
    · exact singleton_update_047
    · rfl
    · rfl
    · exact singleton_update_039
    · rfl
    · exact singleton_update_039
    · rfl
    · exact singleton_update_099
    · rfl
    · exact singleton_update_099
    · rfl
    · rfl
    · exact singleton_update_119
    · rfl

theorem step_063_0 :
    step cache063 (coordinate 19) ⟨0, by decide⟩ = cache064 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_044
    · rfl
    · exact triangle_update_064
    · rfl
    · exact triangle_update_020
    · rfl
    · exact triangle_update_072
    · rfl
    · exact triangle_update_108
    · rfl
    · exact triangle_update_088
    · rfl
    · rfl
    · exact triangle_update_144
    · rfl
    · exact triangle_update_156
  · intro k
    fin_cases k
    · exact singleton_update_012
    · rfl
    · rfl
    · exact singleton_update_008
    · exact singleton_update_012
    · rfl
    · exact singleton_update_108
    · rfl
    · exact singleton_update_084
    · rfl
    · exact singleton_update_092
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_063_1 :
    step cache063 (coordinate 19) ⟨1, by decide⟩ = cache065 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_045
    · rfl
    · exact triangle_update_065
    · rfl
    · exact triangle_update_021
    · rfl
    · exact triangle_update_073
    · rfl
    · exact triangle_update_109
    · rfl
    · exact triangle_update_089
    · rfl
    · rfl
    · exact triangle_update_145
    · rfl
    · exact triangle_update_157
  · intro k
    fin_cases k
    · exact singleton_update_013
    · rfl
    · rfl
    · exact singleton_update_009
    · exact singleton_update_013
    · rfl
    · exact singleton_update_109
    · rfl
    · exact singleton_update_085
    · rfl
    · exact singleton_update_093
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_063_2 :
    step cache063 (coordinate 19) ⟨2, by decide⟩ = cache066 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_046
    · rfl
    · exact triangle_update_066
    · rfl
    · exact triangle_update_022
    · rfl
    · exact triangle_update_074
    · rfl
    · exact triangle_update_110
    · rfl
    · exact triangle_update_090
    · rfl
    · rfl
    · exact triangle_update_146
    · rfl
    · exact triangle_update_158
  · intro k
    fin_cases k
    · exact singleton_update_014
    · rfl
    · rfl
    · exact singleton_update_010
    · exact singleton_update_014
    · rfl
    · exact singleton_update_110
    · rfl
    · exact singleton_update_086
    · rfl
    · exact singleton_update_094
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_063_3 :
    step cache063 (coordinate 19) ⟨3, by decide⟩ = cache067 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_047
    · rfl
    · exact triangle_update_067
    · rfl
    · exact triangle_update_023
    · rfl
    · exact triangle_update_075
    · rfl
    · exact triangle_update_111
    · rfl
    · exact triangle_update_091
    · rfl
    · rfl
    · exact triangle_update_147
    · rfl
    · exact triangle_update_159
  · intro k
    fin_cases k
    · exact singleton_update_015
    · rfl
    · rfl
    · exact singleton_update_011
    · exact singleton_update_015
    · rfl
    · exact singleton_update_111
    · rfl
    · exact singleton_update_087
    · rfl
    · exact singleton_update_095
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_000_3 :
    step cache000 (coordinate 16) ⟨3, by decide⟩ = cache068 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · rfl
    · exact triangle_update_195
    · exact triangle_update_195
    · rfl
    · rfl
    · exact triangle_update_199
    · exact triangle_update_203
    · rfl
    · rfl
    · exact triangle_update_219
    · exact triangle_update_215
    · exact triangle_update_223
    · exact triangle_update_223
    · rfl
    · rfl
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_143
    · exact singleton_update_143
    · rfl
    · rfl
    · exact singleton_update_139
    · rfl
    · exact singleton_update_139
    · rfl
    · exact singleton_update_155
    · rfl
    · exact singleton_update_155
    · exact singleton_update_123
    · rfl
    · rfl
    · rfl

theorem step_068_0 :
    step cache068 (coordinate 17) ⟨0, by decide⟩ = cache069 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · exact triangle_update_188
    · rfl
    · exact triangle_update_060
    · rfl
    · exact triangle_update_180
    · rfl
    · exact triangle_update_100
    · rfl
    · exact triangle_update_208
    · rfl
    · exact triangle_update_112
    · exact triangle_update_160
    · rfl
    · exact triangle_update_228
    · rfl
  · intro k
    fin_cases k
    · exact singleton_update_132
    · rfl
    · rfl
    · exact singleton_update_128
    · exact singleton_update_132
    · rfl
    · exact singleton_update_156
    · rfl
    · exact singleton_update_144
    · rfl
    · exact singleton_update_148
    · rfl
    · rfl
    · exact singleton_update_124
    · rfl
    · rfl

theorem step_069_0 :
    step cache069 (coordinate 18) ⟨0, by decide⟩ = cache070 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_184
    · exact triangle_update_004
    · rfl
    · rfl
    · exact triangle_update_176
    · exact triangle_update_000
    · rfl
    · rfl
    · exact triangle_update_204
    · exact triangle_update_120
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_148
    · exact triangle_update_224
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_052
    · exact singleton_update_052
    · rfl
    · rfl
    · exact singleton_update_040
    · rfl
    · exact singleton_update_040
    · rfl
    · exact singleton_update_064
    · rfl
    · exact singleton_update_064
    · rfl
    · rfl
    · exact singleton_update_116
    · rfl

theorem step_069_1 :
    step cache069 (coordinate 18) ⟨1, by decide⟩ = cache071 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_185
    · exact triangle_update_005
    · rfl
    · rfl
    · exact triangle_update_177
    · exact triangle_update_001
    · rfl
    · rfl
    · exact triangle_update_205
    · exact triangle_update_121
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_149
    · exact triangle_update_225
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_053
    · exact singleton_update_053
    · rfl
    · rfl
    · exact singleton_update_041
    · rfl
    · exact singleton_update_041
    · rfl
    · exact singleton_update_065
    · rfl
    · exact singleton_update_065
    · rfl
    · rfl
    · exact singleton_update_117
    · rfl

theorem step_071_0 :
    step cache071 (coordinate 19) ⟨0, by decide⟩ = cache072 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_052
    · rfl
    · exact triangle_update_060
    · rfl
    · exact triangle_update_028
    · rfl
    · exact triangle_update_096
    · rfl
    · exact triangle_update_080
    · rfl
    · exact triangle_update_116
    · rfl
    · rfl
    · exact triangle_update_160
    · rfl
    · exact triangle_update_136
  · intro k
    fin_cases k
    · exact singleton_update_004
    · rfl
    · rfl
    · exact singleton_update_000
    · exact singleton_update_004
    · rfl
    · exact singleton_update_104
    · rfl
    · exact singleton_update_072
    · rfl
    · exact singleton_update_076
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_071_1 :
    step cache071 (coordinate 19) ⟨1, by decide⟩ = cache073 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_053
    · rfl
    · exact triangle_update_061
    · rfl
    · exact triangle_update_029
    · rfl
    · exact triangle_update_097
    · rfl
    · exact triangle_update_081
    · rfl
    · exact triangle_update_117
    · rfl
    · rfl
    · exact triangle_update_161
    · rfl
    · exact triangle_update_137
  · intro k
    fin_cases k
    · exact singleton_update_005
    · rfl
    · rfl
    · exact singleton_update_001
    · exact singleton_update_005
    · rfl
    · exact singleton_update_105
    · rfl
    · exact singleton_update_073
    · rfl
    · exact singleton_update_077
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_071_2 :
    step cache071 (coordinate 19) ⟨2, by decide⟩ = cache074 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_054
    · rfl
    · exact triangle_update_062
    · rfl
    · exact triangle_update_030
    · rfl
    · exact triangle_update_098
    · rfl
    · exact triangle_update_082
    · rfl
    · exact triangle_update_118
    · rfl
    · rfl
    · exact triangle_update_162
    · rfl
    · exact triangle_update_138
  · intro k
    fin_cases k
    · exact singleton_update_006
    · rfl
    · rfl
    · exact singleton_update_002
    · exact singleton_update_006
    · rfl
    · exact singleton_update_106
    · rfl
    · exact singleton_update_074
    · rfl
    · exact singleton_update_078
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_071_3 :
    step cache071 (coordinate 19) ⟨3, by decide⟩ = cache075 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_055
    · rfl
    · exact triangle_update_063
    · rfl
    · exact triangle_update_031
    · rfl
    · exact triangle_update_099
    · rfl
    · exact triangle_update_083
    · rfl
    · exact triangle_update_119
    · rfl
    · rfl
    · exact triangle_update_163
    · rfl
    · exact triangle_update_139
  · intro k
    fin_cases k
    · exact singleton_update_007
    · rfl
    · rfl
    · exact singleton_update_003
    · exact singleton_update_007
    · rfl
    · exact singleton_update_107
    · rfl
    · exact singleton_update_075
    · rfl
    · exact singleton_update_079
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_069_2 :
    step cache069 (coordinate 18) ⟨2, by decide⟩ = cache076 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_186
    · exact triangle_update_006
    · rfl
    · rfl
    · exact triangle_update_178
    · exact triangle_update_002
    · rfl
    · rfl
    · exact triangle_update_206
    · exact triangle_update_122
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_150
    · exact triangle_update_226
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_054
    · exact singleton_update_054
    · rfl
    · rfl
    · exact singleton_update_042
    · rfl
    · exact singleton_update_042
    · rfl
    · exact singleton_update_066
    · rfl
    · exact singleton_update_066
    · rfl
    · rfl
    · exact singleton_update_118
    · rfl

theorem step_069_3 :
    step cache069 (coordinate 18) ⟨3, by decide⟩ = cache077 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_187
    · exact triangle_update_007
    · rfl
    · rfl
    · exact triangle_update_179
    · exact triangle_update_003
    · rfl
    · rfl
    · exact triangle_update_207
    · exact triangle_update_123
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_151
    · exact triangle_update_227
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_055
    · exact singleton_update_055
    · rfl
    · rfl
    · exact singleton_update_043
    · rfl
    · exact singleton_update_043
    · rfl
    · exact singleton_update_067
    · rfl
    · exact singleton_update_067
    · rfl
    · rfl
    · exact singleton_update_119
    · rfl

theorem step_077_0 :
    step cache077 (coordinate 19) ⟨0, by decide⟩ = cache078 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_044
    · rfl
    · exact triangle_update_060
    · rfl
    · exact triangle_update_020
    · rfl
    · exact triangle_update_096
    · rfl
    · exact triangle_update_108
    · rfl
    · exact triangle_update_116
    · rfl
    · rfl
    · exact triangle_update_160
    · rfl
    · exact triangle_update_156
  · intro k
    fin_cases k
    · exact singleton_update_004
    · rfl
    · rfl
    · exact singleton_update_000
    · exact singleton_update_004
    · rfl
    · exact singleton_update_104
    · rfl
    · exact singleton_update_072
    · rfl
    · exact singleton_update_076
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_077_1 :
    step cache077 (coordinate 19) ⟨1, by decide⟩ = cache079 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_045
    · rfl
    · exact triangle_update_061
    · rfl
    · exact triangle_update_021
    · rfl
    · exact triangle_update_097
    · rfl
    · exact triangle_update_109
    · rfl
    · exact triangle_update_117
    · rfl
    · rfl
    · exact triangle_update_161
    · rfl
    · exact triangle_update_157
  · intro k
    fin_cases k
    · exact singleton_update_005
    · rfl
    · rfl
    · exact singleton_update_001
    · exact singleton_update_005
    · rfl
    · exact singleton_update_105
    · rfl
    · exact singleton_update_073
    · rfl
    · exact singleton_update_077
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_077_2 :
    step cache077 (coordinate 19) ⟨2, by decide⟩ = cache080 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_046
    · rfl
    · exact triangle_update_062
    · rfl
    · exact triangle_update_022
    · rfl
    · exact triangle_update_098
    · rfl
    · exact triangle_update_110
    · rfl
    · exact triangle_update_118
    · rfl
    · rfl
    · exact triangle_update_162
    · rfl
    · exact triangle_update_158
  · intro k
    fin_cases k
    · exact singleton_update_006
    · rfl
    · rfl
    · exact singleton_update_002
    · exact singleton_update_006
    · rfl
    · exact singleton_update_106
    · rfl
    · exact singleton_update_074
    · rfl
    · exact singleton_update_078
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_077_3 :
    step cache077 (coordinate 19) ⟨3, by decide⟩ = cache081 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_047
    · rfl
    · exact triangle_update_063
    · rfl
    · exact triangle_update_023
    · rfl
    · exact triangle_update_099
    · rfl
    · exact triangle_update_111
    · rfl
    · exact triangle_update_119
    · rfl
    · rfl
    · exact triangle_update_163
    · rfl
    · exact triangle_update_159
  · intro k
    fin_cases k
    · exact singleton_update_007
    · rfl
    · rfl
    · exact singleton_update_003
    · exact singleton_update_007
    · rfl
    · exact singleton_update_107
    · rfl
    · exact singleton_update_075
    · rfl
    · exact singleton_update_079
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_068_1 :
    step cache068 (coordinate 17) ⟨1, by decide⟩ = cache082 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · exact triangle_update_189
    · rfl
    · exact triangle_update_061
    · rfl
    · exact triangle_update_181
    · rfl
    · exact triangle_update_101
    · rfl
    · exact triangle_update_209
    · rfl
    · exact triangle_update_113
    · exact triangle_update_161
    · rfl
    · exact triangle_update_229
    · rfl
  · intro k
    fin_cases k
    · exact singleton_update_133
    · rfl
    · rfl
    · exact singleton_update_129
    · exact singleton_update_133
    · rfl
    · exact singleton_update_157
    · rfl
    · exact singleton_update_145
    · rfl
    · exact singleton_update_149
    · rfl
    · rfl
    · exact singleton_update_125
    · rfl
    · rfl

theorem step_082_0 :
    step cache082 (coordinate 18) ⟨0, by decide⟩ = cache083 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_184
    · exact triangle_update_040
    · rfl
    · rfl
    · exact triangle_update_176
    · exact triangle_update_032
    · rfl
    · rfl
    · exact triangle_update_204
    · exact triangle_update_104
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_140
    · exact triangle_update_224
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_052
    · exact singleton_update_052
    · rfl
    · rfl
    · exact singleton_update_040
    · rfl
    · exact singleton_update_040
    · rfl
    · exact singleton_update_064
    · rfl
    · exact singleton_update_064
    · rfl
    · rfl
    · exact singleton_update_116
    · rfl

theorem step_082_1 :
    step cache082 (coordinate 18) ⟨1, by decide⟩ = cache084 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_185
    · exact triangle_update_041
    · rfl
    · rfl
    · exact triangle_update_177
    · exact triangle_update_033
    · rfl
    · rfl
    · exact triangle_update_205
    · exact triangle_update_105
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_141
    · exact triangle_update_225
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_053
    · exact singleton_update_053
    · rfl
    · rfl
    · exact singleton_update_041
    · rfl
    · exact singleton_update_041
    · rfl
    · exact singleton_update_065
    · rfl
    · exact singleton_update_065
    · rfl
    · rfl
    · exact singleton_update_117
    · rfl

theorem step_084_0 :
    step cache084 (coordinate 19) ⟨0, by decide⟩ = cache085 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_052
    · rfl
    · exact triangle_update_060
    · rfl
    · exact triangle_update_028
    · rfl
    · exact triangle_update_096
    · rfl
    · exact triangle_update_080
    · rfl
    · exact triangle_update_116
    · rfl
    · rfl
    · exact triangle_update_160
    · rfl
    · exact triangle_update_136
  · intro k
    fin_cases k
    · exact singleton_update_024
    · rfl
    · rfl
    · exact singleton_update_016
    · exact singleton_update_024
    · rfl
    · exact singleton_update_112
    · rfl
    · exact singleton_update_056
    · rfl
    · exact singleton_update_088
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_084_1 :
    step cache084 (coordinate 19) ⟨1, by decide⟩ = cache086 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_053
    · rfl
    · exact triangle_update_061
    · rfl
    · exact triangle_update_029
    · rfl
    · exact triangle_update_097
    · rfl
    · exact triangle_update_081
    · rfl
    · exact triangle_update_117
    · rfl
    · rfl
    · exact triangle_update_161
    · rfl
    · exact triangle_update_137
  · intro k
    fin_cases k
    · exact singleton_update_025
    · rfl
    · rfl
    · exact singleton_update_017
    · exact singleton_update_025
    · rfl
    · exact singleton_update_113
    · rfl
    · exact singleton_update_057
    · rfl
    · exact singleton_update_089
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_084_2 :
    step cache084 (coordinate 19) ⟨2, by decide⟩ = cache087 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_054
    · rfl
    · exact triangle_update_062
    · rfl
    · exact triangle_update_030
    · rfl
    · exact triangle_update_098
    · rfl
    · exact triangle_update_082
    · rfl
    · exact triangle_update_118
    · rfl
    · rfl
    · exact triangle_update_162
    · rfl
    · exact triangle_update_138
  · intro k
    fin_cases k
    · exact singleton_update_026
    · rfl
    · rfl
    · exact singleton_update_018
    · exact singleton_update_026
    · rfl
    · exact singleton_update_114
    · rfl
    · exact singleton_update_058
    · rfl
    · exact singleton_update_090
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_084_3 :
    step cache084 (coordinate 19) ⟨3, by decide⟩ = cache088 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_055
    · rfl
    · exact triangle_update_063
    · rfl
    · exact triangle_update_031
    · rfl
    · exact triangle_update_099
    · rfl
    · exact triangle_update_083
    · rfl
    · exact triangle_update_119
    · rfl
    · rfl
    · exact triangle_update_163
    · rfl
    · exact triangle_update_139
  · intro k
    fin_cases k
    · exact singleton_update_027
    · rfl
    · rfl
    · exact singleton_update_019
    · exact singleton_update_027
    · rfl
    · exact singleton_update_115
    · rfl
    · exact singleton_update_059
    · rfl
    · exact singleton_update_091
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_082_2 :
    step cache082 (coordinate 18) ⟨2, by decide⟩ = cache089 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_186
    · exact triangle_update_042
    · rfl
    · rfl
    · exact triangle_update_178
    · exact triangle_update_034
    · rfl
    · rfl
    · exact triangle_update_206
    · exact triangle_update_106
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_142
    · exact triangle_update_226
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_054
    · exact singleton_update_054
    · rfl
    · rfl
    · exact singleton_update_042
    · rfl
    · exact singleton_update_042
    · rfl
    · exact singleton_update_066
    · rfl
    · exact singleton_update_066
    · rfl
    · rfl
    · exact singleton_update_118
    · rfl

theorem step_082_3 :
    step cache082 (coordinate 18) ⟨3, by decide⟩ = cache090 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_187
    · exact triangle_update_043
    · rfl
    · rfl
    · exact triangle_update_179
    · exact triangle_update_035
    · rfl
    · rfl
    · exact triangle_update_207
    · exact triangle_update_107
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_143
    · exact triangle_update_227
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_055
    · exact singleton_update_055
    · rfl
    · rfl
    · exact singleton_update_043
    · rfl
    · exact singleton_update_043
    · rfl
    · exact singleton_update_067
    · rfl
    · exact singleton_update_067
    · rfl
    · rfl
    · exact singleton_update_119
    · rfl

theorem step_068_2 :
    step cache068 (coordinate 17) ⟨2, by decide⟩ = cache091 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · exact triangle_update_190
    · rfl
    · exact triangle_update_062
    · rfl
    · exact triangle_update_182
    · rfl
    · exact triangle_update_102
    · rfl
    · exact triangle_update_210
    · rfl
    · exact triangle_update_114
    · exact triangle_update_162
    · rfl
    · exact triangle_update_230
    · rfl
  · intro k
    fin_cases k
    · exact singleton_update_134
    · rfl
    · rfl
    · exact singleton_update_130
    · exact singleton_update_134
    · rfl
    · exact singleton_update_158
    · rfl
    · exact singleton_update_146
    · rfl
    · exact singleton_update_150
    · rfl
    · rfl
    · exact singleton_update_126
    · rfl
    · rfl

theorem step_091_0 :
    step cache091 (coordinate 18) ⟨0, by decide⟩ = cache092 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_184
    · exact triangle_update_036
    · rfl
    · rfl
    · exact triangle_update_176
    · exact triangle_update_024
    · rfl
    · rfl
    · exact triangle_update_204
    · exact triangle_update_124
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_172
    · exact triangle_update_224
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_052
    · exact singleton_update_052
    · rfl
    · rfl
    · exact singleton_update_040
    · rfl
    · exact singleton_update_040
    · rfl
    · exact singleton_update_064
    · rfl
    · exact singleton_update_064
    · rfl
    · rfl
    · exact singleton_update_116
    · rfl

theorem step_091_1 :
    step cache091 (coordinate 18) ⟨1, by decide⟩ = cache093 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_185
    · exact triangle_update_037
    · rfl
    · rfl
    · exact triangle_update_177
    · exact triangle_update_025
    · rfl
    · rfl
    · exact triangle_update_205
    · exact triangle_update_125
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_173
    · exact triangle_update_225
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_053
    · exact singleton_update_053
    · rfl
    · rfl
    · exact singleton_update_041
    · rfl
    · exact singleton_update_041
    · rfl
    · exact singleton_update_065
    · rfl
    · exact singleton_update_065
    · rfl
    · rfl
    · exact singleton_update_117
    · rfl

theorem step_093_0 :
    step cache093 (coordinate 19) ⟨0, by decide⟩ = cache094 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_052
    · rfl
    · exact triangle_update_060
    · rfl
    · exact triangle_update_028
    · rfl
    · exact triangle_update_096
    · rfl
    · exact triangle_update_080
    · rfl
    · exact triangle_update_116
    · rfl
    · rfl
    · exact triangle_update_160
    · rfl
    · exact triangle_update_136
  · intro k
    fin_cases k
    · exact singleton_update_028
    · rfl
    · rfl
    · exact singleton_update_020
    · exact singleton_update_028
    · rfl
    · exact singleton_update_068
    · rfl
    · exact singleton_update_080
    · rfl
    · exact singleton_update_060
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_093_1 :
    step cache093 (coordinate 19) ⟨1, by decide⟩ = cache095 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_053
    · rfl
    · exact triangle_update_061
    · rfl
    · exact triangle_update_029
    · rfl
    · exact triangle_update_097
    · rfl
    · exact triangle_update_081
    · rfl
    · exact triangle_update_117
    · rfl
    · rfl
    · exact triangle_update_161
    · rfl
    · exact triangle_update_137
  · intro k
    fin_cases k
    · exact singleton_update_029
    · rfl
    · rfl
    · exact singleton_update_021
    · exact singleton_update_029
    · rfl
    · exact singleton_update_069
    · rfl
    · exact singleton_update_081
    · rfl
    · exact singleton_update_061
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_093_2 :
    step cache093 (coordinate 19) ⟨2, by decide⟩ = cache096 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_054
    · rfl
    · exact triangle_update_062
    · rfl
    · exact triangle_update_030
    · rfl
    · exact triangle_update_098
    · rfl
    · exact triangle_update_082
    · rfl
    · exact triangle_update_118
    · rfl
    · rfl
    · exact triangle_update_162
    · rfl
    · exact triangle_update_138
  · intro k
    fin_cases k
    · exact singleton_update_030
    · rfl
    · rfl
    · exact singleton_update_022
    · exact singleton_update_030
    · rfl
    · exact singleton_update_070
    · rfl
    · exact singleton_update_082
    · rfl
    · exact singleton_update_062
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_093_3 :
    step cache093 (coordinate 19) ⟨3, by decide⟩ = cache097 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_055
    · rfl
    · exact triangle_update_063
    · rfl
    · exact triangle_update_031
    · rfl
    · exact triangle_update_099
    · rfl
    · exact triangle_update_083
    · rfl
    · exact triangle_update_119
    · rfl
    · rfl
    · exact triangle_update_163
    · rfl
    · exact triangle_update_139
  · intro k
    fin_cases k
    · exact singleton_update_031
    · rfl
    · rfl
    · exact singleton_update_023
    · exact singleton_update_031
    · rfl
    · exact singleton_update_071
    · rfl
    · exact singleton_update_083
    · rfl
    · exact singleton_update_063
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_091_2 :
    step cache091 (coordinate 18) ⟨2, by decide⟩ = cache098 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_186
    · exact triangle_update_038
    · rfl
    · rfl
    · exact triangle_update_178
    · exact triangle_update_026
    · rfl
    · rfl
    · exact triangle_update_206
    · exact triangle_update_126
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_174
    · exact triangle_update_226
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_054
    · exact singleton_update_054
    · rfl
    · rfl
    · exact singleton_update_042
    · rfl
    · exact singleton_update_042
    · rfl
    · exact singleton_update_066
    · rfl
    · exact singleton_update_066
    · rfl
    · rfl
    · exact singleton_update_118
    · rfl

theorem step_098_0 :
    step cache098 (coordinate 19) ⟨0, by decide⟩ = cache099 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_048
    · rfl
    · exact triangle_update_060
    · rfl
    · exact triangle_update_008
    · rfl
    · exact triangle_update_096
    · rfl
    · exact triangle_update_128
    · rfl
    · exact triangle_update_116
    · rfl
    · rfl
    · exact triangle_update_160
    · rfl
    · exact triangle_update_168
  · intro k
    fin_cases k
    · exact singleton_update_028
    · rfl
    · rfl
    · exact singleton_update_020
    · exact singleton_update_028
    · rfl
    · exact singleton_update_068
    · rfl
    · exact singleton_update_080
    · rfl
    · exact singleton_update_060
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_098_1 :
    step cache098 (coordinate 19) ⟨1, by decide⟩ = cache100 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_049
    · rfl
    · exact triangle_update_061
    · rfl
    · exact triangle_update_009
    · rfl
    · exact triangle_update_097
    · rfl
    · exact triangle_update_129
    · rfl
    · exact triangle_update_117
    · rfl
    · rfl
    · exact triangle_update_161
    · rfl
    · exact triangle_update_169
  · intro k
    fin_cases k
    · exact singleton_update_029
    · rfl
    · rfl
    · exact singleton_update_021
    · exact singleton_update_029
    · rfl
    · exact singleton_update_069
    · rfl
    · exact singleton_update_081
    · rfl
    · exact singleton_update_061
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_098_2 :
    step cache098 (coordinate 19) ⟨2, by decide⟩ = cache101 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_050
    · rfl
    · exact triangle_update_062
    · rfl
    · exact triangle_update_010
    · rfl
    · exact triangle_update_098
    · rfl
    · exact triangle_update_130
    · rfl
    · exact triangle_update_118
    · rfl
    · rfl
    · exact triangle_update_162
    · rfl
    · exact triangle_update_170
  · intro k
    fin_cases k
    · exact singleton_update_030
    · rfl
    · rfl
    · exact singleton_update_022
    · exact singleton_update_030
    · rfl
    · exact singleton_update_070
    · rfl
    · exact singleton_update_082
    · rfl
    · exact singleton_update_062
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_098_3 :
    step cache098 (coordinate 19) ⟨3, by decide⟩ = cache102 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_051
    · rfl
    · exact triangle_update_063
    · rfl
    · exact triangle_update_011
    · rfl
    · exact triangle_update_099
    · rfl
    · exact triangle_update_131
    · rfl
    · exact triangle_update_119
    · rfl
    · rfl
    · exact triangle_update_163
    · rfl
    · exact triangle_update_171
  · intro k
    fin_cases k
    · exact singleton_update_031
    · rfl
    · rfl
    · exact singleton_update_023
    · exact singleton_update_031
    · rfl
    · exact singleton_update_071
    · rfl
    · exact singleton_update_083
    · rfl
    · exact singleton_update_063
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_091_3 :
    step cache091 (coordinate 18) ⟨3, by decide⟩ = cache103 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_187
    · exact triangle_update_039
    · rfl
    · rfl
    · exact triangle_update_179
    · exact triangle_update_027
    · rfl
    · rfl
    · exact triangle_update_207
    · exact triangle_update_127
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_175
    · exact triangle_update_227
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_055
    · exact singleton_update_055
    · rfl
    · rfl
    · exact singleton_update_043
    · rfl
    · exact singleton_update_043
    · rfl
    · exact singleton_update_067
    · rfl
    · exact singleton_update_067
    · rfl
    · rfl
    · exact singleton_update_119
    · rfl

theorem step_103_0 :
    step cache103 (coordinate 19) ⟨0, by decide⟩ = cache104 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_044
    · rfl
    · exact triangle_update_060
    · rfl
    · exact triangle_update_020
    · rfl
    · exact triangle_update_096
    · rfl
    · exact triangle_update_108
    · rfl
    · exact triangle_update_116
    · rfl
    · rfl
    · exact triangle_update_160
    · rfl
    · exact triangle_update_156
  · intro k
    fin_cases k
    · exact singleton_update_028
    · rfl
    · rfl
    · exact singleton_update_020
    · exact singleton_update_028
    · rfl
    · exact singleton_update_068
    · rfl
    · exact singleton_update_080
    · rfl
    · exact singleton_update_060
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_103_1 :
    step cache103 (coordinate 19) ⟨1, by decide⟩ = cache105 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_045
    · rfl
    · exact triangle_update_061
    · rfl
    · exact triangle_update_021
    · rfl
    · exact triangle_update_097
    · rfl
    · exact triangle_update_109
    · rfl
    · exact triangle_update_117
    · rfl
    · rfl
    · exact triangle_update_161
    · rfl
    · exact triangle_update_157
  · intro k
    fin_cases k
    · exact singleton_update_029
    · rfl
    · rfl
    · exact singleton_update_021
    · exact singleton_update_029
    · rfl
    · exact singleton_update_069
    · rfl
    · exact singleton_update_081
    · rfl
    · exact singleton_update_061
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_103_2 :
    step cache103 (coordinate 19) ⟨2, by decide⟩ = cache106 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_046
    · rfl
    · exact triangle_update_062
    · rfl
    · exact triangle_update_022
    · rfl
    · exact triangle_update_098
    · rfl
    · exact triangle_update_110
    · rfl
    · exact triangle_update_118
    · rfl
    · rfl
    · exact triangle_update_162
    · rfl
    · exact triangle_update_158
  · intro k
    fin_cases k
    · exact singleton_update_030
    · rfl
    · rfl
    · exact singleton_update_022
    · exact singleton_update_030
    · rfl
    · exact singleton_update_070
    · rfl
    · exact singleton_update_082
    · rfl
    · exact singleton_update_062
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_103_3 :
    step cache103 (coordinate 19) ⟨3, by decide⟩ = cache107 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_047
    · rfl
    · exact triangle_update_063
    · rfl
    · exact triangle_update_023
    · rfl
    · exact triangle_update_099
    · rfl
    · exact triangle_update_111
    · rfl
    · exact triangle_update_119
    · rfl
    · rfl
    · exact triangle_update_163
    · rfl
    · exact triangle_update_159
  · intro k
    fin_cases k
    · exact singleton_update_031
    · rfl
    · rfl
    · exact singleton_update_023
    · exact singleton_update_031
    · rfl
    · exact singleton_update_071
    · rfl
    · exact singleton_update_083
    · rfl
    · exact singleton_update_063
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_068_3 :
    step cache068 (coordinate 17) ⟨3, by decide⟩ = cache108 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · rfl
    · exact triangle_update_191
    · rfl
    · exact triangle_update_063
    · rfl
    · exact triangle_update_183
    · rfl
    · exact triangle_update_103
    · rfl
    · exact triangle_update_211
    · rfl
    · exact triangle_update_115
    · exact triangle_update_163
    · rfl
    · exact triangle_update_231
    · rfl
  · intro k
    fin_cases k
    · exact singleton_update_135
    · rfl
    · rfl
    · exact singleton_update_131
    · exact singleton_update_135
    · rfl
    · exact singleton_update_159
    · rfl
    · exact singleton_update_147
    · rfl
    · exact singleton_update_151
    · rfl
    · rfl
    · exact singleton_update_127
    · rfl
    · rfl

theorem step_108_0 :
    step cache108 (coordinate 18) ⟨0, by decide⟩ = cache109 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_184
    · exact triangle_update_016
    · rfl
    · rfl
    · exact triangle_update_176
    · exact triangle_update_012
    · rfl
    · rfl
    · exact triangle_update_204
    · exact triangle_update_076
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_152
    · exact triangle_update_224
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_052
    · exact singleton_update_052
    · rfl
    · rfl
    · exact singleton_update_040
    · rfl
    · exact singleton_update_040
    · rfl
    · exact singleton_update_064
    · rfl
    · exact singleton_update_064
    · rfl
    · rfl
    · exact singleton_update_116
    · rfl

theorem step_108_1 :
    step cache108 (coordinate 18) ⟨1, by decide⟩ = cache110 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_185
    · exact triangle_update_017
    · rfl
    · rfl
    · exact triangle_update_177
    · exact triangle_update_013
    · rfl
    · rfl
    · exact triangle_update_205
    · exact triangle_update_077
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_153
    · exact triangle_update_225
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_053
    · exact singleton_update_053
    · rfl
    · rfl
    · exact singleton_update_041
    · rfl
    · exact singleton_update_041
    · rfl
    · exact singleton_update_065
    · rfl
    · exact singleton_update_065
    · rfl
    · rfl
    · exact singleton_update_117
    · rfl

theorem step_110_0 :
    step cache110 (coordinate 19) ⟨0, by decide⟩ = cache111 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_052
    · rfl
    · exact triangle_update_060
    · rfl
    · exact triangle_update_028
    · rfl
    · exact triangle_update_096
    · rfl
    · exact triangle_update_080
    · rfl
    · exact triangle_update_116
    · rfl
    · rfl
    · exact triangle_update_160
    · rfl
    · exact triangle_update_136
  · intro k
    fin_cases k
    · exact singleton_update_012
    · rfl
    · rfl
    · exact singleton_update_008
    · exact singleton_update_012
    · rfl
    · exact singleton_update_108
    · rfl
    · exact singleton_update_084
    · rfl
    · exact singleton_update_092
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_110_1 :
    step cache110 (coordinate 19) ⟨1, by decide⟩ = cache112 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_053
    · rfl
    · exact triangle_update_061
    · rfl
    · exact triangle_update_029
    · rfl
    · exact triangle_update_097
    · rfl
    · exact triangle_update_081
    · rfl
    · exact triangle_update_117
    · rfl
    · rfl
    · exact triangle_update_161
    · rfl
    · exact triangle_update_137
  · intro k
    fin_cases k
    · exact singleton_update_013
    · rfl
    · rfl
    · exact singleton_update_009
    · exact singleton_update_013
    · rfl
    · exact singleton_update_109
    · rfl
    · exact singleton_update_085
    · rfl
    · exact singleton_update_093
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_110_2 :
    step cache110 (coordinate 19) ⟨2, by decide⟩ = cache113 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_054
    · rfl
    · exact triangle_update_062
    · rfl
    · exact triangle_update_030
    · rfl
    · exact triangle_update_098
    · rfl
    · exact triangle_update_082
    · rfl
    · exact triangle_update_118
    · rfl
    · rfl
    · exact triangle_update_162
    · rfl
    · exact triangle_update_138
  · intro k
    fin_cases k
    · exact singleton_update_014
    · rfl
    · rfl
    · exact singleton_update_010
    · exact singleton_update_014
    · rfl
    · exact singleton_update_110
    · rfl
    · exact singleton_update_086
    · rfl
    · exact singleton_update_094
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_110_3 :
    step cache110 (coordinate 19) ⟨3, by decide⟩ = cache114 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_055
    · rfl
    · exact triangle_update_063
    · rfl
    · exact triangle_update_031
    · rfl
    · exact triangle_update_099
    · rfl
    · exact triangle_update_083
    · rfl
    · exact triangle_update_119
    · rfl
    · rfl
    · exact triangle_update_163
    · rfl
    · exact triangle_update_139
  · intro k
    fin_cases k
    · exact singleton_update_015
    · rfl
    · rfl
    · exact singleton_update_011
    · exact singleton_update_015
    · rfl
    · exact singleton_update_111
    · rfl
    · exact singleton_update_087
    · rfl
    · exact singleton_update_095
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_108_2 :
    step cache108 (coordinate 18) ⟨2, by decide⟩ = cache115 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_186
    · exact triangle_update_018
    · rfl
    · rfl
    · exact triangle_update_178
    · exact triangle_update_014
    · rfl
    · rfl
    · exact triangle_update_206
    · exact triangle_update_078
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_154
    · exact triangle_update_226
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_054
    · exact singleton_update_054
    · rfl
    · rfl
    · exact singleton_update_042
    · rfl
    · exact singleton_update_042
    · rfl
    · exact singleton_update_066
    · rfl
    · exact singleton_update_066
    · rfl
    · rfl
    · exact singleton_update_118
    · rfl

theorem step_115_0 :
    step cache115 (coordinate 19) ⟨0, by decide⟩ = cache116 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_048
    · rfl
    · exact triangle_update_060
    · rfl
    · exact triangle_update_008
    · rfl
    · exact triangle_update_096
    · rfl
    · exact triangle_update_128
    · rfl
    · exact triangle_update_116
    · rfl
    · rfl
    · exact triangle_update_160
    · rfl
    · exact triangle_update_168
  · intro k
    fin_cases k
    · exact singleton_update_012
    · rfl
    · rfl
    · exact singleton_update_008
    · exact singleton_update_012
    · rfl
    · exact singleton_update_108
    · rfl
    · exact singleton_update_084
    · rfl
    · exact singleton_update_092
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_115_1 :
    step cache115 (coordinate 19) ⟨1, by decide⟩ = cache117 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_049
    · rfl
    · exact triangle_update_061
    · rfl
    · exact triangle_update_009
    · rfl
    · exact triangle_update_097
    · rfl
    · exact triangle_update_129
    · rfl
    · exact triangle_update_117
    · rfl
    · rfl
    · exact triangle_update_161
    · rfl
    · exact triangle_update_169
  · intro k
    fin_cases k
    · exact singleton_update_013
    · rfl
    · rfl
    · exact singleton_update_009
    · exact singleton_update_013
    · rfl
    · exact singleton_update_109
    · rfl
    · exact singleton_update_085
    · rfl
    · exact singleton_update_093
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_115_2 :
    step cache115 (coordinate 19) ⟨2, by decide⟩ = cache118 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_050
    · rfl
    · exact triangle_update_062
    · rfl
    · exact triangle_update_010
    · rfl
    · exact triangle_update_098
    · rfl
    · exact triangle_update_130
    · rfl
    · exact triangle_update_118
    · rfl
    · rfl
    · exact triangle_update_162
    · rfl
    · exact triangle_update_170
  · intro k
    fin_cases k
    · exact singleton_update_014
    · rfl
    · rfl
    · exact singleton_update_010
    · exact singleton_update_014
    · rfl
    · exact singleton_update_110
    · rfl
    · exact singleton_update_086
    · rfl
    · exact singleton_update_094
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_115_3 :
    step cache115 (coordinate 19) ⟨3, by decide⟩ = cache119 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_051
    · rfl
    · exact triangle_update_063
    · rfl
    · exact triangle_update_011
    · rfl
    · exact triangle_update_099
    · rfl
    · exact triangle_update_131
    · rfl
    · exact triangle_update_119
    · rfl
    · rfl
    · exact triangle_update_163
    · rfl
    · exact triangle_update_171
  · intro k
    fin_cases k
    · exact singleton_update_015
    · rfl
    · rfl
    · exact singleton_update_011
    · exact singleton_update_015
    · rfl
    · exact singleton_update_111
    · rfl
    · exact singleton_update_087
    · rfl
    · exact singleton_update_095
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

theorem step_108_3 :
    step cache108 (coordinate 18) ⟨3, by decide⟩ = cache120 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_187
    · exact triangle_update_019
    · rfl
    · rfl
    · exact triangle_update_179
    · exact triangle_update_015
    · rfl
    · rfl
    · exact triangle_update_207
    · exact triangle_update_079
    · rfl
    · rfl
    · rfl
    · rfl
    · exact triangle_update_155
    · exact triangle_update_227
  · intro k
    fin_cases k
    · rfl
    · exact singleton_update_055
    · exact singleton_update_055
    · rfl
    · rfl
    · exact singleton_update_043
    · rfl
    · exact singleton_update_043
    · rfl
    · exact singleton_update_067
    · rfl
    · exact singleton_update_067
    · rfl
    · rfl
    · exact singleton_update_119
    · rfl

theorem step_120_0 :
    step cache120 (coordinate 19) ⟨0, by decide⟩ = cache121 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_044
    · rfl
    · exact triangle_update_060
    · rfl
    · exact triangle_update_020
    · rfl
    · exact triangle_update_096
    · rfl
    · exact triangle_update_108
    · rfl
    · exact triangle_update_116
    · rfl
    · rfl
    · exact triangle_update_160
    · rfl
    · exact triangle_update_156
  · intro k
    fin_cases k
    · exact singleton_update_012
    · rfl
    · rfl
    · exact singleton_update_008
    · exact singleton_update_012
    · rfl
    · exact singleton_update_108
    · rfl
    · exact singleton_update_084
    · rfl
    · exact singleton_update_092
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_124

theorem step_120_1 :
    step cache120 (coordinate 19) ⟨1, by decide⟩ = cache122 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_045
    · rfl
    · exact triangle_update_061
    · rfl
    · exact triangle_update_021
    · rfl
    · exact triangle_update_097
    · rfl
    · exact triangle_update_109
    · rfl
    · exact triangle_update_117
    · rfl
    · rfl
    · exact triangle_update_161
    · rfl
    · exact triangle_update_157
  · intro k
    fin_cases k
    · exact singleton_update_013
    · rfl
    · rfl
    · exact singleton_update_009
    · exact singleton_update_013
    · rfl
    · exact singleton_update_109
    · rfl
    · exact singleton_update_085
    · rfl
    · exact singleton_update_093
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_125

theorem step_120_2 :
    step cache120 (coordinate 19) ⟨2, by decide⟩ = cache123 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_046
    · rfl
    · exact triangle_update_062
    · rfl
    · exact triangle_update_022
    · rfl
    · exact triangle_update_098
    · rfl
    · exact triangle_update_110
    · rfl
    · exact triangle_update_118
    · rfl
    · rfl
    · exact triangle_update_162
    · rfl
    · exact triangle_update_158
  · intro k
    fin_cases k
    · exact singleton_update_014
    · rfl
    · rfl
    · exact singleton_update_010
    · exact singleton_update_014
    · rfl
    · exact singleton_update_110
    · rfl
    · exact singleton_update_086
    · rfl
    · exact singleton_update_094
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_126

theorem step_120_3 :
    step cache120 (coordinate 19) ⟨3, by decide⟩ = cache124 := by
  apply step_eq_of_local_eq
  · intro k
    fin_cases k
    · exact triangle_update_047
    · rfl
    · exact triangle_update_063
    · rfl
    · exact triangle_update_023
    · rfl
    · exact triangle_update_099
    · rfl
    · exact triangle_update_111
    · rfl
    · exact triangle_update_119
    · rfl
    · rfl
    · exact triangle_update_163
    · rfl
    · exact triangle_update_159
  · intro k
    fin_cases k
    · exact singleton_update_015
    · rfl
    · rfl
    · exact singleton_update_011
    · exact singleton_update_015
    · rfl
    · exact singleton_update_111
    · rfl
    · exact singleton_update_087
    · rfl
    · exact singleton_update_095
    · rfl
    · rfl
    · rfl
    · rfl
    · exact singleton_update_127

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem root_cache_receipt :
    Tail442V2.Helper.checkFullCache (prefixCache 16 329851) cache000 = true := by
  decide +kernel

theorem actual_cache000 : prefixCache 16 329851 = cache000 :=
  cache_eq_of_checked _ _ root_cache_receipt

theorem actual_cache001 : prefixCache 17 1319404 = cache001 := by
  change step (prefixCache 16 329851) (coordinate 16)
    ⟨0, by decide⟩ = cache001
  exact (congrArg (fun cache => step cache (coordinate 16) ⟨0, by decide⟩)
    actual_cache000).trans step_000_0

theorem actual_cache002 : prefixCache 17 1319405 = cache002 := by
  change step (prefixCache 16 329851) (coordinate 16)
    ⟨1, by decide⟩ = cache002
  exact (congrArg (fun cache => step cache (coordinate 16) ⟨1, by decide⟩)
    actual_cache000).trans step_000_1

theorem actual_cache003 : prefixCache 18 5277620 = cache003 := by
  change step (prefixCache 17 1319405) (coordinate 17)
    ⟨0, by decide⟩ = cache003
  exact (congrArg (fun cache => step cache (coordinate 17) ⟨0, by decide⟩)
    actual_cache002).trans step_002_0

theorem actual_cache004 : prefixCache 18 5277621 = cache004 := by
  change step (prefixCache 17 1319405) (coordinate 17)
    ⟨1, by decide⟩ = cache004
  exact (congrArg (fun cache => step cache (coordinate 17) ⟨1, by decide⟩)
    actual_cache002).trans step_002_1

theorem actual_cache005 : prefixCache 18 5277622 = cache005 := by
  change step (prefixCache 17 1319405) (coordinate 17)
    ⟨2, by decide⟩ = cache005
  exact (congrArg (fun cache => step cache (coordinate 17) ⟨2, by decide⟩)
    actual_cache002).trans step_002_2

theorem actual_cache006 : prefixCache 18 5277623 = cache006 := by
  change step (prefixCache 17 1319405) (coordinate 17)
    ⟨3, by decide⟩ = cache006
  exact (congrArg (fun cache => step cache (coordinate 17) ⟨3, by decide⟩)
    actual_cache002).trans step_002_3

theorem actual_cache007 : prefixCache 19 21110492 = cache007 := by
  change step (prefixCache 18 5277623) (coordinate 18)
    ⟨0, by decide⟩ = cache007
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨0, by decide⟩)
    actual_cache006).trans step_006_0

theorem actual_cache008 : prefixCache 19 21110493 = cache008 := by
  change step (prefixCache 18 5277623) (coordinate 18)
    ⟨1, by decide⟩ = cache008
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨1, by decide⟩)
    actual_cache006).trans step_006_1

theorem actual_cache009 : prefixCache 19 21110494 = cache009 := by
  change step (prefixCache 18 5277623) (coordinate 18)
    ⟨2, by decide⟩ = cache009
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨2, by decide⟩)
    actual_cache006).trans step_006_2

theorem actual_cache010 : prefixCache 19 21110495 = cache010 := by
  change step (prefixCache 18 5277623) (coordinate 18)
    ⟨3, by decide⟩ = cache010
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨3, by decide⟩)
    actual_cache006).trans step_006_3

theorem actual_cache011 : prefixCache 17 1319406 = cache011 := by
  change step (prefixCache 16 329851) (coordinate 16)
    ⟨2, by decide⟩ = cache011
  exact (congrArg (fun cache => step cache (coordinate 16) ⟨2, by decide⟩)
    actual_cache000).trans step_000_2

theorem actual_cache012 : prefixCache 18 5277624 = cache012 := by
  change step (prefixCache 17 1319406) (coordinate 17)
    ⟨0, by decide⟩ = cache012
  exact (congrArg (fun cache => step cache (coordinate 17) ⟨0, by decide⟩)
    actual_cache011).trans step_011_0

theorem actual_cache013 : prefixCache 19 21110496 = cache013 := by
  change step (prefixCache 18 5277624) (coordinate 18)
    ⟨0, by decide⟩ = cache013
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨0, by decide⟩)
    actual_cache012).trans step_012_0

theorem actual_cache014 : prefixCache 19 21110497 = cache014 := by
  change step (prefixCache 18 5277624) (coordinate 18)
    ⟨1, by decide⟩ = cache014
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨1, by decide⟩)
    actual_cache012).trans step_012_1

theorem actual_cache015 : prefixCache 20 84441988 = cache015 := by
  change step (prefixCache 19 21110497) (coordinate 19)
    ⟨0, by decide⟩ = cache015
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache014).trans step_014_0

theorem actual_cache016 : prefixCache 20 84441989 = cache016 := by
  change step (prefixCache 19 21110497) (coordinate 19)
    ⟨1, by decide⟩ = cache016
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache014).trans step_014_1

theorem actual_cache017 : prefixCache 20 84441990 = cache017 := by
  change step (prefixCache 19 21110497) (coordinate 19)
    ⟨2, by decide⟩ = cache017
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache014).trans step_014_2

theorem actual_cache018 : prefixCache 20 84441991 = cache018 := by
  change step (prefixCache 19 21110497) (coordinate 19)
    ⟨3, by decide⟩ = cache018
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache014).trans step_014_3

theorem actual_cache019 : prefixCache 19 21110498 = cache019 := by
  change step (prefixCache 18 5277624) (coordinate 18)
    ⟨2, by decide⟩ = cache019
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨2, by decide⟩)
    actual_cache012).trans step_012_2

theorem actual_cache020 : prefixCache 19 21110499 = cache020 := by
  change step (prefixCache 18 5277624) (coordinate 18)
    ⟨3, by decide⟩ = cache020
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨3, by decide⟩)
    actual_cache012).trans step_012_3

theorem actual_cache021 : prefixCache 20 84441996 = cache021 := by
  change step (prefixCache 19 21110499) (coordinate 19)
    ⟨0, by decide⟩ = cache021
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache020).trans step_020_0

theorem actual_cache022 : prefixCache 20 84441997 = cache022 := by
  change step (prefixCache 19 21110499) (coordinate 19)
    ⟨1, by decide⟩ = cache022
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache020).trans step_020_1

theorem actual_cache023 : prefixCache 20 84441998 = cache023 := by
  change step (prefixCache 19 21110499) (coordinate 19)
    ⟨2, by decide⟩ = cache023
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache020).trans step_020_2

theorem actual_cache024 : prefixCache 20 84441999 = cache024 := by
  change step (prefixCache 19 21110499) (coordinate 19)
    ⟨3, by decide⟩ = cache024
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache020).trans step_020_3

theorem actual_cache025 : prefixCache 18 5277625 = cache025 := by
  change step (prefixCache 17 1319406) (coordinate 17)
    ⟨1, by decide⟩ = cache025
  exact (congrArg (fun cache => step cache (coordinate 17) ⟨1, by decide⟩)
    actual_cache011).trans step_011_1

theorem actual_cache026 : prefixCache 19 21110500 = cache026 := by
  change step (prefixCache 18 5277625) (coordinate 18)
    ⟨0, by decide⟩ = cache026
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨0, by decide⟩)
    actual_cache025).trans step_025_0

theorem actual_cache027 : prefixCache 19 21110501 = cache027 := by
  change step (prefixCache 18 5277625) (coordinate 18)
    ⟨1, by decide⟩ = cache027
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨1, by decide⟩)
    actual_cache025).trans step_025_1

theorem actual_cache028 : prefixCache 20 84442004 = cache028 := by
  change step (prefixCache 19 21110501) (coordinate 19)
    ⟨0, by decide⟩ = cache028
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache027).trans step_027_0

theorem actual_cache029 : prefixCache 20 84442005 = cache029 := by
  change step (prefixCache 19 21110501) (coordinate 19)
    ⟨1, by decide⟩ = cache029
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache027).trans step_027_1

theorem actual_cache030 : prefixCache 20 84442006 = cache030 := by
  change step (prefixCache 19 21110501) (coordinate 19)
    ⟨2, by decide⟩ = cache030
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache027).trans step_027_2

theorem actual_cache031 : prefixCache 20 84442007 = cache031 := by
  change step (prefixCache 19 21110501) (coordinate 19)
    ⟨3, by decide⟩ = cache031
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache027).trans step_027_3

theorem actual_cache032 : prefixCache 19 21110502 = cache032 := by
  change step (prefixCache 18 5277625) (coordinate 18)
    ⟨2, by decide⟩ = cache032
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨2, by decide⟩)
    actual_cache025).trans step_025_2

theorem actual_cache033 : prefixCache 19 21110503 = cache033 := by
  change step (prefixCache 18 5277625) (coordinate 18)
    ⟨3, by decide⟩ = cache033
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨3, by decide⟩)
    actual_cache025).trans step_025_3

theorem actual_cache034 : prefixCache 20 84442012 = cache034 := by
  change step (prefixCache 19 21110503) (coordinate 19)
    ⟨0, by decide⟩ = cache034
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache033).trans step_033_0

theorem actual_cache035 : prefixCache 20 84442013 = cache035 := by
  change step (prefixCache 19 21110503) (coordinate 19)
    ⟨1, by decide⟩ = cache035
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache033).trans step_033_1

theorem actual_cache036 : prefixCache 20 84442014 = cache036 := by
  change step (prefixCache 19 21110503) (coordinate 19)
    ⟨2, by decide⟩ = cache036
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache033).trans step_033_2

theorem actual_cache037 : prefixCache 20 84442015 = cache037 := by
  change step (prefixCache 19 21110503) (coordinate 19)
    ⟨3, by decide⟩ = cache037
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache033).trans step_033_3

theorem actual_cache038 : prefixCache 18 5277626 = cache038 := by
  change step (prefixCache 17 1319406) (coordinate 17)
    ⟨2, by decide⟩ = cache038
  exact (congrArg (fun cache => step cache (coordinate 17) ⟨2, by decide⟩)
    actual_cache011).trans step_011_2

theorem actual_cache039 : prefixCache 19 21110504 = cache039 := by
  change step (prefixCache 18 5277626) (coordinate 18)
    ⟨0, by decide⟩ = cache039
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨0, by decide⟩)
    actual_cache038).trans step_038_0

theorem actual_cache040 : prefixCache 19 21110505 = cache040 := by
  change step (prefixCache 18 5277626) (coordinate 18)
    ⟨1, by decide⟩ = cache040
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨1, by decide⟩)
    actual_cache038).trans step_038_1

theorem actual_cache041 : prefixCache 20 84442020 = cache041 := by
  change step (prefixCache 19 21110505) (coordinate 19)
    ⟨0, by decide⟩ = cache041
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache040).trans step_040_0

theorem actual_cache042 : prefixCache 20 84442021 = cache042 := by
  change step (prefixCache 19 21110505) (coordinate 19)
    ⟨1, by decide⟩ = cache042
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache040).trans step_040_1

theorem actual_cache043 : prefixCache 20 84442022 = cache043 := by
  change step (prefixCache 19 21110505) (coordinate 19)
    ⟨2, by decide⟩ = cache043
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache040).trans step_040_2

theorem actual_cache044 : prefixCache 20 84442023 = cache044 := by
  change step (prefixCache 19 21110505) (coordinate 19)
    ⟨3, by decide⟩ = cache044
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache040).trans step_040_3

theorem actual_cache045 : prefixCache 19 21110506 = cache045 := by
  change step (prefixCache 18 5277626) (coordinate 18)
    ⟨2, by decide⟩ = cache045
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨2, by decide⟩)
    actual_cache038).trans step_038_2

theorem actual_cache046 : prefixCache 19 21110507 = cache046 := by
  change step (prefixCache 18 5277626) (coordinate 18)
    ⟨3, by decide⟩ = cache046
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨3, by decide⟩)
    actual_cache038).trans step_038_3

theorem actual_cache047 : prefixCache 20 84442028 = cache047 := by
  change step (prefixCache 19 21110507) (coordinate 19)
    ⟨0, by decide⟩ = cache047
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache046).trans step_046_0

theorem actual_cache048 : prefixCache 20 84442029 = cache048 := by
  change step (prefixCache 19 21110507) (coordinate 19)
    ⟨1, by decide⟩ = cache048
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache046).trans step_046_1

theorem actual_cache049 : prefixCache 20 84442030 = cache049 := by
  change step (prefixCache 19 21110507) (coordinate 19)
    ⟨2, by decide⟩ = cache049
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache046).trans step_046_2

theorem actual_cache050 : prefixCache 20 84442031 = cache050 := by
  change step (prefixCache 19 21110507) (coordinate 19)
    ⟨3, by decide⟩ = cache050
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache046).trans step_046_3

theorem actual_cache051 : prefixCache 18 5277627 = cache051 := by
  change step (prefixCache 17 1319406) (coordinate 17)
    ⟨3, by decide⟩ = cache051
  exact (congrArg (fun cache => step cache (coordinate 17) ⟨3, by decide⟩)
    actual_cache011).trans step_011_3

theorem actual_cache052 : prefixCache 19 21110508 = cache052 := by
  change step (prefixCache 18 5277627) (coordinate 18)
    ⟨0, by decide⟩ = cache052
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨0, by decide⟩)
    actual_cache051).trans step_051_0

theorem actual_cache053 : prefixCache 19 21110509 = cache053 := by
  change step (prefixCache 18 5277627) (coordinate 18)
    ⟨1, by decide⟩ = cache053
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨1, by decide⟩)
    actual_cache051).trans step_051_1

theorem actual_cache054 : prefixCache 20 84442036 = cache054 := by
  change step (prefixCache 19 21110509) (coordinate 19)
    ⟨0, by decide⟩ = cache054
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache053).trans step_053_0

theorem actual_cache055 : prefixCache 20 84442037 = cache055 := by
  change step (prefixCache 19 21110509) (coordinate 19)
    ⟨1, by decide⟩ = cache055
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache053).trans step_053_1

theorem actual_cache056 : prefixCache 20 84442038 = cache056 := by
  change step (prefixCache 19 21110509) (coordinate 19)
    ⟨2, by decide⟩ = cache056
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache053).trans step_053_2

theorem actual_cache057 : prefixCache 20 84442039 = cache057 := by
  change step (prefixCache 19 21110509) (coordinate 19)
    ⟨3, by decide⟩ = cache057
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache053).trans step_053_3

theorem actual_cache058 : prefixCache 19 21110510 = cache058 := by
  change step (prefixCache 18 5277627) (coordinate 18)
    ⟨2, by decide⟩ = cache058
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨2, by decide⟩)
    actual_cache051).trans step_051_2

theorem actual_cache059 : prefixCache 20 84442040 = cache059 := by
  change step (prefixCache 19 21110510) (coordinate 19)
    ⟨0, by decide⟩ = cache059
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache058).trans step_058_0

theorem actual_cache060 : prefixCache 20 84442041 = cache060 := by
  change step (prefixCache 19 21110510) (coordinate 19)
    ⟨1, by decide⟩ = cache060
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache058).trans step_058_1

theorem actual_cache061 : prefixCache 20 84442042 = cache061 := by
  change step (prefixCache 19 21110510) (coordinate 19)
    ⟨2, by decide⟩ = cache061
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache058).trans step_058_2

theorem actual_cache062 : prefixCache 20 84442043 = cache062 := by
  change step (prefixCache 19 21110510) (coordinate 19)
    ⟨3, by decide⟩ = cache062
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache058).trans step_058_3

theorem actual_cache063 : prefixCache 19 21110511 = cache063 := by
  change step (prefixCache 18 5277627) (coordinate 18)
    ⟨3, by decide⟩ = cache063
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨3, by decide⟩)
    actual_cache051).trans step_051_3

theorem actual_cache064 : prefixCache 20 84442044 = cache064 := by
  change step (prefixCache 19 21110511) (coordinate 19)
    ⟨0, by decide⟩ = cache064
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache063).trans step_063_0

theorem actual_cache065 : prefixCache 20 84442045 = cache065 := by
  change step (prefixCache 19 21110511) (coordinate 19)
    ⟨1, by decide⟩ = cache065
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache063).trans step_063_1

theorem actual_cache066 : prefixCache 20 84442046 = cache066 := by
  change step (prefixCache 19 21110511) (coordinate 19)
    ⟨2, by decide⟩ = cache066
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache063).trans step_063_2

theorem actual_cache067 : prefixCache 20 84442047 = cache067 := by
  change step (prefixCache 19 21110511) (coordinate 19)
    ⟨3, by decide⟩ = cache067
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache063).trans step_063_3

theorem actual_cache068 : prefixCache 17 1319407 = cache068 := by
  change step (prefixCache 16 329851) (coordinate 16)
    ⟨3, by decide⟩ = cache068
  exact (congrArg (fun cache => step cache (coordinate 16) ⟨3, by decide⟩)
    actual_cache000).trans step_000_3

theorem actual_cache069 : prefixCache 18 5277628 = cache069 := by
  change step (prefixCache 17 1319407) (coordinate 17)
    ⟨0, by decide⟩ = cache069
  exact (congrArg (fun cache => step cache (coordinate 17) ⟨0, by decide⟩)
    actual_cache068).trans step_068_0

theorem actual_cache070 : prefixCache 19 21110512 = cache070 := by
  change step (prefixCache 18 5277628) (coordinate 18)
    ⟨0, by decide⟩ = cache070
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨0, by decide⟩)
    actual_cache069).trans step_069_0

theorem actual_cache071 : prefixCache 19 21110513 = cache071 := by
  change step (prefixCache 18 5277628) (coordinate 18)
    ⟨1, by decide⟩ = cache071
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨1, by decide⟩)
    actual_cache069).trans step_069_1

theorem actual_cache072 : prefixCache 20 84442052 = cache072 := by
  change step (prefixCache 19 21110513) (coordinate 19)
    ⟨0, by decide⟩ = cache072
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache071).trans step_071_0

theorem actual_cache073 : prefixCache 20 84442053 = cache073 := by
  change step (prefixCache 19 21110513) (coordinate 19)
    ⟨1, by decide⟩ = cache073
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache071).trans step_071_1

theorem actual_cache074 : prefixCache 20 84442054 = cache074 := by
  change step (prefixCache 19 21110513) (coordinate 19)
    ⟨2, by decide⟩ = cache074
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache071).trans step_071_2

theorem actual_cache075 : prefixCache 20 84442055 = cache075 := by
  change step (prefixCache 19 21110513) (coordinate 19)
    ⟨3, by decide⟩ = cache075
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache071).trans step_071_3

theorem actual_cache076 : prefixCache 19 21110514 = cache076 := by
  change step (prefixCache 18 5277628) (coordinate 18)
    ⟨2, by decide⟩ = cache076
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨2, by decide⟩)
    actual_cache069).trans step_069_2

theorem actual_cache077 : prefixCache 19 21110515 = cache077 := by
  change step (prefixCache 18 5277628) (coordinate 18)
    ⟨3, by decide⟩ = cache077
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨3, by decide⟩)
    actual_cache069).trans step_069_3

theorem actual_cache078 : prefixCache 20 84442060 = cache078 := by
  change step (prefixCache 19 21110515) (coordinate 19)
    ⟨0, by decide⟩ = cache078
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache077).trans step_077_0

theorem actual_cache079 : prefixCache 20 84442061 = cache079 := by
  change step (prefixCache 19 21110515) (coordinate 19)
    ⟨1, by decide⟩ = cache079
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache077).trans step_077_1

theorem actual_cache080 : prefixCache 20 84442062 = cache080 := by
  change step (prefixCache 19 21110515) (coordinate 19)
    ⟨2, by decide⟩ = cache080
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache077).trans step_077_2

theorem actual_cache081 : prefixCache 20 84442063 = cache081 := by
  change step (prefixCache 19 21110515) (coordinate 19)
    ⟨3, by decide⟩ = cache081
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache077).trans step_077_3

theorem actual_cache082 : prefixCache 18 5277629 = cache082 := by
  change step (prefixCache 17 1319407) (coordinate 17)
    ⟨1, by decide⟩ = cache082
  exact (congrArg (fun cache => step cache (coordinate 17) ⟨1, by decide⟩)
    actual_cache068).trans step_068_1

theorem actual_cache083 : prefixCache 19 21110516 = cache083 := by
  change step (prefixCache 18 5277629) (coordinate 18)
    ⟨0, by decide⟩ = cache083
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨0, by decide⟩)
    actual_cache082).trans step_082_0

theorem actual_cache084 : prefixCache 19 21110517 = cache084 := by
  change step (prefixCache 18 5277629) (coordinate 18)
    ⟨1, by decide⟩ = cache084
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨1, by decide⟩)
    actual_cache082).trans step_082_1

theorem actual_cache085 : prefixCache 20 84442068 = cache085 := by
  change step (prefixCache 19 21110517) (coordinate 19)
    ⟨0, by decide⟩ = cache085
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache084).trans step_084_0

theorem actual_cache086 : prefixCache 20 84442069 = cache086 := by
  change step (prefixCache 19 21110517) (coordinate 19)
    ⟨1, by decide⟩ = cache086
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache084).trans step_084_1

theorem actual_cache087 : prefixCache 20 84442070 = cache087 := by
  change step (prefixCache 19 21110517) (coordinate 19)
    ⟨2, by decide⟩ = cache087
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache084).trans step_084_2

theorem actual_cache088 : prefixCache 20 84442071 = cache088 := by
  change step (prefixCache 19 21110517) (coordinate 19)
    ⟨3, by decide⟩ = cache088
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache084).trans step_084_3

theorem actual_cache089 : prefixCache 19 21110518 = cache089 := by
  change step (prefixCache 18 5277629) (coordinate 18)
    ⟨2, by decide⟩ = cache089
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨2, by decide⟩)
    actual_cache082).trans step_082_2

theorem actual_cache090 : prefixCache 19 21110519 = cache090 := by
  change step (prefixCache 18 5277629) (coordinate 18)
    ⟨3, by decide⟩ = cache090
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨3, by decide⟩)
    actual_cache082).trans step_082_3

theorem actual_cache091 : prefixCache 18 5277630 = cache091 := by
  change step (prefixCache 17 1319407) (coordinate 17)
    ⟨2, by decide⟩ = cache091
  exact (congrArg (fun cache => step cache (coordinate 17) ⟨2, by decide⟩)
    actual_cache068).trans step_068_2

theorem actual_cache092 : prefixCache 19 21110520 = cache092 := by
  change step (prefixCache 18 5277630) (coordinate 18)
    ⟨0, by decide⟩ = cache092
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨0, by decide⟩)
    actual_cache091).trans step_091_0

theorem actual_cache093 : prefixCache 19 21110521 = cache093 := by
  change step (prefixCache 18 5277630) (coordinate 18)
    ⟨1, by decide⟩ = cache093
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨1, by decide⟩)
    actual_cache091).trans step_091_1

theorem actual_cache094 : prefixCache 20 84442084 = cache094 := by
  change step (prefixCache 19 21110521) (coordinate 19)
    ⟨0, by decide⟩ = cache094
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache093).trans step_093_0

theorem actual_cache095 : prefixCache 20 84442085 = cache095 := by
  change step (prefixCache 19 21110521) (coordinate 19)
    ⟨1, by decide⟩ = cache095
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache093).trans step_093_1

theorem actual_cache096 : prefixCache 20 84442086 = cache096 := by
  change step (prefixCache 19 21110521) (coordinate 19)
    ⟨2, by decide⟩ = cache096
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache093).trans step_093_2

theorem actual_cache097 : prefixCache 20 84442087 = cache097 := by
  change step (prefixCache 19 21110521) (coordinate 19)
    ⟨3, by decide⟩ = cache097
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache093).trans step_093_3

theorem actual_cache098 : prefixCache 19 21110522 = cache098 := by
  change step (prefixCache 18 5277630) (coordinate 18)
    ⟨2, by decide⟩ = cache098
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨2, by decide⟩)
    actual_cache091).trans step_091_2

theorem actual_cache099 : prefixCache 20 84442088 = cache099 := by
  change step (prefixCache 19 21110522) (coordinate 19)
    ⟨0, by decide⟩ = cache099
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache098).trans step_098_0

theorem actual_cache100 : prefixCache 20 84442089 = cache100 := by
  change step (prefixCache 19 21110522) (coordinate 19)
    ⟨1, by decide⟩ = cache100
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache098).trans step_098_1

theorem actual_cache101 : prefixCache 20 84442090 = cache101 := by
  change step (prefixCache 19 21110522) (coordinate 19)
    ⟨2, by decide⟩ = cache101
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache098).trans step_098_2

theorem actual_cache102 : prefixCache 20 84442091 = cache102 := by
  change step (prefixCache 19 21110522) (coordinate 19)
    ⟨3, by decide⟩ = cache102
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache098).trans step_098_3

theorem actual_cache103 : prefixCache 19 21110523 = cache103 := by
  change step (prefixCache 18 5277630) (coordinate 18)
    ⟨3, by decide⟩ = cache103
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨3, by decide⟩)
    actual_cache091).trans step_091_3

theorem actual_cache104 : prefixCache 20 84442092 = cache104 := by
  change step (prefixCache 19 21110523) (coordinate 19)
    ⟨0, by decide⟩ = cache104
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache103).trans step_103_0

theorem actual_cache105 : prefixCache 20 84442093 = cache105 := by
  change step (prefixCache 19 21110523) (coordinate 19)
    ⟨1, by decide⟩ = cache105
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache103).trans step_103_1

theorem actual_cache106 : prefixCache 20 84442094 = cache106 := by
  change step (prefixCache 19 21110523) (coordinate 19)
    ⟨2, by decide⟩ = cache106
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache103).trans step_103_2

theorem actual_cache107 : prefixCache 20 84442095 = cache107 := by
  change step (prefixCache 19 21110523) (coordinate 19)
    ⟨3, by decide⟩ = cache107
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache103).trans step_103_3

theorem actual_cache108 : prefixCache 18 5277631 = cache108 := by
  change step (prefixCache 17 1319407) (coordinate 17)
    ⟨3, by decide⟩ = cache108
  exact (congrArg (fun cache => step cache (coordinate 17) ⟨3, by decide⟩)
    actual_cache068).trans step_068_3

theorem actual_cache109 : prefixCache 19 21110524 = cache109 := by
  change step (prefixCache 18 5277631) (coordinate 18)
    ⟨0, by decide⟩ = cache109
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨0, by decide⟩)
    actual_cache108).trans step_108_0

theorem actual_cache110 : prefixCache 19 21110525 = cache110 := by
  change step (prefixCache 18 5277631) (coordinate 18)
    ⟨1, by decide⟩ = cache110
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨1, by decide⟩)
    actual_cache108).trans step_108_1

theorem actual_cache111 : prefixCache 20 84442100 = cache111 := by
  change step (prefixCache 19 21110525) (coordinate 19)
    ⟨0, by decide⟩ = cache111
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache110).trans step_110_0

theorem actual_cache112 : prefixCache 20 84442101 = cache112 := by
  change step (prefixCache 19 21110525) (coordinate 19)
    ⟨1, by decide⟩ = cache112
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache110).trans step_110_1

theorem actual_cache113 : prefixCache 20 84442102 = cache113 := by
  change step (prefixCache 19 21110525) (coordinate 19)
    ⟨2, by decide⟩ = cache113
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache110).trans step_110_2

theorem actual_cache114 : prefixCache 20 84442103 = cache114 := by
  change step (prefixCache 19 21110525) (coordinate 19)
    ⟨3, by decide⟩ = cache114
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache110).trans step_110_3

theorem actual_cache115 : prefixCache 19 21110526 = cache115 := by
  change step (prefixCache 18 5277631) (coordinate 18)
    ⟨2, by decide⟩ = cache115
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨2, by decide⟩)
    actual_cache108).trans step_108_2

theorem actual_cache116 : prefixCache 20 84442104 = cache116 := by
  change step (prefixCache 19 21110526) (coordinate 19)
    ⟨0, by decide⟩ = cache116
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache115).trans step_115_0

theorem actual_cache117 : prefixCache 20 84442105 = cache117 := by
  change step (prefixCache 19 21110526) (coordinate 19)
    ⟨1, by decide⟩ = cache117
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache115).trans step_115_1

theorem actual_cache118 : prefixCache 20 84442106 = cache118 := by
  change step (prefixCache 19 21110526) (coordinate 19)
    ⟨2, by decide⟩ = cache118
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache115).trans step_115_2

theorem actual_cache119 : prefixCache 20 84442107 = cache119 := by
  change step (prefixCache 19 21110526) (coordinate 19)
    ⟨3, by decide⟩ = cache119
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache115).trans step_115_3

theorem actual_cache120 : prefixCache 19 21110527 = cache120 := by
  change step (prefixCache 18 5277631) (coordinate 18)
    ⟨3, by decide⟩ = cache120
  exact (congrArg (fun cache => step cache (coordinate 18) ⟨3, by decide⟩)
    actual_cache108).trans step_108_3

theorem actual_cache121 : prefixCache 20 84442108 = cache121 := by
  change step (prefixCache 19 21110527) (coordinate 19)
    ⟨0, by decide⟩ = cache121
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨0, by decide⟩)
    actual_cache120).trans step_120_0

theorem actual_cache122 : prefixCache 20 84442109 = cache122 := by
  change step (prefixCache 19 21110527) (coordinate 19)
    ⟨1, by decide⟩ = cache122
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨1, by decide⟩)
    actual_cache120).trans step_120_1

theorem actual_cache123 : prefixCache 20 84442110 = cache123 := by
  change step (prefixCache 19 21110527) (coordinate 19)
    ⟨2, by decide⟩ = cache123
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨2, by decide⟩)
    actual_cache120).trans step_120_2

theorem actual_cache124 : prefixCache 20 84442111 = cache124 := by
  change step (prefixCache 19 21110527) (coordinate 19)
    ⟨3, by decide⟩ = cache124
  exact (congrArg (fun cache => step cache (coordinate 19) ⟨3, by decide⟩)
    actual_cache120).trans step_120_3

def children000 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨295, by decide⟩, ⟨1175, by decide⟩, ⟨15876, by decide⟩, ⟨15877, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt000 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 5 ⟨15878, by decide⟩) (coordinate 16) children000 = true := by
  decide +kernel

theorem node000 : EJMOriginalGlobalDAGData.nodes 5 ⟨15878, by decide⟩ =
    .split (coordinate 16) children000 :=
  checked_split_node _ _ _ split_receipt000

def cut001 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨24, by decide⟩ ⟨12, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt001 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 4 ⟨295, by decide⟩) cut001 = true := by
  decide +kernel

theorem node001 : EJMOriginalGlobalDAGData.nodes 4 ⟨295, by decide⟩ = .symmetry cut001 :=
  symmetry_of_checked _ _ symmetry_node_receipt001

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt001 :
    EJMGlobalScoreSymmetry.dominates cut001 (prefixPartial 17 1319404) = true := by
  decide +kernel

def children002 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨112, by decide⟩, ⟨112, by decide⟩, ⟨112, by decide⟩, ⟨455, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt002 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 4 ⟨1175, by decide⟩) (coordinate 17) children002 = true := by
  decide +kernel

theorem node002 : EJMOriginalGlobalDAGData.nodes 4 ⟨1175, by decide⟩ =
    .split (coordinate 17) children002 :=
  checked_split_node _ _ _ split_receipt002

def cut003 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨24, by decide⟩ ⟨13, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt003 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 3 ⟨112, by decide⟩) cut003 = true := by
  decide +kernel

theorem node003 : EJMOriginalGlobalDAGData.nodes 3 ⟨112, by decide⟩ = .symmetry cut003 :=
  symmetry_of_checked _ _ symmetry_node_receipt003

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt003 :
    EJMGlobalScoreSymmetry.dominates cut003 (prefixPartial 18 5277620) = true := by
  decide +kernel

def cut004 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨24, by decide⟩ ⟨13, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt004 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 3 ⟨112, by decide⟩) cut004 = true := by
  decide +kernel

theorem node004 : EJMOriginalGlobalDAGData.nodes 3 ⟨112, by decide⟩ = .symmetry cut004 :=
  symmetry_of_checked _ _ symmetry_node_receipt004

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt004 :
    EJMGlobalScoreSymmetry.dominates cut004 (prefixPartial 18 5277621) = true := by
  decide +kernel

def cut005 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨24, by decide⟩ ⟨13, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt005 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 3 ⟨112, by decide⟩) cut005 = true := by
  decide +kernel

theorem node005 : EJMOriginalGlobalDAGData.nodes 3 ⟨112, by decide⟩ = .symmetry cut005 :=
  symmetry_of_checked _ _ symmetry_node_receipt005

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt005 :
    EJMGlobalScoreSymmetry.dominates cut005 (prefixPartial 18 5277622) = true := by
  decide +kernel

def children006 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨57, by decide⟩, ⟨57, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt006 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 3 ⟨455, by decide⟩) (coordinate 18) children006 = true := by
  decide +kernel

theorem node006 : EJMOriginalGlobalDAGData.nodes 3 ⟨455, by decide⟩ =
    .split (coordinate 18) children006 :=
  checked_split_node _ _ _ split_receipt006

def cut007 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨24, by decide⟩ ⟨14, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt007 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 2 ⟨57, by decide⟩) cut007 = true := by
  decide +kernel

theorem node007 : EJMOriginalGlobalDAGData.nodes 2 ⟨57, by decide⟩ = .symmetry cut007 :=
  symmetry_of_checked _ _ symmetry_node_receipt007

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt007 :
    EJMGlobalScoreSymmetry.dominates cut007 (prefixPartial 19 21110492) = true := by
  decide +kernel

def cut008 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨24, by decide⟩ ⟨14, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt008 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 2 ⟨57, by decide⟩) cut008 = true := by
  decide +kernel

theorem node008 : EJMOriginalGlobalDAGData.nodes 2 ⟨57, by decide⟩ = .symmetry cut008 :=
  symmetry_of_checked _ _ symmetry_node_receipt008

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt008 :
    EJMGlobalScoreSymmetry.dominates cut008 (prefixPartial 19 21110493) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt009 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node009 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt009

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt009 : scale ≤ lower cache009 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt010 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node010 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt010

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt010 : scale ≤ lower cache010 := by
  decide +kernel

def children011 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨1045, by decide⟩, ⟨15875, by decide⟩, ⟨3029, by decide⟩, ⟨14936, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt011 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 4 ⟨15876, by decide⟩) (coordinate 17) children011 = true := by
  decide +kernel

theorem node011 : EJMOriginalGlobalDAGData.nodes 4 ⟨15876, by decide⟩ =
    .split (coordinate 17) children011 :=
  checked_split_node _ _ _ split_receipt011

def children012 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨0, by decide⟩, ⟨33, by decide⟩, ⟨0, by decide⟩, ⟨33, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt012 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 3 ⟨1045, by decide⟩) (coordinate 18) children012 = true := by
  decide +kernel

theorem node012 : EJMOriginalGlobalDAGData.nodes 3 ⟨1045, by decide⟩ =
    .split (coordinate 18) children012 :=
  checked_split_node _ _ _ split_receipt012

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt013 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node013 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt013

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt013 : scale ≤ lower cache013 := by
  decide +kernel

def children014 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt014 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨33, by decide⟩) (coordinate 19) children014 = true := by
  decide +kernel

theorem node014 : EJMOriginalGlobalDAGData.nodes 2 ⟨33, by decide⟩ =
    .split (coordinate 19) children014 :=
  checked_split_node _ _ _ split_receipt014

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt015 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node015 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt015

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt015 : scale ≤ lower cache015 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt016 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node016 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt016

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt016 : scale ≤ lower cache016 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt017 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node017 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt017

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt017 : scale ≤ lower cache017 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt018 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node018 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt018

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt018 : scale ≤ lower cache018 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt019 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node019 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt019

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt019 : scale ≤ lower cache019 := by
  decide +kernel

def children020 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt020 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨33, by decide⟩) (coordinate 19) children020 = true := by
  decide +kernel

theorem node020 : EJMOriginalGlobalDAGData.nodes 2 ⟨33, by decide⟩ =
    .split (coordinate 19) children020 :=
  checked_split_node _ _ _ split_receipt020

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt021 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node021 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt021

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt021 : scale ≤ lower cache021 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt022 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node022 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt022

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt022 : scale ≤ lower cache022 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt023 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node023 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt023

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt023 : scale ≤ lower cache023 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt024 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node024 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt024

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt024 : scale ≤ lower cache024 := by
  decide +kernel

def children025 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨0, by decide⟩, ⟨113, by decide⟩, ⟨0, by decide⟩, ⟨113, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt025 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 3 ⟨15875, by decide⟩) (coordinate 18) children025 = true := by
  decide +kernel

theorem node025 : EJMOriginalGlobalDAGData.nodes 3 ⟨15875, by decide⟩ =
    .split (coordinate 18) children025 :=
  checked_split_node _ _ _ split_receipt025

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt026 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node026 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt026

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt026 : scale ≤ lower cache026 := by
  decide +kernel

def children027 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt027 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨113, by decide⟩) (coordinate 19) children027 = true := by
  decide +kernel

theorem node027 : EJMOriginalGlobalDAGData.nodes 2 ⟨113, by decide⟩ =
    .split (coordinate 19) children027 :=
  checked_split_node _ _ _ split_receipt027

def cut028 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt028 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut028 = true := by
  decide +kernel

theorem node028 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut028 :=
  symmetry_of_checked _ _ symmetry_node_receipt028

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt028 :
    EJMGlobalScoreSymmetry.dominates cut028 (prefixPartial 20 84442004) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt029 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node029 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt029

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt029 : scale ≤ lower cache029 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt030 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node030 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt030

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt030 : scale ≤ lower cache030 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt031 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node031 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt031

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt031 : scale ≤ lower cache031 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt032 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node032 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt032

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt032 : scale ≤ lower cache032 := by
  decide +kernel

def children033 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt033 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨113, by decide⟩) (coordinate 19) children033 = true := by
  decide +kernel

theorem node033 : EJMOriginalGlobalDAGData.nodes 2 ⟨113, by decide⟩ =
    .split (coordinate 19) children033 :=
  checked_split_node _ _ _ split_receipt033

def cut034 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt034 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut034 = true := by
  decide +kernel

theorem node034 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut034 :=
  symmetry_of_checked _ _ symmetry_node_receipt034

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt034 :
    EJMGlobalScoreSymmetry.dominates cut034 (prefixPartial 20 84442012) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt035 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node035 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt035

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt035 : scale ≤ lower cache035 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt036 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node036 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt036

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt036 : scale ≤ lower cache036 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt037 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node037 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt037

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt037 : scale ≤ lower cache037 := by
  decide +kernel

def children038 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨0, by decide⟩, ⟨22, by decide⟩, ⟨0, by decide⟩, ⟨22, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt038 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 3 ⟨3029, by decide⟩) (coordinate 18) children038 = true := by
  decide +kernel

theorem node038 : EJMOriginalGlobalDAGData.nodes 3 ⟨3029, by decide⟩ =
    .split (coordinate 18) children038 :=
  checked_split_node _ _ _ split_receipt038

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt039 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node039 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt039

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt039 : scale ≤ lower cache039 := by
  decide +kernel

def children040 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨9, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt040 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨22, by decide⟩) (coordinate 19) children040 = true := by
  decide +kernel

theorem node040 : EJMOriginalGlobalDAGData.nodes 2 ⟨22, by decide⟩ =
    .split (coordinate 19) children040 :=
  checked_split_node _ _ _ split_receipt040

def cut041 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt041 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut041 = true := by
  decide +kernel

theorem node041 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut041 :=
  symmetry_of_checked _ _ symmetry_node_receipt041

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt041 :
    EJMGlobalScoreSymmetry.dominates cut041 (prefixPartial 20 84442020) = true := by
  decide +kernel

def cut042 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt042 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut042 = true := by
  decide +kernel

theorem node042 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut042 :=
  symmetry_of_checked _ _ symmetry_node_receipt042

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt042 :
    EJMGlobalScoreSymmetry.dominates cut042 (prefixPartial 20 84442021) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt043 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node043 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt043

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt043 : scale ≤ lower cache043 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt044 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node044 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt044

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt044 : scale ≤ lower cache044 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt045 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node045 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt045

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt045 : scale ≤ lower cache045 := by
  decide +kernel

def children046 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨9, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt046 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨22, by decide⟩) (coordinate 19) children046 = true := by
  decide +kernel

theorem node046 : EJMOriginalGlobalDAGData.nodes 2 ⟨22, by decide⟩ =
    .split (coordinate 19) children046 :=
  checked_split_node _ _ _ split_receipt046

def cut047 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt047 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut047 = true := by
  decide +kernel

theorem node047 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut047 :=
  symmetry_of_checked _ _ symmetry_node_receipt047

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt047 :
    EJMGlobalScoreSymmetry.dominates cut047 (prefixPartial 20 84442028) = true := by
  decide +kernel

def cut048 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt048 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut048 = true := by
  decide +kernel

theorem node048 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut048 :=
  symmetry_of_checked _ _ symmetry_node_receipt048

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt048 :
    EJMGlobalScoreSymmetry.dominates cut048 (prefixPartial 20 84442029) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt049 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node049 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt049

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt049 : scale ≤ lower cache049 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt050 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node050 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt050

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt050 : scale ≤ lower cache050 := by
  decide +kernel

def children051 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨0, by decide⟩, ⟨162, by decide⟩, ⟨162, by decide⟩, ⟨162, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt051 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 3 ⟨14936, by decide⟩) (coordinate 18) children051 = true := by
  decide +kernel

theorem node051 : EJMOriginalGlobalDAGData.nodes 3 ⟨14936, by decide⟩ =
    .split (coordinate 18) children051 :=
  checked_split_node _ _ _ split_receipt051

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt052 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node052 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt052

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt052 : scale ≤ lower cache052 := by
  decide +kernel

def children053 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨9, by decide⟩, ⟨9, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt053 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨162, by decide⟩) (coordinate 19) children053 = true := by
  decide +kernel

theorem node053 : EJMOriginalGlobalDAGData.nodes 2 ⟨162, by decide⟩ =
    .split (coordinate 19) children053 :=
  checked_split_node _ _ _ split_receipt053

def cut054 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt054 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut054 = true := by
  decide +kernel

theorem node054 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut054 :=
  symmetry_of_checked _ _ symmetry_node_receipt054

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt054 :
    EJMGlobalScoreSymmetry.dominates cut054 (prefixPartial 20 84442036) = true := by
  decide +kernel

def cut055 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt055 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut055 = true := by
  decide +kernel

theorem node055 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut055 :=
  symmetry_of_checked _ _ symmetry_node_receipt055

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt055 :
    EJMGlobalScoreSymmetry.dominates cut055 (prefixPartial 20 84442037) = true := by
  decide +kernel

def cut056 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt056 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut056 = true := by
  decide +kernel

theorem node056 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut056 :=
  symmetry_of_checked _ _ symmetry_node_receipt056

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt056 :
    EJMGlobalScoreSymmetry.dominates cut056 (prefixPartial 20 84442038) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt057 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node057 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt057

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt057 : scale ≤ lower cache057 := by
  decide +kernel

def children058 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨9, by decide⟩, ⟨9, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt058 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨162, by decide⟩) (coordinate 19) children058 = true := by
  decide +kernel

theorem node058 : EJMOriginalGlobalDAGData.nodes 2 ⟨162, by decide⟩ =
    .split (coordinate 19) children058 :=
  checked_split_node _ _ _ split_receipt058

def cut059 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt059 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut059 = true := by
  decide +kernel

theorem node059 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut059 :=
  symmetry_of_checked _ _ symmetry_node_receipt059

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt059 :
    EJMGlobalScoreSymmetry.dominates cut059 (prefixPartial 20 84442040) = true := by
  decide +kernel

def cut060 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt060 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut060 = true := by
  decide +kernel

theorem node060 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut060 :=
  symmetry_of_checked _ _ symmetry_node_receipt060

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt060 :
    EJMGlobalScoreSymmetry.dominates cut060 (prefixPartial 20 84442041) = true := by
  decide +kernel

def cut061 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt061 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut061 = true := by
  decide +kernel

theorem node061 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut061 :=
  symmetry_of_checked _ _ symmetry_node_receipt061

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt061 :
    EJMGlobalScoreSymmetry.dominates cut061 (prefixPartial 20 84442042) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt062 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node062 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt062

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt062 : scale ≤ lower cache062 := by
  decide +kernel

def children063 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨9, by decide⟩, ⟨9, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt063 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨162, by decide⟩) (coordinate 19) children063 = true := by
  decide +kernel

theorem node063 : EJMOriginalGlobalDAGData.nodes 2 ⟨162, by decide⟩ =
    .split (coordinate 19) children063 :=
  checked_split_node _ _ _ split_receipt063

def cut064 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt064 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut064 = true := by
  decide +kernel

theorem node064 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut064 :=
  symmetry_of_checked _ _ symmetry_node_receipt064

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt064 :
    EJMGlobalScoreSymmetry.dominates cut064 (prefixPartial 20 84442044) = true := by
  decide +kernel

def cut065 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt065 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut065 = true := by
  decide +kernel

theorem node065 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut065 :=
  symmetry_of_checked _ _ symmetry_node_receipt065

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt065 :
    EJMGlobalScoreSymmetry.dominates cut065 (prefixPartial 20 84442045) = true := by
  decide +kernel

def cut066 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt066 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut066 = true := by
  decide +kernel

theorem node066 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut066 :=
  symmetry_of_checked _ _ symmetry_node_receipt066

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt066 :
    EJMGlobalScoreSymmetry.dominates cut066 (prefixPartial 20 84442046) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt067 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node067 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt067

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt067 : scale ≤ lower cache067 := by
  decide +kernel

def children068 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨1045, by decide⟩, ⟨14311, by decide⟩, ⟨2836, by decide⟩, ⟨14936, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt068 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 4 ⟨15877, by decide⟩) (coordinate 17) children068 = true := by
  decide +kernel

theorem node068 : EJMOriginalGlobalDAGData.nodes 4 ⟨15877, by decide⟩ =
    .split (coordinate 17) children068 :=
  checked_split_node _ _ _ split_receipt068

def children069 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨0, by decide⟩, ⟨33, by decide⟩, ⟨0, by decide⟩, ⟨33, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt069 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 3 ⟨1045, by decide⟩) (coordinate 18) children069 = true := by
  decide +kernel

theorem node069 : EJMOriginalGlobalDAGData.nodes 3 ⟨1045, by decide⟩ =
    .split (coordinate 18) children069 :=
  checked_split_node _ _ _ split_receipt069

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt070 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node070 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt070

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt070 : scale ≤ lower cache070 := by
  decide +kernel

def children071 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt071 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨33, by decide⟩) (coordinate 19) children071 = true := by
  decide +kernel

theorem node071 : EJMOriginalGlobalDAGData.nodes 2 ⟨33, by decide⟩ =
    .split (coordinate 19) children071 :=
  checked_split_node _ _ _ split_receipt071

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt072 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node072 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt072

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt072 : scale ≤ lower cache072 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt073 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node073 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt073

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt073 : scale ≤ lower cache073 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt074 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node074 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt074

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt074 : scale ≤ lower cache074 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt075 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node075 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt075

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt075 : scale ≤ lower cache075 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt076 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node076 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt076

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt076 : scale ≤ lower cache076 := by
  decide +kernel

def children077 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt077 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨33, by decide⟩) (coordinate 19) children077 = true := by
  decide +kernel

theorem node077 : EJMOriginalGlobalDAGData.nodes 2 ⟨33, by decide⟩ =
    .split (coordinate 19) children077 :=
  checked_split_node _ _ _ split_receipt077

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt078 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node078 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt078

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt078 : scale ≤ lower cache078 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt079 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node079 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt079

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt079 : scale ≤ lower cache079 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt080 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node080 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt080

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt080 : scale ≤ lower cache080 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt081 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node081 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt081

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt081 : scale ≤ lower cache081 := by
  decide +kernel

def children082 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨0, by decide⟩, ⟨113, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt082 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 3 ⟨14311, by decide⟩) (coordinate 18) children082 = true := by
  decide +kernel

theorem node082 : EJMOriginalGlobalDAGData.nodes 3 ⟨14311, by decide⟩ =
    .split (coordinate 18) children082 :=
  checked_split_node _ _ _ split_receipt082

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt083 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node083 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt083

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt083 : scale ≤ lower cache083 := by
  decide +kernel

def children084 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt084 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨113, by decide⟩) (coordinate 19) children084 = true := by
  decide +kernel

theorem node084 : EJMOriginalGlobalDAGData.nodes 2 ⟨113, by decide⟩ =
    .split (coordinate 19) children084 :=
  checked_split_node _ _ _ split_receipt084

def cut085 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt085 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut085 = true := by
  decide +kernel

theorem node085 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut085 :=
  symmetry_of_checked _ _ symmetry_node_receipt085

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt085 :
    EJMGlobalScoreSymmetry.dominates cut085 (prefixPartial 20 84442068) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt086 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node086 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt086

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt086 : scale ≤ lower cache086 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt087 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node087 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt087

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt087 : scale ≤ lower cache087 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt088 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node088 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt088

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt088 : scale ≤ lower cache088 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt089 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node089 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt089

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt089 : scale ≤ lower cache089 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt090 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node090 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt090

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt090 : scale ≤ lower cache090 := by
  decide +kernel

def children091 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨0, by decide⟩, ⟨22, by decide⟩, ⟨22, by decide⟩, ⟨22, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt091 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 3 ⟨2836, by decide⟩) (coordinate 18) children091 = true := by
  decide +kernel

theorem node091 : EJMOriginalGlobalDAGData.nodes 3 ⟨2836, by decide⟩ =
    .split (coordinate 18) children091 :=
  checked_split_node _ _ _ split_receipt091

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt092 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node092 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt092

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt092 : scale ≤ lower cache092 := by
  decide +kernel

def children093 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨9, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt093 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨22, by decide⟩) (coordinate 19) children093 = true := by
  decide +kernel

theorem node093 : EJMOriginalGlobalDAGData.nodes 2 ⟨22, by decide⟩ =
    .split (coordinate 19) children093 :=
  checked_split_node _ _ _ split_receipt093

def cut094 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt094 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut094 = true := by
  decide +kernel

theorem node094 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut094 :=
  symmetry_of_checked _ _ symmetry_node_receipt094

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt094 :
    EJMGlobalScoreSymmetry.dominates cut094 (prefixPartial 20 84442084) = true := by
  decide +kernel

def cut095 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt095 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut095 = true := by
  decide +kernel

theorem node095 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut095 :=
  symmetry_of_checked _ _ symmetry_node_receipt095

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt095 :
    EJMGlobalScoreSymmetry.dominates cut095 (prefixPartial 20 84442085) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt096 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node096 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt096

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt096 : scale ≤ lower cache096 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt097 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node097 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt097

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt097 : scale ≤ lower cache097 := by
  decide +kernel

def children098 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨9, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt098 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨22, by decide⟩) (coordinate 19) children098 = true := by
  decide +kernel

theorem node098 : EJMOriginalGlobalDAGData.nodes 2 ⟨22, by decide⟩ =
    .split (coordinate 19) children098 :=
  checked_split_node _ _ _ split_receipt098

def cut099 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt099 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut099 = true := by
  decide +kernel

theorem node099 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut099 :=
  symmetry_of_checked _ _ symmetry_node_receipt099

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt099 :
    EJMGlobalScoreSymmetry.dominates cut099 (prefixPartial 20 84442088) = true := by
  decide +kernel

def cut100 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt100 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut100 = true := by
  decide +kernel

theorem node100 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut100 :=
  symmetry_of_checked _ _ symmetry_node_receipt100

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt100 :
    EJMGlobalScoreSymmetry.dominates cut100 (prefixPartial 20 84442089) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt101 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node101 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt101

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt101 : scale ≤ lower cache101 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt102 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node102 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt102

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt102 : scale ≤ lower cache102 := by
  decide +kernel

def children103 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨9, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt103 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨22, by decide⟩) (coordinate 19) children103 = true := by
  decide +kernel

theorem node103 : EJMOriginalGlobalDAGData.nodes 2 ⟨22, by decide⟩ =
    .split (coordinate 19) children103 :=
  checked_split_node _ _ _ split_receipt103

def cut104 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt104 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut104 = true := by
  decide +kernel

theorem node104 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut104 :=
  symmetry_of_checked _ _ symmetry_node_receipt104

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt104 :
    EJMGlobalScoreSymmetry.dominates cut104 (prefixPartial 20 84442092) = true := by
  decide +kernel

def cut105 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt105 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut105 = true := by
  decide +kernel

theorem node105 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut105 :=
  symmetry_of_checked _ _ symmetry_node_receipt105

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt105 :
    EJMGlobalScoreSymmetry.dominates cut105 (prefixPartial 20 84442093) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt106 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node106 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt106

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt106 : scale ≤ lower cache106 := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt107 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node107 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt107

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt107 : scale ≤ lower cache107 := by
  decide +kernel

def children108 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨0, by decide⟩, ⟨162, by decide⟩, ⟨162, by decide⟩, ⟨162, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt108 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 3 ⟨14936, by decide⟩) (coordinate 18) children108 = true := by
  decide +kernel

theorem node108 : EJMOriginalGlobalDAGData.nodes 3 ⟨14936, by decide⟩ =
    .split (coordinate 18) children108 :=
  checked_split_node _ _ _ split_receipt108

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt109 : isBound (EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node109 : EJMOriginalGlobalDAGData.nodes 2 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt109

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt109 : scale ≤ lower cache109 := by
  decide +kernel

def children110 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨9, by decide⟩, ⟨9, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt110 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨162, by decide⟩) (coordinate 19) children110 = true := by
  decide +kernel

theorem node110 : EJMOriginalGlobalDAGData.nodes 2 ⟨162, by decide⟩ =
    .split (coordinate 19) children110 :=
  checked_split_node _ _ _ split_receipt110

def cut111 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt111 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut111 = true := by
  decide +kernel

theorem node111 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut111 :=
  symmetry_of_checked _ _ symmetry_node_receipt111

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt111 :
    EJMGlobalScoreSymmetry.dominates cut111 (prefixPartial 20 84442100) = true := by
  decide +kernel

def cut112 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt112 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut112 = true := by
  decide +kernel

theorem node112 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut112 :=
  symmetry_of_checked _ _ symmetry_node_receipt112

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt112 :
    EJMGlobalScoreSymmetry.dominates cut112 (prefixPartial 20 84442101) = true := by
  decide +kernel

def cut113 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt113 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut113 = true := by
  decide +kernel

theorem node113 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut113 :=
  symmetry_of_checked _ _ symmetry_node_receipt113

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt113 :
    EJMGlobalScoreSymmetry.dominates cut113 (prefixPartial 20 84442102) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt114 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node114 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt114

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt114 : scale ≤ lower cache114 := by
  decide +kernel

def children115 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨9, by decide⟩, ⟨9, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt115 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨162, by decide⟩) (coordinate 19) children115 = true := by
  decide +kernel

theorem node115 : EJMOriginalGlobalDAGData.nodes 2 ⟨162, by decide⟩ =
    .split (coordinate 19) children115 :=
  checked_split_node _ _ _ split_receipt115

def cut116 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt116 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut116 = true := by
  decide +kernel

theorem node116 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut116 :=
  symmetry_of_checked _ _ symmetry_node_receipt116

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt116 :
    EJMGlobalScoreSymmetry.dominates cut116 (prefixPartial 20 84442104) = true := by
  decide +kernel

def cut117 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt117 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut117 = true := by
  decide +kernel

theorem node117 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut117 :=
  symmetry_of_checked _ _ symmetry_node_receipt117

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt117 :
    EJMGlobalScoreSymmetry.dominates cut117 (prefixPartial 20 84442105) = true := by
  decide +kernel

def cut118 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt118 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut118 = true := by
  decide +kernel

theorem node118 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut118 :=
  symmetry_of_checked _ _ symmetry_node_receipt118

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt118 :
    EJMGlobalScoreSymmetry.dominates cut118 (prefixPartial 20 84442106) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt119 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node119 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt119

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt119 : scale ≤ lower cache119 := by
  decide +kernel

def children120 : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  ![⟨9, by decide⟩, ⟨9, by decide⟩, ⟨9, by decide⟩, ⟨0, by decide⟩]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem split_receipt120 :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨162, by decide⟩) (coordinate 19) children120 = true := by
  decide +kernel

theorem node120 : EJMOriginalGlobalDAGData.nodes 2 ⟨162, by decide⟩ =
    .split (coordinate 19) children120 :=
  checked_split_node _ _ _ split_receipt120

def cut121 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt121 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut121 = true := by
  decide +kernel

theorem node121 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut121 :=
  symmetry_of_checked _ _ symmetry_node_receipt121

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt121 :
    EJMGlobalScoreSymmetry.dominates cut121 (prefixPartial 20 84442108) = true := by
  decide +kernel

def cut122 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt122 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut122 = true := by
  decide +kernel

theorem node122 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut122 :=
  symmetry_of_checked _ _ symmetry_node_receipt122

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt122 :
    EJMGlobalScoreSymmetry.dominates cut122 (prefixPartial 20 84442109) = true := by
  decide +kernel

def cut123 : EJMGlobalScoreSymmetry.Cut :=
  EJMGlobalScoreSymmetry.cutOfTag ⟨144, by decide⟩ ⟨17, by decide⟩

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem symmetry_node_receipt123 :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩) cut123 = true := by
  decide +kernel

theorem node123 : EJMOriginalGlobalDAGData.nodes 1 ⟨9, by decide⟩ = .symmetry cut123 :=
  symmetry_of_checked _ _ symmetry_node_receipt123

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem dominates_receipt123 :
    EJMGlobalScoreSymmetry.dominates cut123 (prefixPartial 20 84442110) = true := by
  decide +kernel

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem bound_node_receipt124 : isBound (EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩) = true := by
  decide +kernel

theorem node124 : EJMOriginalGlobalDAGData.nodes 1 ⟨0, by decide⟩ = .bound :=
  bound_of_isBound _ bound_node_receipt124

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 65536 in
set_option trace.profiler true in
theorem lower_receipt124 : scale ≤ lower cache124 := by
  decide +kernel

theorem accepted124 : Accepted 20 84442111 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442111 0 ⟨0, by decide⟩
    cache124 (by decide) actual_cache124 node124 lower_receipt124

theorem accepted123 : Accepted 20 84442110 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442110 0 ⟨9, by decide⟩
    cache123 cut123 (by decide) actual_cache123 node123
    dominates_receipt123

theorem accepted122 : Accepted 20 84442109 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442109 0 ⟨9, by decide⟩
    cache122 cut122 (by decide) actual_cache122 node122
    dominates_receipt122

theorem accepted121 : Accepted 20 84442108 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442108 0 ⟨9, by decide⟩
    cache121 cut121 (by decide) actual_cache121 node121
    dominates_receipt121

theorem accepted120 : Accepted 19 21110527 ⟨162, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110527 ⟨162, by decide⟩
    (by decide) children120 node120
  intro a
  fin_cases a
  · exact accepted121
  · exact accepted122
  · exact accepted123
  · exact accepted124

theorem accepted119 : Accepted 20 84442107 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442107 0 ⟨0, by decide⟩
    cache119 (by decide) actual_cache119 node119 lower_receipt119

theorem accepted118 : Accepted 20 84442106 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442106 0 ⟨9, by decide⟩
    cache118 cut118 (by decide) actual_cache118 node118
    dominates_receipt118

theorem accepted117 : Accepted 20 84442105 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442105 0 ⟨9, by decide⟩
    cache117 cut117 (by decide) actual_cache117 node117
    dominates_receipt117

theorem accepted116 : Accepted 20 84442104 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442104 0 ⟨9, by decide⟩
    cache116 cut116 (by decide) actual_cache116 node116
    dominates_receipt116

theorem accepted115 : Accepted 19 21110526 ⟨162, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110526 ⟨162, by decide⟩
    (by decide) children115 node115
  intro a
  fin_cases a
  · exact accepted116
  · exact accepted117
  · exact accepted118
  · exact accepted119

theorem accepted114 : Accepted 20 84442103 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442103 0 ⟨0, by decide⟩
    cache114 (by decide) actual_cache114 node114 lower_receipt114

theorem accepted113 : Accepted 20 84442102 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442102 0 ⟨9, by decide⟩
    cache113 cut113 (by decide) actual_cache113 node113
    dominates_receipt113

theorem accepted112 : Accepted 20 84442101 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442101 0 ⟨9, by decide⟩
    cache112 cut112 (by decide) actual_cache112 node112
    dominates_receipt112

theorem accepted111 : Accepted 20 84442100 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442100 0 ⟨9, by decide⟩
    cache111 cut111 (by decide) actual_cache111 node111
    dominates_receipt111

theorem accepted110 : Accepted 19 21110525 ⟨162, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110525 ⟨162, by decide⟩
    (by decide) children110 node110
  intro a
  fin_cases a
  · exact accepted111
  · exact accepted112
  · exact accepted113
  · exact accepted114

theorem accepted109 : Accepted 19 21110524 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110524 1 ⟨0, by decide⟩
    cache109 (by decide) actual_cache109 node109 lower_receipt109

theorem accepted108 : Accepted 18 5277631 ⟨14936, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 18 5277631 ⟨14936, by decide⟩
    (by decide) children108 node108
  intro a
  fin_cases a
  · exact accepted109
  · exact accepted110
  · exact accepted115
  · exact accepted120

theorem accepted107 : Accepted 20 84442095 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442095 0 ⟨0, by decide⟩
    cache107 (by decide) actual_cache107 node107 lower_receipt107

theorem accepted106 : Accepted 20 84442094 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442094 0 ⟨0, by decide⟩
    cache106 (by decide) actual_cache106 node106 lower_receipt106

theorem accepted105 : Accepted 20 84442093 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442093 0 ⟨9, by decide⟩
    cache105 cut105 (by decide) actual_cache105 node105
    dominates_receipt105

theorem accepted104 : Accepted 20 84442092 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442092 0 ⟨9, by decide⟩
    cache104 cut104 (by decide) actual_cache104 node104
    dominates_receipt104

theorem accepted103 : Accepted 19 21110523 ⟨22, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110523 ⟨22, by decide⟩
    (by decide) children103 node103
  intro a
  fin_cases a
  · exact accepted104
  · exact accepted105
  · exact accepted106
  · exact accepted107

theorem accepted102 : Accepted 20 84442091 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442091 0 ⟨0, by decide⟩
    cache102 (by decide) actual_cache102 node102 lower_receipt102

theorem accepted101 : Accepted 20 84442090 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442090 0 ⟨0, by decide⟩
    cache101 (by decide) actual_cache101 node101 lower_receipt101

theorem accepted100 : Accepted 20 84442089 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442089 0 ⟨9, by decide⟩
    cache100 cut100 (by decide) actual_cache100 node100
    dominates_receipt100

theorem accepted099 : Accepted 20 84442088 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442088 0 ⟨9, by decide⟩
    cache099 cut099 (by decide) actual_cache099 node099
    dominates_receipt099

theorem accepted098 : Accepted 19 21110522 ⟨22, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110522 ⟨22, by decide⟩
    (by decide) children098 node098
  intro a
  fin_cases a
  · exact accepted099
  · exact accepted100
  · exact accepted101
  · exact accepted102

theorem accepted097 : Accepted 20 84442087 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442087 0 ⟨0, by decide⟩
    cache097 (by decide) actual_cache097 node097 lower_receipt097

theorem accepted096 : Accepted 20 84442086 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442086 0 ⟨0, by decide⟩
    cache096 (by decide) actual_cache096 node096 lower_receipt096

theorem accepted095 : Accepted 20 84442085 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442085 0 ⟨9, by decide⟩
    cache095 cut095 (by decide) actual_cache095 node095
    dominates_receipt095

theorem accepted094 : Accepted 20 84442084 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442084 0 ⟨9, by decide⟩
    cache094 cut094 (by decide) actual_cache094 node094
    dominates_receipt094

theorem accepted093 : Accepted 19 21110521 ⟨22, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110521 ⟨22, by decide⟩
    (by decide) children093 node093
  intro a
  fin_cases a
  · exact accepted094
  · exact accepted095
  · exact accepted096
  · exact accepted097

theorem accepted092 : Accepted 19 21110520 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110520 1 ⟨0, by decide⟩
    cache092 (by decide) actual_cache092 node092 lower_receipt092

theorem accepted091 : Accepted 18 5277630 ⟨2836, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 18 5277630 ⟨2836, by decide⟩
    (by decide) children091 node091
  intro a
  fin_cases a
  · exact accepted092
  · exact accepted093
  · exact accepted098
  · exact accepted103

theorem accepted090 : Accepted 19 21110519 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110519 1 ⟨0, by decide⟩
    cache090 (by decide) actual_cache090 node090 lower_receipt090

theorem accepted089 : Accepted 19 21110518 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110518 1 ⟨0, by decide⟩
    cache089 (by decide) actual_cache089 node089 lower_receipt089

theorem accepted088 : Accepted 20 84442071 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442071 0 ⟨0, by decide⟩
    cache088 (by decide) actual_cache088 node088 lower_receipt088

theorem accepted087 : Accepted 20 84442070 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442070 0 ⟨0, by decide⟩
    cache087 (by decide) actual_cache087 node087 lower_receipt087

theorem accepted086 : Accepted 20 84442069 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442069 0 ⟨0, by decide⟩
    cache086 (by decide) actual_cache086 node086 lower_receipt086

theorem accepted085 : Accepted 20 84442068 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442068 0 ⟨9, by decide⟩
    cache085 cut085 (by decide) actual_cache085 node085
    dominates_receipt085

theorem accepted084 : Accepted 19 21110517 ⟨113, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110517 ⟨113, by decide⟩
    (by decide) children084 node084
  intro a
  fin_cases a
  · exact accepted085
  · exact accepted086
  · exact accepted087
  · exact accepted088

theorem accepted083 : Accepted 19 21110516 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110516 1 ⟨0, by decide⟩
    cache083 (by decide) actual_cache083 node083 lower_receipt083

theorem accepted082 : Accepted 18 5277629 ⟨14311, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 18 5277629 ⟨14311, by decide⟩
    (by decide) children082 node082
  intro a
  fin_cases a
  · exact accepted083
  · exact accepted084
  · exact accepted089
  · exact accepted090

theorem accepted081 : Accepted 20 84442063 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442063 0 ⟨0, by decide⟩
    cache081 (by decide) actual_cache081 node081 lower_receipt081

theorem accepted080 : Accepted 20 84442062 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442062 0 ⟨0, by decide⟩
    cache080 (by decide) actual_cache080 node080 lower_receipt080

theorem accepted079 : Accepted 20 84442061 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442061 0 ⟨0, by decide⟩
    cache079 (by decide) actual_cache079 node079 lower_receipt079

theorem accepted078 : Accepted 20 84442060 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442060 0 ⟨0, by decide⟩
    cache078 (by decide) actual_cache078 node078 lower_receipt078

theorem accepted077 : Accepted 19 21110515 ⟨33, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110515 ⟨33, by decide⟩
    (by decide) children077 node077
  intro a
  fin_cases a
  · exact accepted078
  · exact accepted079
  · exact accepted080
  · exact accepted081

theorem accepted076 : Accepted 19 21110514 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110514 1 ⟨0, by decide⟩
    cache076 (by decide) actual_cache076 node076 lower_receipt076

theorem accepted075 : Accepted 20 84442055 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442055 0 ⟨0, by decide⟩
    cache075 (by decide) actual_cache075 node075 lower_receipt075

theorem accepted074 : Accepted 20 84442054 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442054 0 ⟨0, by decide⟩
    cache074 (by decide) actual_cache074 node074 lower_receipt074

theorem accepted073 : Accepted 20 84442053 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442053 0 ⟨0, by decide⟩
    cache073 (by decide) actual_cache073 node073 lower_receipt073

theorem accepted072 : Accepted 20 84442052 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442052 0 ⟨0, by decide⟩
    cache072 (by decide) actual_cache072 node072 lower_receipt072

theorem accepted071 : Accepted 19 21110513 ⟨33, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110513 ⟨33, by decide⟩
    (by decide) children071 node071
  intro a
  fin_cases a
  · exact accepted072
  · exact accepted073
  · exact accepted074
  · exact accepted075

theorem accepted070 : Accepted 19 21110512 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110512 1 ⟨0, by decide⟩
    cache070 (by decide) actual_cache070 node070 lower_receipt070

theorem accepted069 : Accepted 18 5277628 ⟨1045, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 18 5277628 ⟨1045, by decide⟩
    (by decide) children069 node069
  intro a
  fin_cases a
  · exact accepted070
  · exact accepted071
  · exact accepted076
  · exact accepted077

theorem accepted068 : Accepted 17 1319407 ⟨15877, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 17 1319407 ⟨15877, by decide⟩
    (by decide) children068 node068
  intro a
  fin_cases a
  · exact accepted069
  · exact accepted082
  · exact accepted091
  · exact accepted108

theorem accepted067 : Accepted 20 84442047 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442047 0 ⟨0, by decide⟩
    cache067 (by decide) actual_cache067 node067 lower_receipt067

theorem accepted066 : Accepted 20 84442046 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442046 0 ⟨9, by decide⟩
    cache066 cut066 (by decide) actual_cache066 node066
    dominates_receipt066

theorem accepted065 : Accepted 20 84442045 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442045 0 ⟨9, by decide⟩
    cache065 cut065 (by decide) actual_cache065 node065
    dominates_receipt065

theorem accepted064 : Accepted 20 84442044 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442044 0 ⟨9, by decide⟩
    cache064 cut064 (by decide) actual_cache064 node064
    dominates_receipt064

theorem accepted063 : Accepted 19 21110511 ⟨162, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110511 ⟨162, by decide⟩
    (by decide) children063 node063
  intro a
  fin_cases a
  · exact accepted064
  · exact accepted065
  · exact accepted066
  · exact accepted067

theorem accepted062 : Accepted 20 84442043 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442043 0 ⟨0, by decide⟩
    cache062 (by decide) actual_cache062 node062 lower_receipt062

theorem accepted061 : Accepted 20 84442042 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442042 0 ⟨9, by decide⟩
    cache061 cut061 (by decide) actual_cache061 node061
    dominates_receipt061

theorem accepted060 : Accepted 20 84442041 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442041 0 ⟨9, by decide⟩
    cache060 cut060 (by decide) actual_cache060 node060
    dominates_receipt060

theorem accepted059 : Accepted 20 84442040 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442040 0 ⟨9, by decide⟩
    cache059 cut059 (by decide) actual_cache059 node059
    dominates_receipt059

theorem accepted058 : Accepted 19 21110510 ⟨162, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110510 ⟨162, by decide⟩
    (by decide) children058 node058
  intro a
  fin_cases a
  · exact accepted059
  · exact accepted060
  · exact accepted061
  · exact accepted062

theorem accepted057 : Accepted 20 84442039 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442039 0 ⟨0, by decide⟩
    cache057 (by decide) actual_cache057 node057 lower_receipt057

theorem accepted056 : Accepted 20 84442038 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442038 0 ⟨9, by decide⟩
    cache056 cut056 (by decide) actual_cache056 node056
    dominates_receipt056

theorem accepted055 : Accepted 20 84442037 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442037 0 ⟨9, by decide⟩
    cache055 cut055 (by decide) actual_cache055 node055
    dominates_receipt055

theorem accepted054 : Accepted 20 84442036 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442036 0 ⟨9, by decide⟩
    cache054 cut054 (by decide) actual_cache054 node054
    dominates_receipt054

theorem accepted053 : Accepted 19 21110509 ⟨162, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110509 ⟨162, by decide⟩
    (by decide) children053 node053
  intro a
  fin_cases a
  · exact accepted054
  · exact accepted055
  · exact accepted056
  · exact accepted057

theorem accepted052 : Accepted 19 21110508 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110508 1 ⟨0, by decide⟩
    cache052 (by decide) actual_cache052 node052 lower_receipt052

theorem accepted051 : Accepted 18 5277627 ⟨14936, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 18 5277627 ⟨14936, by decide⟩
    (by decide) children051 node051
  intro a
  fin_cases a
  · exact accepted052
  · exact accepted053
  · exact accepted058
  · exact accepted063

theorem accepted050 : Accepted 20 84442031 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442031 0 ⟨0, by decide⟩
    cache050 (by decide) actual_cache050 node050 lower_receipt050

theorem accepted049 : Accepted 20 84442030 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442030 0 ⟨0, by decide⟩
    cache049 (by decide) actual_cache049 node049 lower_receipt049

theorem accepted048 : Accepted 20 84442029 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442029 0 ⟨9, by decide⟩
    cache048 cut048 (by decide) actual_cache048 node048
    dominates_receipt048

theorem accepted047 : Accepted 20 84442028 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442028 0 ⟨9, by decide⟩
    cache047 cut047 (by decide) actual_cache047 node047
    dominates_receipt047

theorem accepted046 : Accepted 19 21110507 ⟨22, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110507 ⟨22, by decide⟩
    (by decide) children046 node046
  intro a
  fin_cases a
  · exact accepted047
  · exact accepted048
  · exact accepted049
  · exact accepted050

theorem accepted045 : Accepted 19 21110506 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110506 1 ⟨0, by decide⟩
    cache045 (by decide) actual_cache045 node045 lower_receipt045

theorem accepted044 : Accepted 20 84442023 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442023 0 ⟨0, by decide⟩
    cache044 (by decide) actual_cache044 node044 lower_receipt044

theorem accepted043 : Accepted 20 84442022 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442022 0 ⟨0, by decide⟩
    cache043 (by decide) actual_cache043 node043 lower_receipt043

theorem accepted042 : Accepted 20 84442021 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442021 0 ⟨9, by decide⟩
    cache042 cut042 (by decide) actual_cache042 node042
    dominates_receipt042

theorem accepted041 : Accepted 20 84442020 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442020 0 ⟨9, by decide⟩
    cache041 cut041 (by decide) actual_cache041 node041
    dominates_receipt041

theorem accepted040 : Accepted 19 21110505 ⟨22, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110505 ⟨22, by decide⟩
    (by decide) children040 node040
  intro a
  fin_cases a
  · exact accepted041
  · exact accepted042
  · exact accepted043
  · exact accepted044

theorem accepted039 : Accepted 19 21110504 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110504 1 ⟨0, by decide⟩
    cache039 (by decide) actual_cache039 node039 lower_receipt039

theorem accepted038 : Accepted 18 5277626 ⟨3029, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 18 5277626 ⟨3029, by decide⟩
    (by decide) children038 node038
  intro a
  fin_cases a
  · exact accepted039
  · exact accepted040
  · exact accepted045
  · exact accepted046

theorem accepted037 : Accepted 20 84442015 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442015 0 ⟨0, by decide⟩
    cache037 (by decide) actual_cache037 node037 lower_receipt037

theorem accepted036 : Accepted 20 84442014 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442014 0 ⟨0, by decide⟩
    cache036 (by decide) actual_cache036 node036 lower_receipt036

theorem accepted035 : Accepted 20 84442013 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442013 0 ⟨0, by decide⟩
    cache035 (by decide) actual_cache035 node035 lower_receipt035

theorem accepted034 : Accepted 20 84442012 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442012 0 ⟨9, by decide⟩
    cache034 cut034 (by decide) actual_cache034 node034
    dominates_receipt034

theorem accepted033 : Accepted 19 21110503 ⟨113, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110503 ⟨113, by decide⟩
    (by decide) children033 node033
  intro a
  fin_cases a
  · exact accepted034
  · exact accepted035
  · exact accepted036
  · exact accepted037

theorem accepted032 : Accepted 19 21110502 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110502 1 ⟨0, by decide⟩
    cache032 (by decide) actual_cache032 node032 lower_receipt032

theorem accepted031 : Accepted 20 84442007 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442007 0 ⟨0, by decide⟩
    cache031 (by decide) actual_cache031 node031 lower_receipt031

theorem accepted030 : Accepted 20 84442006 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442006 0 ⟨0, by decide⟩
    cache030 (by decide) actual_cache030 node030 lower_receipt030

theorem accepted029 : Accepted 20 84442005 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84442005 0 ⟨0, by decide⟩
    cache029 (by decide) actual_cache029 node029 lower_receipt029

theorem accepted028 : Accepted 20 84442004 ⟨9, by decide⟩ := by
  exact accepted_symmetry_of_cache 20 84442004 0 ⟨9, by decide⟩
    cache028 cut028 (by decide) actual_cache028 node028
    dominates_receipt028

theorem accepted027 : Accepted 19 21110501 ⟨113, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110501 ⟨113, by decide⟩
    (by decide) children027 node027
  intro a
  fin_cases a
  · exact accepted028
  · exact accepted029
  · exact accepted030
  · exact accepted031

theorem accepted026 : Accepted 19 21110500 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110500 1 ⟨0, by decide⟩
    cache026 (by decide) actual_cache026 node026 lower_receipt026

theorem accepted025 : Accepted 18 5277625 ⟨15875, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 18 5277625 ⟨15875, by decide⟩
    (by decide) children025 node025
  intro a
  fin_cases a
  · exact accepted026
  · exact accepted027
  · exact accepted032
  · exact accepted033

theorem accepted024 : Accepted 20 84441999 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84441999 0 ⟨0, by decide⟩
    cache024 (by decide) actual_cache024 node024 lower_receipt024

theorem accepted023 : Accepted 20 84441998 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84441998 0 ⟨0, by decide⟩
    cache023 (by decide) actual_cache023 node023 lower_receipt023

theorem accepted022 : Accepted 20 84441997 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84441997 0 ⟨0, by decide⟩
    cache022 (by decide) actual_cache022 node022 lower_receipt022

theorem accepted021 : Accepted 20 84441996 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84441996 0 ⟨0, by decide⟩
    cache021 (by decide) actual_cache021 node021 lower_receipt021

theorem accepted020 : Accepted 19 21110499 ⟨33, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110499 ⟨33, by decide⟩
    (by decide) children020 node020
  intro a
  fin_cases a
  · exact accepted021
  · exact accepted022
  · exact accepted023
  · exact accepted024

theorem accepted019 : Accepted 19 21110498 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110498 1 ⟨0, by decide⟩
    cache019 (by decide) actual_cache019 node019 lower_receipt019

theorem accepted018 : Accepted 20 84441991 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84441991 0 ⟨0, by decide⟩
    cache018 (by decide) actual_cache018 node018 lower_receipt018

theorem accepted017 : Accepted 20 84441990 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84441990 0 ⟨0, by decide⟩
    cache017 (by decide) actual_cache017 node017 lower_receipt017

theorem accepted016 : Accepted 20 84441989 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84441989 0 ⟨0, by decide⟩
    cache016 (by decide) actual_cache016 node016 lower_receipt016

theorem accepted015 : Accepted 20 84441988 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 20 84441988 0 ⟨0, by decide⟩
    cache015 (by decide) actual_cache015 node015 lower_receipt015

theorem accepted014 : Accepted 19 21110497 ⟨33, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 19 21110497 ⟨33, by decide⟩
    (by decide) children014 node014
  intro a
  fin_cases a
  · exact accepted015
  · exact accepted016
  · exact accepted017
  · exact accepted018

theorem accepted013 : Accepted 19 21110496 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110496 1 ⟨0, by decide⟩
    cache013 (by decide) actual_cache013 node013 lower_receipt013

theorem accepted012 : Accepted 18 5277624 ⟨1045, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 18 5277624 ⟨1045, by decide⟩
    (by decide) children012 node012
  intro a
  fin_cases a
  · exact accepted013
  · exact accepted014
  · exact accepted019
  · exact accepted020

theorem accepted011 : Accepted 17 1319406 ⟨15876, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 17 1319406 ⟨15876, by decide⟩
    (by decide) children011 node011
  intro a
  fin_cases a
  · exact accepted012
  · exact accepted025
  · exact accepted038
  · exact accepted051

theorem accepted010 : Accepted 19 21110495 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110495 1 ⟨0, by decide⟩
    cache010 (by decide) actual_cache010 node010 lower_receipt010

theorem accepted009 : Accepted 19 21110494 ⟨0, by decide⟩ := by
  exact accepted_bound_of_cache 19 21110494 1 ⟨0, by decide⟩
    cache009 (by decide) actual_cache009 node009 lower_receipt009

theorem accepted008 : Accepted 19 21110493 ⟨57, by decide⟩ := by
  exact accepted_symmetry_of_cache 19 21110493 1 ⟨57, by decide⟩
    cache008 cut008 (by decide) actual_cache008 node008
    dominates_receipt008

theorem accepted007 : Accepted 19 21110492 ⟨57, by decide⟩ := by
  exact accepted_symmetry_of_cache 19 21110492 1 ⟨57, by decide⟩
    cache007 cut007 (by decide) actual_cache007 node007
    dominates_receipt007

theorem accepted006 : Accepted 18 5277623 ⟨455, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 18 5277623 ⟨455, by decide⟩
    (by decide) children006 node006
  intro a
  fin_cases a
  · exact accepted007
  · exact accepted008
  · exact accepted009
  · exact accepted010

theorem accepted005 : Accepted 18 5277622 ⟨112, by decide⟩ := by
  exact accepted_symmetry_of_cache 18 5277622 2 ⟨112, by decide⟩
    cache005 cut005 (by decide) actual_cache005 node005
    dominates_receipt005

theorem accepted004 : Accepted 18 5277621 ⟨112, by decide⟩ := by
  exact accepted_symmetry_of_cache 18 5277621 2 ⟨112, by decide⟩
    cache004 cut004 (by decide) actual_cache004 node004
    dominates_receipt004

theorem accepted003 : Accepted 18 5277620 ⟨112, by decide⟩ := by
  exact accepted_symmetry_of_cache 18 5277620 2 ⟨112, by decide⟩
    cache003 cut003 (by decide) actual_cache003 node003
    dominates_receipt003

theorem accepted002 : Accepted 17 1319405 ⟨1175, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 17 1319405 ⟨1175, by decide⟩
    (by decide) children002 node002
  intro a
  fin_cases a
  · exact accepted003
  · exact accepted004
  · exact accepted005
  · exact accepted006

theorem accepted001 : Accepted 17 1319404 ⟨295, by decide⟩ := by
  exact accepted_symmetry_of_cache 17 1319404 3 ⟨295, by decide⟩
    cache001 cut001 (by decide) actual_cache001 node001
    dominates_receipt001

theorem accepted000 : Accepted 16 329851 ⟨15878, by decide⟩ := by
  apply EJMOriginalReplayAssembly.assemble 16 329851 ⟨15878, by decide⟩
    (by decide) children000 node000
  intro a
  fin_cases a
  · exact accepted001
  · exact accepted002
  · exact accepted011
  · exact accepted068

/-- Exactly the unchanged direct Pilot125 proposition. -/
theorem accepted_d16_p329851_i15878 : EJMOriginalReplayAssembly.Accepted 16 329851 ⟨15878, by decide⟩ :=
  accepted000

#print axioms step_eq_of_local_eq
#print axioms root_cache_receipt
#print axioms actual_cache124
#print axioms accepted_d16_p329851_i15878

end D5.S3.Quantum.Entanglement.EJM.Raw002Cap8.Raw293Sharing.SharedPilot125
