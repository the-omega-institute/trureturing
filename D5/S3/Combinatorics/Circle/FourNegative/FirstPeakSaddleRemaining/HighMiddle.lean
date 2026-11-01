/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HighMiddle
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:consumed-unbounded-polynomial-margins)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: High-middle exact margins, complete residue selection and native dyadic masks. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.Arithmetic

/-! SOURCE_ONLY_UNCOMPILED. Each sparse certificate is factored by Horner's
identity. `ring` must prove its equality to the original source margin;
`positivity` must prove its sign for unbounded nonnegative parameters.
No JSON, generator exit status or sampled parameter bound is a Lean premise. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining
open private rectangle scaled_margin grain_q high_margin scaled_to_rectangle
  ArithmeticSelection ArithmeticSelection.mk NativeChoice native_of_selection dyadic_time_cases from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining.Arithmetic
open private half_power from D5.S3.Combinatorics.Circle.FourNegative.Descending.Endpoint

set_option linter.unusedVariables false in
private theorem high_h_zero (X Y Z T : ℤ) (hX : 0≤X) (hY : 0≤Y) (hZ : 0≤Z) (hT : 0≤T) :
    ∀ i, 0≤high_margin (1+X) (1+Y) (4+Z) (4*(4+Z)+T) (0) i := by
  intro i
  fin_cases i
  · -- E_lower: 72 exact coefficients
    convert (show (0 : ℤ) ≤
      (((((((96) * Z + ((56) * T + (1472))) * Z + (((8) * T + (656)) * T + (8416))) * Z + (((64) * T
      + (2552)) * T + (21248))) * Z + (((128) * T + (3296)) * T + (19968))) * Y + (((((96) * Z +
      ((56) * T + (1472))) * Z + (((8) * T + (656)) * T + (8416))) * Z + (((64) * T + (2552)) * T +
      (21248))) * Z + (((128) * T + (3296)) * T + (19968)))) * X + ((((((192) * Z + ((112) * T +
      (2944))) * Z + (((16) * T + (1312)) * T + (16832))) * Z + (((128) * T + (5104)) * T +
      (42492))) * Z + (((256) * T + (6592)) * T + (39916))) * Y + (((((192) * Z + ((112) * T +
      (2952))) * Z + (((16) * T + (1314)) * T + (16946))) * Z + (((128) * T + (5124)) * T +
      (43026))) * Z + (((256) * T + (6640)) * T + (40744))))) * X + ((((((96) * Z + ((56) * T +
      (1472))) * Z + (((8) * T + (656)) * T + (8416))) * Z + (((64) * T + (2552)) * T + (21244))) *
      Z + (((128) * T + (3296)) * T + (19948))) * Y + (((((96) * Z + ((56) * T + (1480))) * Z +
      (((8) * T + (658)) * T + (8530))) * Z + (((64) * T + (2572)) * T + (21778))) * Z + (((128) * T
      + (3344)) * T + (20776)))) by positivity) using 1 <;>
      dsimp [high_margin,scaled_margin,grain_q] <;> ring
  · -- E_upper: 120 exact coefficients
    convert (show (0 : ℤ) ≤
      (((((((((384) * Z + ((224) * T + (7936))) * Z + (((32) * T + (3776)) * T + (65408))) * Z +
      (((416) * T + (23776)) * T + (268800))) * Z + (((1792) * T + (66304)) * T + (550912))) * Z +
      (((2560) * T + (69120)) * T + (450560))) * Y + ((((((384) * Z + ((224) * T + (7936))) * Z +
      (((32) * T + (3776)) * T + (65408))) * Z + (((416) * T + (23776)) * T + (268800))) * Z +
      (((1792) * T + (66304)) * T + (550912))) * Z + (((2560) * T + (69120)) * T + (450560)))) * X +
      (((((((1280) * Z + ((736) * T + (26400))) * Z + (((104) * T + (12360)) * T + (217344))) * Z +
      (((1344) * T + (77600)) * T + (893008))) * Z + (((5760) * T + (215960)) * T + (1831536))) * Z
      + (((8192) * T + (224864)) * T + (1500352))) * Y + ((((((1280) * Z + ((736) * T + (26400))) *
      Z + (((104) * T + (12360)) * T + (217344))) * Z + (((1344) * T + (77600)) * T + (893008))) * Z
      + (((5760) * T + (215960)) * T + (1831536))) * Z + (((8192) * T + (224864)) * T +
      (1500352))))) * X + (((((((1408) * Z + ((800) * T + (28992))) * Z + (((112) * T + (13392)) * T
      + (238464))) * Z + (((1440) * T + (83872)) * T + (979616))) * Z + (((6144) * T + (233008)) * T
      + (2010340))) * Z + (((8704) * T + (242368)) * T + (1649044))) * Y + ((((((1408) * Z + ((800)
      * T + (28992))) * Z + (((112) * T + (13392)) * T + (238464))) * Z + (((1440) * T + (83872)) *
      T + (979608))) * Z + (((6144) * T + (233006)) * T + (2010276))) * Z + (((8704) * T + (242360))
      * T + (1648916))))) * X + (((((((512) * Z + ((288) * T + (10528))) * Z + (((40) * T + (4808))
      * T + (86528))) * Z + (((512) * T + (30048)) * T + (355408))) * Z + (((2176) * T + (83352)) *
      T + (729716))) * Z + (((3072) * T + (86624)) * T + (599252))) * Y + ((((((512) * Z + ((288) *
      T + (10528))) * Z + (((40) * T + (4808)) * T + (86528))) * Z + (((512) * T + (30048)) * T +
      (355400))) * Z + (((2176) * T + (83350)) * T + (729652))) * Z + (((3072) * T + (86616)) * T +
      (599124)))) by positivity) using 1 <;>
      dsimp [high_margin,scaled_margin,grain_q] <;> ring
  · -- H_lower: 144 exact coefficients
    convert (show (0 : ℤ) ≤
      ((((((((((128) * Z + ((64) * T + (2880))) * Z + (((8) * T + (1168)) * T + (26624))) * Z +
      (((112) * T + (8288)) * T + (129088))) * Z + (((552) * T + (28304)) * T + (344832))) * Z +
      (((1088) * T + (45696)) * T + (478208))) * Z + (((640) * T + (26880)) * T + (266240))) * Y +
      (((((((128) * Z + ((64) * T + (2880))) * Z + (((8) * T + (1168)) * T + (26624))) * Z + (((112)
      * T + (8288)) * T + (129088))) * Z + (((552) * T + (28304)) * T + (344832))) * Z + (((1088) *
      T + (45696)) * T + (478208))) * Z + (((640) * T + (26880)) * T + (266240)))) * X +
      ((((((((384) * Z + ((192) * T + (8512))) * Z + (((24) * T + (3440)) * T + (77296))) * Z +
      (((328) * T + (23836)) * T + (366448))) * Z + (((1560) * T + (78700)) * T + (950024))) * Z +
      (((2880) * T + (120336)) * T + (1262408))) * Z + (((1408) * T + (63616)) * T + (657568))) * Y
      + (((((((384) * Z + ((192) * T + (8512))) * Z + (((24) * T + (3440)) * T + (77296))) * Z +
      (((328) * T + (23836)) * T + (366448))) * Z + (((1560) * T + (78700)) * T + (950024))) * Z +
      (((2880) * T + (120336)) * T + (1262408))) * Z + (((1408) * T + (63616)) * T + (657568))))) *
      X + ((((((((384) * Z + ((192) * T + (8384))) * Z + (((24) * T + (3376)) * T + (74720))) * Z +
      (((320) * T + (22808)) * T + (345632))) * Z + (((1464) * T + (72488)) * T + (865552))) * Z +
      (((2496) * T + (103584)) * T + (1090190))) * Z + (((896) * T + (46592)) * T + (516406))) * Y +
      (((((((384) * Z + ((192) * T + (8384))) * Z + (((24) * T + (3376)) * T + (74720))) * Z +
      (((320) * T + (22808)) * T + (345632))) * Z + (((1464) * T + (72488)) * T + (865560))) * Z +
      (((2496) * T + (103586)) * T + (1090252))) * Z + (((896) * T + (46600)) * T + (516524))))) * X
      + ((((((((128) * Z + ((64) * T + (2752))) * Z + (((8) * T + (1104)) * T + (24048))) * Z +
      (((104) * T + (7260)) * T + (108272))) * Z + (((456) * T + (22092)) * T + (260360))) * Z +
      (((704) * T + (28944)) * T + (305990))) * Z + (((128) * T + (9856)) * T + (125078))) * Y +
      (((((((128) * Z + ((64) * T + (2752))) * Z + (((8) * T + (1104)) * T + (24048))) * Z + (((104)
      * T + (7260)) * T + (108272))) * Z + (((456) * T + (22092)) * T + (260368))) * Z + (((704) * T
      + (28946)) * T + (306052))) * Z + (((128) * T + (9864)) * T + (125196)))) by positivity) using 1 <;>
      dsimp [high_margin,scaled_margin,grain_q] <;> ring
  · -- H_upper: 90 exact coefficients
    convert (show (0 : ℤ) ≤
      ((((((((128) * Z + ((64) * T + (2576))) * Z + (((8) * T + (1028)) * T + (20768))) * Z + (((96)
      * T + (6200)) * T + (83856))) * Z + (((384) * T + (16644)) * T + (169600))) * Z + (((512) * T
      + (16784)) * T + (137472))) * Y + ((((((128) * Z + ((64) * T + (2576))) * Z + (((8) * T +
      (1028)) * T + (20768))) * Z + (((96) * T + (6200)) * T + (83856))) * Z + (((384) * T +
      (16644)) * T + (169600))) * Z + (((512) * T + (16784)) * T + (137472)))) * X + (((((((256) * Z
      + ((128) * T + (5152))) * Z + (((16) * T + (2056)) * T + (41536))) * Z + (((192) * T +
      (12400)) * T + (167712))) * Z + (((768) * T + (33288)) * T + (339202))) * Z + (((1024) * T +
      (33568)) * T + (274954))) * Y + ((((((256) * Z + ((128) * T + (5152))) * Z + (((16) * T +
      (2056)) * T + (41536))) * Z + (((192) * T + (12400)) * T + (167704))) * Z + (((768) * T +
      (33286)) * T + (339136))) * Z + (((1024) * T + (33560)) * T + (274816))))) * X + (((((((128) *
      Z + ((64) * T + (2576))) * Z + (((8) * T + (1028)) * T + (20768))) * Z + (((96) * T + (6200))
      * T + (83856))) * Z + (((384) * T + (16644)) * T + (169602))) * Z + (((512) * T + (16784)) * T
      + (137482))) * Y + ((((((128) * Z + ((64) * T + (2576))) * Z + (((8) * T + (1028)) * T +
      (20768))) * Z + (((96) * T + (6200)) * T + (83848))) * Z + (((384) * T + (16642)) * T +
      (169536))) * Z + (((512) * T + (16776)) * T + (137344)))) by positivity) using 1 <;>
      dsimp [high_margin,scaled_margin,grain_q] <;> ring

set_option linter.unusedVariables false in
private theorem high_h_max (X Y Z T : ℤ) (hX : 0≤X) (hY : 0≤Y) (hZ : 0≤Z) (hT : 0≤T) :
    ∀ i, 0≤high_margin (1+X) (1+Y) (4+Z) (4*(4+Z)+T) (2*(4+Z)*(1+X)) i := by
  intro i
  fin_cases i
  · -- E_lower: 72 exact coefficients
    convert (show (0 : ℤ) ≤
      (((((((96) * Z + ((56) * T + (1408))) * Z + (((8) * T + (640)) * T + (7648))) * Z + (((64) * T
      + (2424)) * T + (18176))) * Z + (((128) * T + (3040)) * T + (15872))) * Y + (((((128) * Z +
      ((64) * T + (1960))) * Z + (((8) * T + (744)) * T + (11216))) * Z + (((64) * T + (2872)) * T +
      (28424))) * Z + (((128) * T + (3680)) * T + (26912)))) * X + ((((((192) * Z + ((112) * T +
      (2816))) * Z + (((16) * T + (1280)) * T + (15296))) * Z + (((128) * T + (4848)) * T +
      (36348))) * Z + (((256) * T + (6080)) * T + (31724))) * Y + (((((256) * Z + ((128) * T +
      (3928))) * Z + (((16) * T + (1490)) * T + (22546))) * Z + (((128) * T + (5764)) * T +
      (57374))) * Z + (((256) * T + (7408)) * T + (54616))))) * X + ((((((96) * Z + ((56) * T +
      (1408))) * Z + (((8) * T + (640)) * T + (7648))) * Z + (((64) * T + (2424)) * T + (18172))) *
      Z + (((128) * T + (3040)) * T + (15852))) * Y + (((((128) * Z + ((64) * T + (1968))) * Z +
      (((8) * T + (746)) * T + (11330))) * Z + (((64) * T + (2892)) * T + (28950))) * Z + (((128) *
      T + (3728)) * T + (27704)))) by positivity) using 1 <;>
      dsimp [high_margin,scaled_margin,grain_q] <;> ring
  · -- E_upper: 120 exact coefficients
    convert (show (0 : ℤ) ≤
      (((((((((384) * Z + ((224) * T + (7936))) * Z + (((32) * T + (3776)) * T + (65408))) * Z +
      (((416) * T + (23776)) * T + (268800))) * Z + (((1792) * T + (66304)) * T + (550912))) * Z +
      (((2560) * T + (69120)) * T + (450560))) * Y + ((((((384) * Z + ((224) * T + (7936))) * Z +
      (((32) * T + (3776)) * T + (65408))) * Z + (((416) * T + (23776)) * T + (268800))) * Z +
      (((1792) * T + (66304)) * T + (550912))) * Z + (((2560) * T + (69120)) * T + (450560)))) * X +
      (((((((1280) * Z + ((736) * T + (26400))) * Z + (((104) * T + (12360)) * T + (217408))) * Z +
      (((1344) * T + (77616)) * T + (893776))) * Z + (((5760) * T + (216088)) * T + (1834608))) * Z
      + (((8192) * T + (225120)) * T + (1504448))) * Y + ((((((1280) * Z + ((736) * T + (26368))) *
      Z + (((104) * T + (12352)) * T + (216856))) * Z + (((1344) * T + (77512)) * T + (890208))) * Z
      + (((5760) * T + (215640)) * T + (1824360))) * Z + (((8192) * T + (224480)) * T +
      (1493408))))) * X + (((((((1408) * Z + ((800) * T + (28992))) * Z + (((112) * T + (13392)) * T
      + (238592))) * Z + (((1440) * T + (83904)) * T + (981152))) * Z + (((6144) * T + (233264)) * T
      + (2016484))) * Z + (((8704) * T + (242880)) * T + (1657236))) * Y + ((((((1408) * Z + ((800)
      * T + (28928))) * Z + (((112) * T + (13376)) * T + (237488))) * Z + (((1440) * T + (83696)) *
      T + (974008))) * Z + (((6144) * T + (232366)) * T + (1995928))) * Z + (((8704) * T + (241592))
      * T + (1635044))))) * X + (((((((512) * Z + ((288) * T + (10528))) * Z + (((40) * T + (4808))
      * T + (86592))) * Z + (((512) * T + (30064)) * T + (356176))) * Z + (((2176) * T + (83480)) *
      T + (732788))) * Z + (((3072) * T + (86880)) * T + (603348))) * Y + ((((((512) * Z + ((288) *
      T + (10496))) * Z + (((40) * T + (4800)) * T + (86040))) * Z + (((512) * T + (29960)) * T +
      (352600))) * Z + (((2176) * T + (83030)) * T + (722480))) * Z + (((3072) * T + (86232)) * T +
      (592196)))) by positivity) using 1 <;>
      dsimp [high_margin,scaled_margin,grain_q] <;> ring
  · -- H_lower: 144 exact coefficients
    convert (show (0 : ℤ) ≤
      ((((((((((128) * Z + ((64) * T + (2880))) * Z + (((8) * T + (1168)) * T + (26624))) * Z +
      (((112) * T + (8288)) * T + (129088))) * Z + (((552) * T + (28304)) * T + (344832))) * Z +
      (((1088) * T + (45696)) * T + (478208))) * Z + (((640) * T + (26880)) * T + (266240))) * Y +
      (((((((128) * Z + ((64) * T + (2880))) * Z + (((8) * T + (1168)) * T + (26624))) * Z + (((112)
      * T + (8288)) * T + (129088))) * Z + (((552) * T + (28304)) * T + (344832))) * Z + (((1088) *
      T + (45696)) * T + (478208))) * Z + (((640) * T + (26880)) * T + (266240)))) * X +
      ((((((((384) * Z + ((192) * T + (8512))) * Z + (((24) * T + (3440)) * T + (77296))) * Z +
      (((328) * T + (23836)) * T + (366384))) * Z + (((1560) * T + (78684)) * T + (949256))) * Z +
      (((2880) * T + (120208)) * T + (1259336))) * Z + (((1408) * T + (63360)) * T + (653472))) * Y
      + (((((((384) * Z + ((192) * T + (8512))) * Z + (((24) * T + (3440)) * T + (77328))) * Z +
      (((328) * T + (23844)) * T + (366932))) * Z + (((1560) * T + (78788)) * T + (952768))) * Z +
      (((2880) * T + (120656)) * T + (1269324))) * Z + (((1408) * T + (64000)) * T + (664112))))) *
      X + ((((((((384) * Z + ((192) * T + (8384))) * Z + (((24) * T + (3376)) * T + (74720))) * Z +
      (((320) * T + (22808)) * T + (345504))) * Z + (((1464) * T + (72456)) * T + (864016))) * Z +
      (((2496) * T + (103328)) * T + (1084046))) * Z + (((896) * T + (46080)) * T + (508214))) * Y +
      (((((((384) * Z + ((192) * T + (8384))) * Z + (((24) * T + (3376)) * T + (74784))) * Z +
      (((320) * T + (22824)) * T + (346600))) * Z + (((1464) * T + (72664)) * T + (871048))) * Z +
      (((2496) * T + (104226)) * T + (1104080))) * Z + (((896) * T + (47368)) * T + (529596))))) * X
      + ((((((((128) * Z + ((64) * T + (2752))) * Z + (((8) * T + (1104)) * T + (24048))) * Z +
      (((104) * T + (7260)) * T + (108208))) * Z + (((456) * T + (22076)) * T + (259592))) * Z +
      (((704) * T + (28816)) * T + (302918))) * Z + (((128) * T + (9600)) * T + (120982))) * Y +
      (((((((128) * Z + ((64) * T + (2752))) * Z + (((8) * T + (1104)) * T + (24080))) * Z + (((104)
      * T + (7268)) * T + (108756))) * Z + (((456) * T + (22180)) * T + (263112))) * Z + (((704) * T
      + (29266)) * T + (312964))) * Z + (((128) * T + (10248)) * T + (131724)))) by positivity) using 1 <;>
      dsimp [high_margin,scaled_margin,grain_q] <;> ring
  · -- H_upper: 90 exact coefficients
    convert (show (0 : ℤ) ≤
      ((((((((128) * Z + ((64) * T + (2576))) * Z + (((8) * T + (1028)) * T + (20832))) * Z + (((96)
      * T + (6216)) * T + (84624))) * Z + (((384) * T + (16772)) * T + (172672))) * Z + (((512) * T
      + (17040)) * T + (141568))) * Y + ((((((128) * Z + ((64) * T + (2544))) * Z + (((8) * T +
      (1020)) * T + (20284))) * Z + (((96) * T + (6112)) * T + (81112))) * Z + (((384) * T +
      (16324)) * T + (162684))) * Z + (((512) * T + (16400)) * T + (130928)))) * X + (((((((256) * Z
      + ((128) * T + (5152))) * Z + (((16) * T + (2056)) * T + (41664))) * Z + (((192) * T +
      (12432)) * T + (169248))) * Z + (((768) * T + (33544)) * T + (345346))) * Z + (((1024) * T +
      (34080)) * T + (283146))) * Y + ((((((256) * Z + ((128) * T + (5088))) * Z + (((16) * T +
      (2040)) * T + (40568))) * Z + (((192) * T + (12224)) * T + (162216))) * Z + (((768) * T +
      (32646)) * T + (325308))) * Z + (((1024) * T + (32792)) * T + (261744))))) * X + (((((((128) *
      Z + ((64) * T + (2576))) * Z + (((8) * T + (1028)) * T + (20832))) * Z + (((96) * T + (6216))
      * T + (84624))) * Z + (((384) * T + (16772)) * T + (172674))) * Z + (((512) * T + (17040)) * T
      + (141578))) * Y + ((((((128) * Z + ((64) * T + (2544))) * Z + (((8) * T + (1020)) * T +
      (20284))) * Z + (((96) * T + (6112)) * T + (81104))) * Z + (((384) * T + (16322)) * T +
      (162624))) * Z + (((512) * T + (16392)) * T + (130816)))) by positivity) using 1 <;>
      dsimp [high_margin,scaled_margin,grain_q] <;> ring

set_option linter.unusedVariables false in
private theorem high_t_two_z (X Y Z T : ℤ) (hX : 0≤X) (hY : 0≤Y) (hZ : 0≤Z) (hT : 0≤T) :
    ∀ i, 0≤high_margin (1+X) (1+Y) (4+Z) (2*(4+Z)) (2*(1+X)) i := by
  intro i
  fin_cases i
  · -- E_lower: 30 exact coefficients
    convert (show (0 : ℤ) ≤
      (((((((16) * Z + (224)) * Z + (1104)) * Z + (2176)) * Z + (1280)) * Y + (((((16) * Z + (240))
      * Z + (1320)) * Z + (3152)) * Z + (2760))) * X + ((((((32) * Z + (448)) * Z + (2208)) * Z +
      (4348)) * Z + (2540)) * Y + (((((32) * Z + (484)) * Z + (2698)) * Z + (6578)) * Z + (5940))))
      * X + ((((((16) * Z + (224)) * Z + (1104)) * Z + (2172)) * Z + (1260)) * Y + (((((16) * Z +
      (244)) * Z + (1378)) * Z + (3426)) * Z + (3180))) by positivity) using 1 <;>
      dsimp [high_margin,scaled_margin,grain_q] <;> ring
  · -- E_upper: 48 exact coefficients
    convert (show (0 : ℤ) ≤
      (((((((((64) * Z + (1280)) * Z + (10176)) * Z + (40192)) * Z + (78848)) * Z + (61440)) * Y +
      ((((((64) * Z + (1280)) * Z + (10176)) * Z + (40192)) * Z + (78848)) * Z + (61440))) * X +
      (((((((224) * Z + (4496)) * Z + (35968)) * Z + (143424)) * Z + (285168)) * Z + (226240)) * Y +
      ((((((224) * Z + (4496)) * Z + (35952)) * Z + (143208)) * Z + (284192)) * Z + (224760)))) * X
      + (((((((256) * Z + (5152)) * Z + (41408)) * Z + (166272)) * Z + (333796)) * Z + (268180)) * Y
      + ((((((256) * Z + (5152)) * Z + (41376)) * Z + (165836)) * Z + (331812)) * Z + (265160)))) *
      X + (((((((96) * Z + (1936)) * Z + (15616)) * Z + (63040)) * Z + (127476)) * Z + (103380)) * Y
      + ((((((96) * Z + (1936)) * Z + (15600)) * Z + (62820)) * Z + (126468)) * Z + (101840))) by positivity) using 1 <;>
      dsimp [high_margin,scaled_margin,grain_q] <;> ring
  · -- H_lower: 56 exact coefficients
    convert (show (0 : ℤ) ≤
      ((((((((((32) * Z + (736)) * Z + (7008)) * Z + (35360)) * Z + (99712)) * Z + (148992)) * Z +
      (92160)) * Y + (((((((32) * Z + (736)) * Z + (7008)) * Z + (35360)) * Z + (99712)) * Z +
      (148992)) * Z + (92160))) * X + ((((((((96) * Z + (2176)) * Z + (20376)) * Z + (100792)) * Z +
      (277352)) * Z + (401608)) * Z + (238240)) * Y + (((((((96) * Z + (2176)) * Z + (20376)) * Z +
      (100808)) * Z + (277564)) * Z + (402544)) * Z + (239620)))) * X + ((((((((96) * Z + (2144)) *
      Z + (19728)) * Z + (95504)) * Z + (255568)) * Z + (356238)) * Z + (199990)) * Y + (((((((96) *
      Z + (2144)) * Z + (19728)) * Z + (95536)) * Z + (255996)) * Z + (358140)) * Z + (202800)))) *
      X + ((((((((32) * Z + (704)) * Z + (6360)) * Z + (30072)) * Z + (77928)) * Z + (103622)) * Z +
      (53910)) * Y + (((((((32) * Z + (704)) * Z + (6360)) * Z + (30088)) * Z + (78144)) * Z +
      (104588)) * Z + (55340))) by positivity) using 1 <;>
      dsimp [high_margin,scaled_margin,grain_q] <;> ring
  · -- H_upper: 36 exact coefficients
    convert (show (0 : ℤ) ≤
      ((((((((32) * Z + (648)) * Z + (5264)) * Z + (21480)) * Z + (44096)) * Z + (36480)) * Y +
      ((((((32) * Z + (648)) * Z + (5248)) * Z + (21268)) * Z + (43160)) * Z + (35100))) * X +
      (((((((64) * Z + (1296)) * Z + (10528)) * Z + (42960)) * Z + (88194)) * Z + (72970)) * Y +
      ((((((64) * Z + (1296)) * Z + (10496)) * Z + (42532)) * Z + (86288)) * Z + (70140)))) * X +
      (((((((32) * Z + (648)) * Z + (5264)) * Z + (21480)) * Z + (44098)) * Z + (36490)) * Y +
      ((((((32) * Z + (648)) * Z + (5248)) * Z + (21264)) * Z + (43128)) * Z + (35040))) by positivity) using 1 <;>
      dsimp [high_margin,scaled_margin,grain_q] <;> ring


private theorem high_interpolate (W J z t h : ℤ)
    (hW : 1≤W) (hJ : 1≤J) (hz : 4≤z) (ht : 4*z≤t)
    (hh : 0≤h ∧ h≤2*z*W) : ∀ i, 0≤high_margin W J z t h i := by
  have hW0 : 0<W := by omega
  have hz0 : 0<z := by omega
  intro i
  have h0 : 0≤high_margin W J z t 0 i := by
    convert high_h_zero (W-1) (J-1) (z-4) (t-4*z)
      (by omega) (by omega) (by omega) (by omega) i using 1 <;> congr 1 <;> ring
  have h1 : 0≤high_margin W J z t (2*z*W) i := by
    convert high_h_max (W-1) (J-1) (z-4) (t-4*z)
      (by omega) (by omega) (by omega) (by omega) i using 1 <;> congr 1 <;> ring
  have he : (2*z*W)*high_margin W J z t h i =
      (2*z*W-h)*high_margin W J z t 0 i+
      h*high_margin W J z t (2*z*W) i := by
    fin_cases i <;> dsimp [high_margin,scaled_margin,grain_q] <;> ring
  have hn := add_nonneg (mul_nonneg (sub_nonneg.mpr hh.2) h0) (mul_nonneg hh.1 h1)
  rw [←he] at hn
  exact nonneg_of_mul_nonneg_right hn (by positivity)

private theorem high_arithmetic (W J z t : ℤ)
    (hW : 1≤W) (hJ : 1≤J) (hz : 4≤z)
    (ht : t=2*z ∨ 4*z≤t) (heven : t%2=0) :
    Nonempty (ArithmeticSelection t z (z*W) J) := by
  have hW0 : 0<W := by omega
  have hJ0 : 0<J := by omega
  have hz0 : 0<z := by omega
  have hZW : 1≤z*W := by
    have hp := mul_nonneg (show 0≤z-1 by omega) (show 0≤W-1 by omega)
    nlinarith only [hp,hW,hz]
  rcases ht with ht|ht
  · subst t
    have hm : ∀ i, 0≤high_margin W J z (2*z) (2*W) i := by
      intro i
      convert high_t_two_z (W-1) (J-1) (z-4) 0
        (by omega) (by omega) (by omega) (by omega) i using 1 <;> congr 1 <;> ring
    refine ⟨ArithmeticSelection.mk J (2*W) 1 ⟨hJ,?_⟩
      ⟨by positivity,?_⟩ ⟨by norm_num,by omega⟩ ?_⟩
    · have hp := mul_nonneg (show 0≤4*z*W-1 by nlinarith) (show 0≤J by omega)
      nlinarith only [hp]
    · have hp := mul_pos (show 0<8*z*W by positivity) (show 0<z-1 by omega)
      nlinarith only [hp]
    · apply scaled_to_rectangle _ _ _ _ _ _ _ _ (2*W)
        (2*W*(2*z+z-1)+2*(2*W)-1) (2*W*(z-1)-1) 1
        (by positivity) (by omega) (by ring)
      simpa only [high_margin,mul_assoc] using hm
  · let m := t/2
    let k := (-m)%(z+1)
    let v := -((-m)/(z+1))
    have hm : t=2*m := by dsimp [m]; omega
    have hmz : 2*z≤m := by omega
    have hk0 : 0≤k := Int.emod_nonneg _ (by omega)
    have hk1 : k≤z := by
      have := Int.emod_lt_of_pos (-m) (show 0<z+1 by omega)
      dsimp [k]
      omega
    have hv : (z+1)*v=m+k := by
      have hh := Int.emod_add_ediv (-m) (z+1)
      dsimp [k,v]
      nlinarith only [hh]
    have hv0 : 0≤v := by
      by_contra hh
      have hp := mul_neg_of_pos_of_neg (show 0<z+1 by omega) (show v<0 by omega)
      nlinarith only [hp,hv,hmz,hk0,hz]
    have hv1 : 2*v≤t-2 := by
      by_contra hh
      have hvv : m≤v := by omega
      have hp := mul_le_mul_of_nonneg_left hvv (show 0≤z+1 by omega)
      have hprod := mul_nonneg (show 0≤z-1 by omega) (show 0≤m-2 by omega)
      nlinarith only [hp,hprod,hv,hk1,hmz,hz]
    have hhc : 2*z*(2*W*k)<2*(z*W)*t := by
      have hp := mul_pos (show 0<2*z*W by positivity) (show 0<t-2*k by omega)
      nlinarith only [hp]
    refine ⟨ArithmeticSelection.mk J (2*W*k) v ⟨hJ,?_⟩
      ⟨by positivity,hhc⟩ ⟨hv0,hv1⟩ ?_⟩
    · have hp := mul_nonneg (show 0≤4*z*W-1 by nlinarith) (show 0≤J by omega)
      nlinarith only [hp]
    · have hscaled := high_interpolate W J z t (2*W*k) hW hJ hz ht
        ⟨by positivity,by nlinarith only [mul_nonneg (show 0≤2*W by positivity) (show 0≤z-k by omega)]⟩
      apply scaled_to_rectangle _ _ _ _ _ _ _ _ (2*W)
        (2*W*(t+z-1)+2*(2*W*k)-1) (2*W*(z-1)-1) v
        (by positivity) (by omega)
      · have hp := congrArg (fun u : ℤ => 4*W*u) hv
        nlinarith only [hp,hm]
      · simpa only [high_margin,mul_assoc] using hscaled

/-- Consuming interface for ALL a>b>d>c>=2 with b>c+d. -/
private theorem high_middle_choice_exists (a b c d : ℕ)
    (hc : 2≤c) (hcd : c<d) (hdb : d<b) (hba : b<a) (hb : c+d<b) :
    Nonempty (NativeChoice a b c d) := by
  let W : ℤ := 2^(b-c-d-1)
  let J : ℤ := 2^(a-b-1)
  have hW : 1≤W := by dsimp [W]; exact one_le_pow₀ (by norm_num)
  have hJ : 1≤J := by dsimp [J]; exact one_le_pow₀ (by norm_num)
  have hz : (4:ℤ)≤2^c := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hc
  have hK : (2:ℤ)^(b-d-1)=(2:ℤ)^c*W := by
    dsimp [W]
    rw [←pow_add]
    congr 1
    omega
  have ht := dyadic_time_cases c d hcd
  have he : (2:ℤ)^d%2=0 := by
    rw [half_power d (by omega)]
    omega
  obtain ⟨sel⟩ := high_arithmetic W J (2^c) (2^d) hW hJ hz ht he
  refine ⟨native_of_selection a b c d hc hcd hdb hba ?_⟩
  simpa only [hK,J] using sel

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining
