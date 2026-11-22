/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/StrictBoundary
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:private-consumed-full-saddle-implementation)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Polynomial margins in the strict diagonal case. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal.Certificates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal

open private scaledMargin boundaryMargin rectangleMargin E0 H0 pivot grain reserve C A D L M Ln Mn
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal.Certificates

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
private theorem chart_strict_boundary (X Y Z T : ℤ)
    (hX : 0≤X) (hY : 0≤Y) (hZ : 0≤Z) (hT : 0≤T) :
    ∀ i : Fin 4, 0≤boundaryMargin (1+X) (1+Y) (2+Z) i := by
  intro i
  fin_cases i
  · -- E_lower: 100 exact sparse monomials
    convert (show (0 : ℤ)≤(((7058+Z*(11276+Z*(5920+Z*1024)))+Y*((29456+Z*(46092+Z*(23872+Z*4096)))+Y*((45952+Z*(70656+Z*(36128+Z*6144)))+Y*((31744+Z*(48128+Z*(24320+Z*4096)))+Y*(8192+Z*(12288+Z*(6144+Z*1024)))))))+X*(((27152+Z*(43916+Z*(23360+Z*4096)))+Y*((114704+Z*(181004+Z*(94592+Z*16384)))+Y*((180736+Z*(279424+Z*(143680+Z*24576)))+Y*((125952+Z*(191488+Z*(97024+Z*16384)))+Y*(32768+Z*(49152+Z*(24576+Z*4096)))))))+X*(((39296+Z*(64256+Z*(34592+Z*6144)))+Y*((167680+Z*(266752+Z*(140608+Z*24576)))+Y*((266624+Z*(414464+Z*(214304+Z*36864)))+Y*((187392+Z*(285696+Z*(145152+Z*24576)))+Y*(49152+Z*(73728+Z*(36864+Z*6144)))))))+X*(((25344+Z*(41856+Z*(22784+Z*4096)))+Y*((109056+Z*(174848+Z*(92928+Z*16384)))+Y*((174848+Z*(273280+Z*(142080+Z*24576)))+Y*((123904+Z*(189440+Z*(96512+Z*16384)))+Y*(32768+Z*(49152+Z*(24576+Z*4096)))))))+X*((6144+Z*(10240+Z*(5632+Z*1024)))+Y*((26624+Z*(43008+Z*(23040+Z*4096)))+Y*((43008+Z*(67584+Z*(35328+Z*6144)))+Y*((30720+Z*(47104+Z*(24064+Z*4096)))+Y*(8192+Z*(12288+Z*(6144+Z*1024))))))))))) by positivity) using 1 <;>
      dsimp [scaledMargin,boundaryMargin,rectangleMargin,E0,H0,pivot,grain,reserve,C,A,D,L,M,Ln,Mn] <;> ring
  · -- E_upper: 60 exact sparse monomials
    convert (show (0 : ℤ)≤(((3184+Z*(3128+Z*768))+Y*((9456+Z*(9336+Z*2304))+Y*((9344+Z*(9280+Z*2304))+Y*(3072+Z*(3072+Z*768)))))+X*(((13552+Z*(13432+Z*3328))+Y*((40432+Z*(40184+Z*9984))+Y*((40192+Z*(40064+Z*9984))+Y*(13312+Z*(13312+Z*3328)))))+X*(((21632+Z*(21568+Z*5376))+Y*((64768+Z*(64640+Z*16128))+Y*((64640+Z*(64576+Z*16128))+Y*(21504+Z*(21504+Z*5376)))))+X*(((15360+Z*(15360+Z*3840))+Y*((46080+Z*(46080+Z*11520))+Y*((46080+Z*(46080+Z*11520))+Y*(15360+Z*(15360+Z*3840)))))+X*((4096+Z*(4096+Z*1024))+Y*((12288+Z*(12288+Z*3072))+Y*((12288+Z*(12288+Z*3072))+Y*(4096+Z*(4096+Z*1024))))))))) by positivity) using 1 <;>
      dsimp [scaledMargin,boundaryMargin,rectangleMargin,E0,H0,pivot,grain,reserve,C,A,D,L,M,Ln,Mn] <;> ring
  · -- H_lower: 120 exact sparse monomials
    convert (show (0 : ℤ)≤(((6063+Z*(10200+Z*(5632+Z*1024)))+Y*((26448+Z*(42920+Z*(23040+Z*4096)))+Y*((42912+Z*(67536+Z*(35328+Z*6144)))+Y*((30720+Z*(47104+Z*(24064+Z*4096)))+Y*(8192+Z*(12288+Z*(6144+Z*1024)))))))+X*(((31568+Z*(52136+Z*(28416+Z*5120)))+Y*((135824+Z*(217928+Z*(115968+Z*20480)))+Y*((217920+Z*(340896+Z*(177408+Z*30720)))+Y*((154624+Z*(236544+Z*(120576+Z*20480)))+Y*(40960+Z*(61440+Z*(30720+Z*5120)))))))+X*(((66464+Z*(107472+Z*(57600+Z*10240)))+Y*((281408+Z*(445344+Z*(234240+Z*40960)))+Y*((445344+Z*(691152+Z*(357120+Z*61440)))+Y*((312320+Z*(476160+Z*(241920+Z*40960)))+Y*(81920+Z*(122880+Z*(61440+Z*10240)))))))+X*(((70656+Z*(111616+Z*(58624+Z*10240)))+Y*((293888+Z*(457728+Z*(237312+Z*40960)))+Y*((457728+Z*(703488+Z*(360192+Z*61440)))+Y*((316416+Z*(480256+Z*(242944+Z*40960)))+Y*(81920+Z*(122880+Z*(61440+Z*10240)))))))+X*(((37888+Z*(58368+Z*(29952+Z*5120)))+Y*((154624+Z*(236544+Z*(120576+Z*20480)))+Y*((236544+Z*(359424+Z*(182016+Z*30720)))+Y*((160768+Z*(242688+Z*(122112+Z*20480)))+Y*(40960+Z*(61440+Z*(30720+Z*5120)))))))+X*((8192+Z*(12288+Z*(6144+Z*1024)))+Y*((32768+Z*(49152+Z*(24576+Z*4096)))+Y*((49152+Z*(73728+Z*(36864+Z*6144)))+Y*((32768+Z*(49152+Z*(24576+Z*4096)))+Y*(8192+Z*(12288+Z*(6144+Z*1024)))))))))))) by positivity) using 1 <;>
      dsimp [scaledMargin,boundaryMargin,rectangleMargin,E0,H0,pivot,grain,reserve,C,A,D,L,M,Ln,Mn] <;> ring
  · -- H_upper: 54 exact sparse monomials
    convert (show (0 : ℤ)≤(((115+Z*56)+Y*((244+Z*120)+Y*(128+Z*64)))+X*(((1396+Z*(1208+Z*256))+Y*((3828+Z*(3448+Z*768))+Y*((3456+Z*(3264+Z*768))+Y*(1024+Z*(1024+Z*256)))))+X*(((3456+Z*(3264+Z*768))+Y*((9984+Z*(9600+Z*2304))+Y*((9600+Z*(9408+Z*2304))+Y*(3072+Z*(3072+Z*768)))))+X*(((3200+Z*(3136+Z*768))+Y*((9472+Z*(9344+Z*2304))+Y*((9344+Z*(9280+Z*2304))+Y*(3072+Z*(3072+Z*768)))))+X*((1024+Z*(1024+Z*256))+Y*((3072+Z*(3072+Z*768))+Y*((3072+Z*(3072+Z*768))+Y*(1024+Z*(1024+Z*256))))))))) by positivity) using 1 <;>
      dsimp [scaledMargin,boundaryMargin,rectangleMargin,E0,H0,pivot,grain,reserve,C,A,D,L,M,Ln,Mn] <;> ring

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal
