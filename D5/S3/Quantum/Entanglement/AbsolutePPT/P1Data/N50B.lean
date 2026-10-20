import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N50B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
def nodes : Array Node := #[
  ⟨![(0, (1/10)), (0, 5), (0, (1/4)), (0, 3)], .localRegion⟩,
  ⟨![(0, (1/10)), (0, (5/4)), ((1/4), (21/8)), (0, (3/2))], .bound .vertex 0 0 0⟩,
  ⟨![(0, (1/20)), ((5/4), (15/8)), ((1/4), (27/32)), (0, (3/8))], .bound .leftEnd 5 0 0⟩,
  ⟨![((1/20), (1/10)), ((5/4), (25/16)), ((1/4), (27/32)), (0, (3/8))], .bound .leftEnd 0 0 0⟩,
  ⟨![((1/20), (1/10)), ((25/16), (15/8)), ((1/4), (35/64)), (0, (3/8))], .bound .leftEnd 5 0 0⟩,
  ⟨![((1/20), (1/10)), ((25/16), (15/8)), ((35/64), (27/32)), (0, (3/16))], .bound .leftEnd 2 0 0⟩,
  ⟨![((1/20), (1/10)), ((25/16), (15/8)), ((35/64), (27/32)), ((3/16), (3/8))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/20), (1/10)), ((25/16), (15/8)), ((35/64), (27/32)), (0, (3/8))], .split 3 (3/16) 5 6⟩,
  ⟨![((1/20), (1/10)), ((25/16), (15/8)), ((1/4), (27/32)), (0, (3/8))], .split 2 (35/64) 4 7⟩,
  ⟨![((1/20), (1/10)), ((5/4), (15/8)), ((1/4), (27/32)), (0, (3/8))], .split 1 (25/16) 3 8⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((1/4), (27/32)), (0, (3/8))], .split 0 (1/20) 2 9⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((1/4), (27/32)), ((3/8), (3/4))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((1/4), (27/32)), (0, (3/4))], .split 3 (3/8) 10 11⟩,
  ⟨![(0, (1/20)), ((5/4), (25/16)), ((27/32), (23/16)), (0, (3/8))], .bound .leftEnd 0 0 0⟩,
  ⟨![(0, (1/20)), ((25/16), (15/8)), ((27/32), (23/16)), (0, (3/8))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/20)), ((5/4), (15/8)), ((27/32), (23/16)), (0, (3/8))], .split 1 (25/16) 13 14⟩,
  ⟨![((1/20), (1/10)), ((5/4), (15/8)), ((27/32), (23/16)), (0, (3/8))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((27/32), (23/16)), (0, (3/8))], .split 0 (1/20) 15 16⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((27/32), (23/16)), ((3/8), (3/4))], .bound .leftEnd 8 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((27/32), (23/16)), (0, (3/4))], .split 3 (3/8) 17 18⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((1/4), (23/16)), (0, (3/4))], .split 2 (27/32) 12 19⟩,
  ⟨![(0, (1/40)), ((15/8), (65/32)), ((1/4), (51/128)), (0, (3/32))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/40)), ((15/8), (65/32)), ((1/4), (51/128)), ((3/32), (3/16))], .bound .leftEnd 8 0 0⟩,
  ⟨![(0, (1/40)), ((15/8), (65/32)), ((1/4), (51/128)), (0, (3/16))], .split 3 (3/32) 21 22⟩,
  ⟨![(0, (1/40)), ((15/8), (65/32)), ((51/128), (35/64)), (0, (3/16))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/40)), ((15/8), (65/32)), ((1/4), (35/64)), (0, (3/16))], .split 2 (51/128) 23 24⟩,
  ⟨![(0, (1/40)), ((65/32), (35/16)), ((1/4), (51/128)), (0, (3/32))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/40)), ((65/32), (35/16)), ((1/4), (51/128)), ((3/32), (3/16))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/40)), ((65/32), (35/16)), ((1/4), (51/128)), (0, (3/16))], .split 3 (3/32) 26 27⟩,
  ⟨![(0, (1/40)), ((65/32), (35/16)), ((51/128), (35/64)), (0, (3/16))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/40)), ((65/32), (35/16)), ((1/4), (35/64)), (0, (3/16))], .split 2 (51/128) 28 29⟩,
  ⟨![(0, (1/40)), ((15/8), (35/16)), ((1/4), (35/64)), (0, (3/16))], .split 1 (65/32) 25 30⟩,
  ⟨![((1/40), (1/20)), ((15/8), (65/32)), ((1/4), (51/128)), (0, (3/32))], .bound .leftEnd 2 0 0⟩,
  ⟨![((1/40), (1/20)), ((15/8), (65/32)), ((1/4), (51/128)), ((3/32), (3/16))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/40), (1/20)), ((15/8), (65/32)), ((1/4), (51/128)), (0, (3/16))], .split 3 (3/32) 32 33⟩,
  ⟨![((1/40), (1/20)), ((15/8), (65/32)), ((51/128), (35/64)), (0, (3/16))], .bound .leftEnd 2 0 0⟩,
  ⟨![((1/40), (1/20)), ((15/8), (65/32)), ((1/4), (35/64)), (0, (3/16))], .split 2 (51/128) 34 35⟩,
  ⟨![((1/40), (1/20)), ((65/32), (35/16)), ((1/4), (35/64)), (0, (3/16))], .bound .leftEnd 2 0 0⟩,
  ⟨![((1/40), (1/20)), ((15/8), (35/16)), ((1/4), (35/64)), (0, (3/16))], .split 1 (65/32) 36 37⟩,
  ⟨![(0, (1/20)), ((15/8), (35/16)), ((1/4), (35/64)), (0, (3/16))], .split 0 (1/40) 31 38⟩,
  ⟨![(0, (1/20)), ((15/8), (35/16)), ((1/4), (35/64)), ((3/16), (3/8))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/20)), ((15/8), (35/16)), ((1/4), (35/64)), (0, (3/8))], .split 3 (3/16) 39 40⟩,
  ⟨![(0, (1/20)), ((15/8), (35/16)), ((35/64), (27/32)), (0, (3/16))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/20)), ((15/8), (35/16)), ((35/64), (27/32)), ((3/16), (3/8))], .bound .leftEnd 8 0 0⟩,
  ⟨![(0, (1/20)), ((15/8), (35/16)), ((35/64), (27/32)), (0, (3/8))], .split 3 (3/16) 42 43⟩,
  ⟨![(0, (1/20)), ((15/8), (35/16)), ((1/4), (27/32)), (0, (3/8))], .split 2 (35/64) 41 44⟩,
  ⟨![(0, (1/40)), ((35/16), (75/32)), ((1/4), (51/128)), (0, (3/32))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/40)), ((35/16), (75/32)), ((1/4), (51/128)), ((3/32), (3/16))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/40)), ((35/16), (75/32)), ((1/4), (51/128)), (0, (3/16))], .split 3 (3/32) 46 47⟩,
  ⟨![(0, (1/40)), ((35/16), (75/32)), ((51/128), (35/64)), (0, (3/16))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/40)), ((35/16), (75/32)), ((1/4), (35/64)), (0, (3/16))], .split 2 (51/128) 48 49⟩,
  ⟨![(0, (1/40)), ((75/32), (5/2)), ((1/4), (35/64)), (0, (3/16))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/40)), ((35/16), (5/2)), ((1/4), (35/64)), (0, (3/16))], .split 1 (75/32) 50 51⟩,
  ⟨![((1/40), (1/20)), ((35/16), (5/2)), ((1/4), (35/64)), (0, (3/16))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/20)), ((35/16), (5/2)), ((1/4), (35/64)), (0, (3/16))], .split 0 (1/40) 52 53⟩,
  ⟨![(0, (1/20)), ((35/16), (5/2)), ((1/4), (35/64)), ((3/16), (3/8))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/20)), ((35/16), (5/2)), ((1/4), (35/64)), (0, (3/8))], .split 3 (3/16) 54 55⟩,
  ⟨![(0, (1/20)), ((35/16), (5/2)), ((35/64), (27/32)), (0, (3/16))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/20)), ((35/16), (5/2)), ((35/64), (27/32)), ((3/16), (3/8))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/20)), ((35/16), (5/2)), ((35/64), (27/32)), (0, (3/8))], .split 3 (3/16) 57 58⟩,
  ⟨![(0, (1/20)), ((35/16), (5/2)), ((1/4), (27/32)), (0, (3/8))], .split 2 (35/64) 56 59⟩,
  ⟨![(0, (1/20)), ((15/8), (5/2)), ((1/4), (27/32)), (0, (3/8))], .split 1 (35/16) 45 60⟩,
  ⟨![((1/20), (1/10)), ((15/8), (35/16)), ((1/4), (35/64)), (0, (3/16))], .bound .leftEnd 2 0 0⟩,
  ⟨![((1/20), (1/10)), ((15/8), (35/16)), ((1/4), (35/64)), ((3/16), (3/8))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/20), (1/10)), ((15/8), (35/16)), ((1/4), (35/64)), (0, (3/8))], .split 3 (3/16) 62 63⟩,
  ⟨![((1/20), (1/10)), ((15/8), (35/16)), ((35/64), (27/32)), (0, (3/8))], .bound .leftEnd 2 0 0⟩,
  ⟨![((1/20), (1/10)), ((15/8), (35/16)), ((1/4), (27/32)), (0, (3/8))], .split 2 (35/64) 64 65⟩,
  ⟨![((1/20), (1/10)), ((35/16), (5/2)), ((1/4), (35/64)), (0, (3/8))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/20), (1/10)), ((35/16), (5/2)), ((35/64), (27/32)), (0, (3/8))], .bound .leftEnd 2 0 0⟩,
  ⟨![((1/20), (1/10)), ((35/16), (5/2)), ((1/4), (27/32)), (0, (3/8))], .split 2 (35/64) 67 68⟩,
  ⟨![((1/20), (1/10)), ((15/8), (5/2)), ((1/4), (27/32)), (0, (3/8))], .split 1 (35/16) 66 69⟩,
  ⟨![(0, (1/10)), ((15/8), (5/2)), ((1/4), (27/32)), (0, (3/8))], .split 0 (1/20) 61 70⟩,
  ⟨![(0, (1/10)), ((15/8), (5/2)), ((1/4), (27/32)), ((3/8), (3/4))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((15/8), (5/2)), ((1/4), (27/32)), (0, (3/4))], .split 3 (3/8) 71 72⟩,
  ⟨![(0, (1/10)), ((15/8), (5/2)), ((27/32), (23/16)), (0, (3/8))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/10)), ((15/8), (5/2)), ((27/32), (23/16)), ((3/8), (3/4))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((15/8), (5/2)), ((27/32), (23/16)), (0, (3/4))], .split 3 (3/8) 74 75⟩,
  ⟨![(0, (1/10)), ((15/8), (5/2)), ((1/4), (23/16)), (0, (3/4))], .split 2 (27/32) 73 76⟩,
  ⟨![(0, (1/10)), ((5/4), (5/2)), ((1/4), (23/16)), (0, (3/4))], .split 1 (15/8) 20 77⟩,
  ⟨![(0, (1/10)), ((5/4), (5/2)), ((1/4), (23/16)), ((3/4), (3/2))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (5/2)), ((1/4), (23/16)), (0, (3/2))], .split 3 (3/4) 78 79⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((23/16), (65/32)), (0, (3/8))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((23/16), (65/32)), ((3/8), (3/4))], .bound .leftEnd 8 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((23/16), (65/32)), (0, (3/4))], .split 3 (3/8) 81 82⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((65/32), (21/8)), (0, (3/4))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((23/16), (21/8)), (0, (3/4))], .split 2 (65/32) 83 84⟩,
  ⟨![(0, (1/10)), ((15/8), (5/2)), ((23/16), (21/8)), (0, (3/4))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (5/2)), ((23/16), (21/8)), (0, (3/4))], .split 1 (15/8) 85 86⟩,
  ⟨![(0, (1/10)), ((5/4), (5/2)), ((23/16), (21/8)), ((3/4), (3/2))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (5/2)), ((23/16), (21/8)), (0, (3/2))], .split 3 (3/4) 87 88⟩,
  ⟨![(0, (1/10)), ((5/4), (5/2)), ((1/4), (21/8)), (0, (3/2))], .split 2 (23/16) 80 89⟩,
  ⟨![(0, (1/10)), (0, (5/2)), ((1/4), (21/8)), (0, (3/2))], .split 1 (5/4) 1 90⟩,
  ⟨![(0, (1/10)), (0, (5/2)), ((1/4), (21/8)), ((3/2), 3)], .bound .vertex 1 0 0⟩,
  ⟨![(0, (1/10)), (0, (5/2)), ((1/4), (21/8)), (0, 3)], .split 3 (3/2) 91 92⟩,
  ⟨![(0, (1/10)), (0, (5/4)), ((21/8), 5), (0, (3/2))], .bound .vertex 4 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (5/2)), ((21/8), (61/16)), (0, (3/4))], .bound .vertex 2 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((21/8), (103/32)), ((3/4), (3/2))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((103/32), (61/16)), ((3/4), (3/2))], .bound .vertex 2 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (15/8)), ((21/8), (61/16)), ((3/4), (3/2))], .split 2 (103/32) 96 97⟩,
  ⟨![(0, (1/10)), ((15/8), (5/2)), ((21/8), (61/16)), ((3/4), (3/2))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((5/4), (5/2)), ((21/8), (61/16)), ((3/4), (3/2))], .split 1 (15/8) 98 99⟩,
  ⟨![(0, (1/10)), ((5/4), (5/2)), ((21/8), (61/16)), (0, (3/2))], .split 3 (3/4) 95 100⟩,
  ⟨![(0, (1/10)), ((5/4), (5/2)), ((61/16), 5), (0, (3/2))], .infeasible 0⟩,
  ⟨![(0, (1/10)), ((5/4), (5/2)), ((21/8), 5), (0, (3/2))], .split 2 (61/16) 101 102⟩,
  ⟨![(0, (1/10)), (0, (5/2)), ((21/8), 5), (0, (3/2))], .split 1 (5/4) 94 103⟩,
  ⟨![(0, (1/10)), (0, (5/4)), ((21/8), (61/16)), ((3/2), 3)], .bound .vertex 1 0 0⟩,
  ⟨![(0, (1/10)), (0, (5/4)), ((61/16), 5), ((3/2), (9/4))], .bound .vertex 1 0 0⟩,
  ⟨![(0, (1/10)), (0, (5/4)), ((61/16), 5), ((9/4), 3)], .bound .vertex 6 0 0⟩,
  ⟨![(0, (1/10)), (0, (5/4)), ((61/16), 5), ((3/2), 3)], .split 3 (9/4) 106 107⟩,
  ⟨![(0, (1/10)), (0, (5/4)), ((21/8), 5), ((3/2), 3)], .split 2 (61/16) 105 108⟩,
  ⟨![(0, (1/10)), ((5/4), (5/2)), ((21/8), 5), ((3/2), 3)], .bound .vertex 1 0 0⟩,
  ⟨![(0, (1/10)), (0, (5/2)), ((21/8), 5), ((3/2), 3)], .split 1 (5/4) 109 110⟩,
  ⟨![(0, (1/10)), (0, (5/2)), ((21/8), 5), (0, 3)], .split 3 (3/2) 104 111⟩,
  ⟨![(0, (1/10)), (0, (5/2)), ((1/4), 5), (0, 3)], .split 2 (21/8) 93 112⟩,
  ⟨![(0, (1/20)), ((5/2), (45/16)), ((1/4), (35/64)), (0, (3/16))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/20)), ((5/2), (45/16)), ((1/4), (35/64)), ((3/16), (3/8))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/20)), ((5/2), (45/16)), ((1/4), (35/64)), (0, (3/8))], .split 3 (3/16) 114 115⟩,
  ⟨![(0, (1/20)), ((5/2), (45/16)), ((35/64), (27/32)), (0, (3/8))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/20)), ((5/2), (45/16)), ((1/4), (27/32)), (0, (3/8))], .split 2 (35/64) 116 117⟩,
  ⟨![(0, (1/20)), ((45/16), (25/8)), ((1/4), (35/64)), (0, (3/8))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/20)), ((45/16), (25/8)), ((35/64), (27/32)), (0, (3/8))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/20)), ((45/16), (25/8)), ((1/4), (27/32)), (0, (3/8))], .split 2 (35/64) 119 120⟩,
  ⟨![(0, (1/20)), ((5/2), (25/8)), ((1/4), (27/32)), (0, (3/8))], .split 1 (45/16) 118 121⟩,
  ⟨![((1/20), (1/10)), ((5/2), (25/8)), ((1/4), (27/32)), (0, (3/8))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((5/2), (25/8)), ((1/4), (27/32)), (0, (3/8))], .split 0 (1/20) 122 123⟩,
  ⟨![(0, (1/10)), ((5/2), (25/8)), ((1/4), (27/32)), ((3/8), (3/4))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((5/2), (25/8)), ((1/4), (27/32)), (0, (3/4))], .split 3 (3/8) 124 125⟩,
  ⟨![(0, (1/10)), ((5/2), (25/8)), ((27/32), (23/16)), (0, (3/8))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/10)), ((5/2), (25/8)), ((27/32), (23/16)), ((3/8), (3/4))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((5/2), (25/8)), ((27/32), (23/16)), (0, (3/4))], .split 3 (3/8) 127 128⟩,
  ⟨![(0, (1/10)), ((5/2), (25/8)), ((1/4), (23/16)), (0, (3/4))], .split 2 (27/32) 126 129⟩,
  ⟨![(0, (1/10)), ((25/8), (15/4)), ((1/4), (27/32)), (0, (3/4))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((25/8), (15/4)), ((27/32), (23/16)), (0, (3/8))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/10)), ((25/8), (15/4)), ((27/32), (23/16)), ((3/8), (3/4))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((25/8), (15/4)), ((27/32), (23/16)), (0, (3/4))], .split 3 (3/8) 132 133⟩,
  ⟨![(0, (1/10)), ((25/8), (15/4)), ((1/4), (23/16)), (0, (3/4))], .split 2 (27/32) 131 134⟩,
  ⟨![(0, (1/10)), ((5/2), (15/4)), ((1/4), (23/16)), (0, (3/4))], .split 1 (25/8) 130 135⟩,
  ⟨![(0, (1/10)), ((5/2), (15/4)), ((1/4), (23/16)), ((3/4), (3/2))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((5/2), (15/4)), ((1/4), (23/16)), (0, (3/2))], .split 3 (3/4) 136 137⟩,
  ⟨![(0, (1/10)), ((5/2), (15/4)), ((23/16), (21/8)), (0, (3/4))], .bound .leftEnd 2 0 0⟩,
  ⟨![(0, (1/10)), ((5/2), (15/4)), ((23/16), (21/8)), ((3/4), (3/2))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((5/2), (15/4)), ((23/16), (21/8)), (0, (3/2))], .split 3 (3/4) 139 140⟩,
  ⟨![(0, (1/10)), ((5/2), (15/4)), ((1/4), (21/8)), (0, (3/2))], .split 2 (23/16) 138 141⟩,
  ⟨![(0, (1/10)), ((15/4), 5), ((1/4), (23/16)), (0, (3/2))], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((15/4), 5), ((23/16), (21/8)), (0, (3/2))], .infeasible 0⟩,
  ⟨![(0, (1/10)), ((15/4), 5), ((1/4), (21/8)), (0, (3/2))], .split 2 (23/16) 143 144⟩,
  ⟨![(0, (1/10)), ((5/2), 5), ((1/4), (21/8)), (0, (3/2))], .split 1 (15/4) 142 145⟩,
  ⟨![(0, (1/10)), ((5/2), 5), ((1/4), (21/8)), ((3/2), 3)], .bound .leftEnd 1 0 0⟩,
  ⟨![(0, (1/10)), ((5/2), 5), ((1/4), (21/8)), (0, 3)], .split 3 (3/2) 146 147⟩,
  ⟨![(0, (1/10)), ((5/2), 5), ((21/8), 5), (0, 3)], .infeasible 0⟩,
  ⟨![(0, (1/10)), ((5/2), 5), ((1/4), 5), (0, 3)], .split 2 (21/8) 148 149⟩,
  ⟨![(0, (1/10)), (0, 5), ((1/4), 5), (0, 3)], .split 1 (5/2) 113 150⟩,
  ⟨![(0, (1/10)), (0, 5), (0, 5), (0, 3)], .split 2 (1/4) 0 151⟩,
  ⟨![((1/10), (3/10)), (0, (5/4)), (0, (5/2)), (0, (3/2))], .bound .vertex 8 0 0⟩,
  ⟨![((1/10), (3/20)), ((5/4), (25/16)), (0, (5/8)), (0, (3/8))], .bound .leftEnd 0 0 0⟩,
  ⟨![((1/10), (3/20)), ((25/16), (15/8)), (0, (5/16)), (0, (3/8))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/10), (3/20)), ((25/16), (15/8)), ((5/16), (5/8)), (0, (3/16))], .bound .leftEnd 2 0 0⟩,
  ⟨![((1/10), (3/20)), ((25/16), (15/8)), ((5/16), (5/8)), ((3/16), (3/8))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/10), (3/20)), ((25/16), (15/8)), ((5/16), (5/8)), (0, (3/8))], .split 3 (3/16) 156 157⟩,
  ⟨![((1/10), (3/20)), ((25/16), (15/8)), (0, (5/8)), (0, (3/8))], .split 2 (5/16) 155 158⟩,
  ⟨![((1/10), (3/20)), ((5/4), (15/8)), (0, (5/8)), (0, (3/8))], .split 1 (25/16) 154 159⟩,
  ⟨![((3/20), (1/5)), ((5/4), (15/8)), (0, (5/8)), (0, (3/8))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/10), (1/5)), ((5/4), (15/8)), (0, (5/8)), (0, (3/8))], .split 0 (3/20) 160 161⟩,
  ⟨![((1/10), (1/5)), ((5/4), (15/8)), (0, (5/8)), ((3/8), (3/4))], .infeasible 16⟩,
  ⟨![((1/10), (1/5)), ((5/4), (15/8)), (0, (5/8)), (0, (3/4))], .split 3 (3/8) 162 163⟩,
  ⟨![((1/10), (1/5)), ((5/4), (15/8)), ((5/8), (5/4)), (0, (3/8))], .bound .leftEnd 2 0 0⟩,
  ⟨![((1/10), (1/5)), ((5/4), (15/8)), ((5/8), (5/4)), ((3/8), (3/4))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/10), (1/5)), ((5/4), (15/8)), ((5/8), (5/4)), (0, (3/4))], .split 3 (3/8) 165 166⟩,
  ⟨![((1/10), (1/5)), ((5/4), (15/8)), (0, (5/4)), (0, (3/4))], .split 2 (5/8) 164 167⟩,
  ⟨![((1/10), (1/5)), ((15/8), (5/2)), (0, (5/8)), (0, (3/4))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/10), (1/5)), ((15/8), (5/2)), ((5/8), (5/4)), (0, (3/8))], .bound .leftEnd 2 0 0⟩,
  ⟨![((1/10), (1/5)), ((15/8), (5/2)), ((5/8), (5/4)), ((3/8), (3/4))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/10), (1/5)), ((15/8), (5/2)), ((5/8), (5/4)), (0, (3/4))], .split 3 (3/8) 170 171⟩,
  ⟨![((1/10), (1/5)), ((15/8), (5/2)), (0, (5/4)), (0, (3/4))], .split 2 (5/8) 169 172⟩,
  ⟨![((1/10), (1/5)), ((5/4), (5/2)), (0, (5/4)), (0, (3/4))], .split 1 (15/8) 168 173⟩,
  ⟨![((1/5), (3/10)), ((5/4), (15/8)), (0, (5/8)), (0, (3/4))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/5), (3/10)), ((5/4), (15/8)), ((5/8), (5/4)), (0, (3/8))], .bound .vertex 2 0 0⟩,
  ⟨![((1/5), (3/10)), ((5/4), (15/8)), ((5/8), (5/4)), ((3/8), (3/4))], .bound .vertex 1 0 0⟩,
  ⟨![((1/5), (3/10)), ((5/4), (15/8)), ((5/8), (5/4)), (0, (3/4))], .split 3 (3/8) 176 177⟩,
  ⟨![((1/5), (3/10)), ((5/4), (15/8)), (0, (5/4)), (0, (3/4))], .split 2 (5/8) 175 178⟩,
  ⟨![((1/5), (3/10)), ((15/8), (5/2)), (0, (5/4)), (0, (3/4))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/5), (3/10)), ((5/4), (5/2)), (0, (5/4)), (0, (3/4))], .split 1 (15/8) 179 180⟩,
  ⟨![((1/10), (3/10)), ((5/4), (5/2)), (0, (5/4)), (0, (3/4))], .split 0 (1/5) 174 181⟩,
  ⟨![((1/10), (3/10)), ((5/4), (5/2)), (0, (5/4)), ((3/4), (3/2))], .infeasible 16⟩,
  ⟨![((1/10), (3/10)), ((5/4), (5/2)), (0, (5/4)), (0, (3/2))], .split 3 (3/4) 182 183⟩,
  ⟨![((1/10), (1/5)), ((5/4), (15/8)), ((5/4), (15/8)), (0, (3/8))], .bound .leftEnd 2 0 0⟩,
  ⟨![((1/10), (1/5)), ((5/4), (15/8)), ((5/4), (15/8)), ((3/8), (3/4))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/10), (1/5)), ((5/4), (15/8)), ((5/4), (15/8)), (0, (3/4))], .split 3 (3/8) 185 186⟩,
  ⟨![((1/10), (1/5)), ((5/4), (15/8)), ((15/8), (5/2)), (0, (3/4))], .bound .vertex 2 0 0⟩,
  ⟨![((1/10), (1/5)), ((5/4), (15/8)), ((5/4), (5/2)), (0, (3/4))], .split 2 (15/8) 187 188⟩,
  ⟨![((1/10), (1/5)), ((15/8), (5/2)), ((5/4), (5/2)), (0, (3/4))], .bound .leftEnd 2 0 0⟩,
  ⟨![((1/10), (1/5)), ((5/4), (5/2)), ((5/4), (5/2)), (0, (3/4))], .split 1 (15/8) 189 190⟩,
  ⟨![((1/5), (3/10)), ((5/4), (5/2)), ((5/4), (5/2)), (0, (3/4))], .bound .vertex 2 0 0⟩,
  ⟨![((1/10), (3/10)), ((5/4), (5/2)), ((5/4), (5/2)), (0, (3/4))], .split 0 (1/5) 191 192⟩,
  ⟨![((1/10), (3/10)), ((5/4), (5/2)), ((5/4), (5/2)), ((3/4), (3/2))], .bound .vertex 1 0 0⟩,
  ⟨![((1/10), (3/10)), ((5/4), (5/2)), ((5/4), (5/2)), (0, (3/2))], .split 3 (3/4) 193 194⟩,
  ⟨![((1/10), (3/10)), ((5/4), (5/2)), (0, (5/2)), (0, (3/2))], .split 2 (5/4) 184 195⟩,
  ⟨![((1/10), (3/10)), (0, (5/2)), (0, (5/2)), (0, (3/2))], .split 1 (5/4) 153 196⟩,
  ⟨![((3/10), (2/5)), (0, (5/8)), (0, (5/4)), (0, (3/4))], .bound .vertex 0 0 0⟩,
  ⟨![((3/10), (2/5)), ((5/8), (5/4)), (0, (5/4)), (0, (3/4))], .bound .vertex 1 0 0⟩,
  ⟨![((3/10), (2/5)), (0, (5/4)), (0, (5/4)), (0, (3/4))], .split 1 (5/8) 198 199⟩,
  ⟨![((2/5), (1/2)), (0, (5/8)), (0, (5/4)), (0, (3/4))], .bound .vertex 0 0 0⟩,
  ⟨![((2/5), (1/2)), ((5/8), (5/4)), (0, (5/4)), (0, (3/4))], .bound .vertex 1 0 0⟩,
  ⟨![((2/5), (1/2)), (0, (5/4)), (0, (5/4)), (0, (3/4))], .split 1 (5/8) 201 202⟩,
  ⟨![((3/10), (1/2)), (0, (5/4)), (0, (5/4)), (0, (3/4))], .split 0 (2/5) 200 203⟩,
  ⟨![((3/10), (1/2)), (0, (5/4)), (0, (5/4)), ((3/4), (3/2))], .infeasible 16⟩,
  ⟨![((3/10), (1/2)), (0, (5/4)), (0, (5/4)), (0, (3/2))], .split 3 (3/4) 204 205⟩,
  ⟨![((3/10), (1/2)), (0, (5/4)), ((5/4), (5/2)), (0, (3/4))], .bound .vertex 2 0 0⟩,
  ⟨![((3/10), (1/2)), (0, (5/4)), ((5/4), (5/2)), ((3/4), (3/2))], .bound .vertex 1 0 0⟩,
  ⟨![((3/10), (1/2)), (0, (5/4)), ((5/4), (5/2)), (0, (3/2))], .split 3 (3/4) 207 208⟩,
  ⟨![((3/10), (1/2)), (0, (5/4)), (0, (5/2)), (0, (3/2))], .split 2 (5/4) 206 209⟩,
  ⟨![((3/10), (1/2)), ((5/4), (5/2)), (0, (5/4)), (0, (3/2))], .bound .vertex 1 0 0⟩,
  ⟨![((3/10), (1/2)), ((5/4), (5/2)), ((5/4), (5/2)), (0, (3/2))], .infeasible 0⟩,
  ⟨![((3/10), (1/2)), ((5/4), (5/2)), (0, (5/2)), (0, (3/2))], .split 2 (5/4) 211 212⟩,
  ⟨![((3/10), (1/2)), (0, (5/2)), (0, (5/2)), (0, (3/2))], .split 1 (5/4) 210 213⟩,
  ⟨![((1/10), (1/2)), (0, (5/2)), (0, (5/2)), (0, (3/2))], .split 0 (3/10) 197 214⟩,
  ⟨![((1/10), (1/2)), (0, (5/2)), (0, (5/2)), ((3/2), 3)], .bound .vertex 1 0 0⟩,
  ⟨![((1/10), (1/2)), (0, (5/2)), (0, (5/2)), (0, 3)], .split 3 (3/2) 215 216⟩,
  ⟨![((1/10), (3/10)), (0, (5/4)), ((5/2), (15/4)), (0, (3/4))], .bound .vertex 2 0 0⟩,
  ⟨![((1/10), (1/5)), (0, (5/4)), ((5/2), (15/4)), ((3/4), (3/2))], .bound .vertex 8 0 0⟩,
  ⟨![((1/5), (3/10)), (0, (5/8)), ((5/2), (15/4)), ((3/4), (3/2))], .bound .vertex 0 0 0⟩,
  ⟨![((1/5), (3/10)), ((5/8), (5/4)), ((5/2), (15/4)), ((3/4), (3/2))], .infeasible 0⟩,
  ⟨![((1/5), (3/10)), (0, (5/4)), ((5/2), (15/4)), ((3/4), (3/2))], .split 1 (5/8) 220 221⟩,
  ⟨![((1/10), (3/10)), (0, (5/4)), ((5/2), (15/4)), ((3/4), (3/2))], .split 0 (1/5) 219 222⟩,
  ⟨![((1/10), (3/10)), (0, (5/4)), ((5/2), (15/4)), (0, (3/2))], .split 3 (3/4) 218 223⟩,
  ⟨![((1/10), (3/10)), (0, (5/4)), ((15/4), 5), (0, (3/2))], .bound .vertex 2 0 0⟩,
  ⟨![((1/10), (3/10)), (0, (5/4)), ((5/2), 5), (0, (3/2))], .split 2 (15/4) 224 225⟩,
  ⟨![((1/10), (3/10)), ((5/4), (5/2)), ((5/2), (15/4)), (0, (3/2))], .bound .vertex 3 0 0⟩,
  ⟨![((1/10), (3/10)), ((5/4), (5/2)), ((15/4), 5), (0, (3/2))], .infeasible 0⟩,
  ⟨![((1/10), (3/10)), ((5/4), (5/2)), ((5/2), 5), (0, (3/2))], .split 2 (15/4) 227 228⟩,
  ⟨![((1/10), (3/10)), (0, (5/2)), ((5/2), 5), (0, (3/2))], .split 1 (5/4) 226 229⟩,
  ⟨![((3/10), (1/2)), (0, (5/2)), ((5/2), 5), (0, (3/2))], .infeasible 0⟩,
  ⟨![((1/10), (1/2)), (0, (5/2)), ((5/2), 5), (0, (3/2))], .split 0 (3/10) 230 231⟩,
  ⟨![((1/10), (3/10)), (0, (5/4)), ((5/2), (15/4)), ((3/2), (9/4))], .bound .vertex 1 0 0⟩,
  ⟨![((1/10), (1/5)), (0, (5/8)), ((5/2), (25/8)), ((9/4), 3)], .infeasible 16⟩,
  ⟨![((1/10), (1/5)), (0, (5/8)), ((25/8), (15/4)), ((9/4), (21/8))], .bound .vertex 1 0 0⟩,
  ⟨![((1/10), (1/5)), (0, (5/8)), ((25/8), (15/4)), ((21/8), 3)], .infeasible 16⟩,
  ⟨![((1/10), (1/5)), (0, (5/8)), ((25/8), (15/4)), ((9/4), 3)], .split 3 (21/8) 235 236⟩,
  ⟨![((1/10), (1/5)), (0, (5/8)), ((5/2), (15/4)), ((9/4), 3)], .split 2 (25/8) 234 237⟩,
  ⟨![((1/10), (1/5)), ((5/8), (5/4)), ((5/2), (15/4)), ((9/4), 3)], .bound .vertex 1 0 0⟩,
  ⟨![((1/10), (1/5)), (0, (5/4)), ((5/2), (15/4)), ((9/4), 3)], .split 1 (5/8) 238 239⟩,
  ⟨![((1/5), (3/10)), (0, (5/4)), ((5/2), (15/4)), ((9/4), 3)], .bound .vertex 3 0 0⟩,
  ⟨![((1/10), (3/10)), (0, (5/4)), ((5/2), (15/4)), ((9/4), 3)], .split 0 (1/5) 240 241⟩,
  ⟨![((1/10), (3/10)), (0, (5/4)), ((5/2), (15/4)), ((3/2), 3)], .split 3 (9/4) 233 242⟩,
  ⟨![((1/10), (3/10)), (0, (5/4)), ((15/4), 5), ((3/2), 3)], .bound .vertex 3 0 0⟩,
  ⟨![((1/10), (3/10)), (0, (5/4)), ((5/2), 5), ((3/2), 3)], .split 2 (15/4) 243 244⟩,
  ⟨![((1/10), (3/10)), ((5/4), (5/2)), ((5/2), 5), ((3/2), 3)], .bound .vertex 3 0 0⟩,
  ⟨![((1/10), (3/10)), (0, (5/2)), ((5/2), 5), ((3/2), 3)], .split 1 (5/4) 245 246⟩,
  ⟨![((3/10), (1/2)), (0, (5/2)), ((5/2), 5), ((3/2), 3)], .infeasible 0⟩,
  ⟨![((1/10), (1/2)), (0, (5/2)), ((5/2), 5), ((3/2), 3)], .split 0 (3/10) 247 248⟩,
  ⟨![((1/10), (1/2)), (0, (5/2)), ((5/2), 5), (0, 3)], .split 3 (3/2) 232 249⟩,
  ⟨![((1/10), (1/2)), (0, (5/2)), (0, 5), (0, 3)], .split 2 (5/2) 217 250⟩,
  ⟨![((1/10), (3/10)), ((5/2), (15/4)), (0, (5/4)), (0, (3/2))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/10), (3/10)), ((5/2), (15/4)), ((5/4), (5/2)), (0, (3/2))], .bound .vertex 3 0 0⟩,
  ⟨![((1/10), (3/10)), ((5/2), (15/4)), (0, (5/2)), (0, (3/2))], .split 2 (5/4) 252 253⟩,
  ⟨![((1/10), (3/10)), ((15/4), 5), (0, (5/4)), (0, (3/2))], .bound .leftEnd 1 0 0⟩,
  ⟨![((1/10), (3/10)), ((15/4), 5), ((5/4), (5/2)), (0, (3/2))], .infeasible 0⟩,
  ⟨![((1/10), (3/10)), ((15/4), 5), (0, (5/2)), (0, (3/2))], .split 2 (5/4) 255 256⟩,
  ⟨![((1/10), (3/10)), ((5/2), 5), (0, (5/2)), (0, (3/2))], .split 1 (15/4) 254 257⟩,
  ⟨![((3/10), (1/2)), ((5/2), 5), (0, (5/2)), (0, (3/2))], .infeasible 0⟩,
  ⟨![((1/10), (1/2)), ((5/2), 5), (0, (5/2)), (0, (3/2))], .split 0 (3/10) 258 259⟩,
  ⟨![((1/10), (1/2)), ((5/2), 5), (0, (5/2)), ((3/2), 3)], .infeasible 16⟩,
  ⟨![((1/10), (1/2)), ((5/2), 5), (0, (5/2)), (0, 3)], .split 3 (3/2) 260 261⟩,
  ⟨![((1/10), (1/2)), ((5/2), 5), ((5/2), 5), (0, 3)], .infeasible 0⟩,
  ⟨![((1/10), (1/2)), ((5/2), 5), (0, 5), (0, 3)], .split 2 (5/2) 262 263⟩,
  ⟨![((1/10), (1/2)), (0, 5), (0, 5), (0, 3)], .split 1 (5/2) 251 264⟩,
  ⟨![(0, (1/2)), (0, 5), (0, 5), (0, 3)], .split 0 (1/10) 152 265⟩
]
private def starts : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 11, 2, 13, 14, 13, 16, 13, 18, 13, 2, 21, 22, 21, 24, 21, 26, 27, 26, 29, 26, 21, 32, 33, 32, 35, 32, 37, 32, 21, 40, 21, 42, 43, 42, 21, 46, 47, 46, 49, 46, 51, 46, 53, 46, 55, 46, 57, 58, 57, 46, 21, 62, 63, 62, 65, 62, 67, 68, 67, 62, 21, 72, 21, 74, 75, 74, 21, 2, 79, 2, 81, 82, 81, 84, 81, 86, 81, 88, 81, 2, 1, 92, 1, 94, 95, 96, 97, 96, 99, 96, 95, 102, 95, 94, 105, 106, 107, 106, 105, 110, 105, 94, 1, 114, 115, 114, 117, 114, 119, 120, 119, 114, 123, 114, 125, 114, 127, 128, 127, 114, 131, 132, 133, 132, 131, 114, 137, 114, 139, 140, 139, 114, 143, 144, 143, 114, 147, 114, 149, 114, 1, 0, 153, 154, 155, 156, 157, 156, 155, 154, 161, 154, 163, 154, 165, 166, 165, 154, 169, 170, 171, 170, 169, 154, 175, 176, 177, 176, 175, 180, 175, 154, 183, 154, 185, 186, 185, 188, 185, 190, 185, 192, 185, 194, 185, 154, 153, 198, 199, 198, 201, 202, 201, 198, 205, 198, 207, 208, 207, 198, 211, 212, 211, 198, 153, 216, 153, 218, 219, 220, 221, 220, 219, 218, 225, 218, 227, 228, 227, 218, 231, 218, 233, 234, 235, 236, 235, 234, 239, 234, 241, 234, 233, 244, 233, 246, 233, 248, 233, 218, 153, 252, 253, 252, 255, 256, 255, 252, 259, 252, 261, 252, 263, 252, 153, 0]
private def start (i : Nat) : Nat := starts[i]?.getD i

private def Step (i : Nat) : Prop :=
  start i ≤ i ∧ match (node nodes i).rule with
  | .split _ _ l r => l < i ∧ r < i ∧ start l = start i ∧ start r = l+1 ∧ r+1 = i
  | _ => start i = i
private instance (i : Nat) : Decidable (Step i) := by
  unfold Step
  cases (node nodes i).rule <;> infer_instance

private theorem checked_shape_0 : ∀ k : Fin 16, Step (0+k.val) := by decide +kernel

private theorem checked_shape_16 : ∀ k : Fin 16, Step (16+k.val) := by decide +kernel

private theorem checked_shape_32 : ∀ k : Fin 16, Step (32+k.val) := by decide +kernel

private theorem checked_shape_48 : ∀ k : Fin 16, Step (48+k.val) := by decide +kernel

private theorem checked_shape_64 : ∀ k : Fin 16, Step (64+k.val) := by decide +kernel

private theorem checked_shape_80 : ∀ k : Fin 16, Step (80+k.val) := by decide +kernel

private theorem checked_shape_96 : ∀ k : Fin 16, Step (96+k.val) := by decide +kernel

private theorem checked_shape_112 : ∀ k : Fin 16, Step (112+k.val) := by decide +kernel

private theorem checked_shape_128 : ∀ k : Fin 16, Step (128+k.val) := by decide +kernel

private theorem checked_shape_144 : ∀ k : Fin 16, Step (144+k.val) := by decide +kernel

private theorem checked_shape_160 : ∀ k : Fin 16, Step (160+k.val) := by decide +kernel

private theorem checked_shape_176 : ∀ k : Fin 16, Step (176+k.val) := by decide +kernel

private theorem checked_shape_192 : ∀ k : Fin 16, Step (192+k.val) := by decide +kernel

private theorem checked_shape_208 : ∀ k : Fin 16, Step (208+k.val) := by decide +kernel

private theorem checked_shape_224 : ∀ k : Fin 16, Step (224+k.val) := by decide +kernel

private theorem checked_shape_240 : ∀ k : Fin 16, Step (240+k.val) := by decide +kernel

private theorem checked_shape_256 : ∀ k : Fin 11, Step (256+k.val) := by decide +kernel

private theorem checked_steps : ∀ i : Fin nodes.size, Step i.val := by
  intro i
  have hi : i.val < 267 := i.isLt
  by_cases hsplit_128 : i.val < 128
  · by_cases hsplit_64 : i.val < 64
    · by_cases hsplit_32 : i.val < 32
      · by_cases hsplit_16 : i.val < 16
        · have hlocal : i.val-0 < 16 := by omega
          have hh := checked_shape_0 ⟨i.val-0,hlocal⟩
          have heq : 0+(i.val-0)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-16 < 16 := by omega
          have hh := checked_shape_16 ⟨i.val-16,hlocal⟩
          have heq : 16+(i.val-16)=i.val := by omega
          simpa only [heq] using hh
      · by_cases hsplit_48 : i.val < 48
        · have hlocal : i.val-32 < 16 := by omega
          have hh := checked_shape_32 ⟨i.val-32,hlocal⟩
          have heq : 32+(i.val-32)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-48 < 16 := by omega
          have hh := checked_shape_48 ⟨i.val-48,hlocal⟩
          have heq : 48+(i.val-48)=i.val := by omega
          simpa only [heq] using hh
    · by_cases hsplit_96 : i.val < 96
      · by_cases hsplit_80 : i.val < 80
        · have hlocal : i.val-64 < 16 := by omega
          have hh := checked_shape_64 ⟨i.val-64,hlocal⟩
          have heq : 64+(i.val-64)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-80 < 16 := by omega
          have hh := checked_shape_80 ⟨i.val-80,hlocal⟩
          have heq : 80+(i.val-80)=i.val := by omega
          simpa only [heq] using hh
      · by_cases hsplit_112 : i.val < 112
        · have hlocal : i.val-96 < 16 := by omega
          have hh := checked_shape_96 ⟨i.val-96,hlocal⟩
          have heq : 96+(i.val-96)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-112 < 16 := by omega
          have hh := checked_shape_112 ⟨i.val-112,hlocal⟩
          have heq : 112+(i.val-112)=i.val := by omega
          simpa only [heq] using hh
  · by_cases hsplit_192 : i.val < 192
    · by_cases hsplit_160 : i.val < 160
      · by_cases hsplit_144 : i.val < 144
        · have hlocal : i.val-128 < 16 := by omega
          have hh := checked_shape_128 ⟨i.val-128,hlocal⟩
          have heq : 128+(i.val-128)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-144 < 16 := by omega
          have hh := checked_shape_144 ⟨i.val-144,hlocal⟩
          have heq : 144+(i.val-144)=i.val := by omega
          simpa only [heq] using hh
      · by_cases hsplit_176 : i.val < 176
        · have hlocal : i.val-160 < 16 := by omega
          have hh := checked_shape_160 ⟨i.val-160,hlocal⟩
          have heq : 160+(i.val-160)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-176 < 16 := by omega
          have hh := checked_shape_176 ⟨i.val-176,hlocal⟩
          have heq : 176+(i.val-176)=i.val := by omega
          simpa only [heq] using hh
    · by_cases hsplit_224 : i.val < 224
      · by_cases hsplit_208 : i.val < 208
        · have hlocal : i.val-192 < 16 := by omega
          have hh := checked_shape_192 ⟨i.val-192,hlocal⟩
          have heq : 192+(i.val-192)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-208 < 16 := by omega
          have hh := checked_shape_208 ⟨i.val-208,hlocal⟩
          have heq : 208+(i.val-208)=i.val := by omega
          simpa only [heq] using hh
      · by_cases hsplit_240 : i.val < 240
        · have hlocal : i.val-224 < 16 := by omega
          have hh := checked_shape_224 ⟨i.val-224,hlocal⟩
          have heq : 224+(i.val-224)=i.val := by omega
          simpa only [heq] using hh
        · by_cases hsplit_256 : i.val < 256
          · have hlocal : i.val-240 < 16 := by omega
            have hh := checked_shape_240 ⟨i.val-240,hlocal⟩
            have heq : 240+(i.val-240)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-256 < 11 := by omega
            have hh := checked_shape_256 ⟨i.val-256,hlocal⟩
            have heq : 256+(i.val-256)=i.val := by omega
            simpa only [heq] using hh

private theorem checked_walk : walk nodes nodes.size (nodes.size-1) = List.range nodes.size := by
  have traversal (fuel : Nat) : ∀ i, i < nodes.size → i < fuel →
      walk nodes fuel i = List.range' (start i) (i+1-start i) := by
    induction fuel with
    | zero => intro i hi hf; omega
    | succ fuel ih =>
      intro i hi hf
      have h := checked_steps ⟨i,hi⟩
      change Step i at h
      rcases h with ⟨hstart,h⟩
      cases he : (node nodes i).rule with
      | split axis cut l r =>
        simp only [he] at h
        obtain ⟨hl,hr,hsl,hsr,hiEq⟩ := h
        have hsl_le : start i ≤ l := by
          have hh : start l ≤ l := (checked_steps ⟨l,lt_trans hl hi⟩).1
          simpa only [hsl] using hh
        have hwl := ih l (lt_trans hl hi) (by omega)
        have hwr := ih r (lt_trans hr hi) (by omega)
        simp only [walk,he]
        rw [hwl,hwr,hsl,hsr]
        let m := l+1-start i
        let n := r+1-(l+1)
        change (List.range' (start i) m ++ List.range' (l+1) n) ++ [i] =
          List.range' (start i) (i+1-start i)
        have hm : start i+m = l+1 := by dsimp [m]; omega
        have hn : m+n+1 = i+1-start i := by dsimp [m,n]; omega
        have hlast : start i+(m+n) = i := by dsimp [m,n]; omega
        have happ : List.range' (start i) m ++ List.range' (l+1) n =
            List.range' (start i) (m+n) := by
          simpa only [hm] using (List.range'_append_1 (s := start i) (m := m) (n := n))
        rw [happ]
        have hc := (List.range'_1_concat (s := start i) (n := m+n)).symm
        rw [hn,hlast] at hc
        exact hc
      | localRegion | infeasible _ | boxTail | capInfeasible _ _ | bound _ _ _ _ =>
        have hs : start i = i := by simpa only [he] using h
        have hlen : i+1-start i = 1 := by omega
        calc
          walk nodes (fuel+1) i = [i] := by simp only [walk,he]
          _ = List.range' (start i) (i+1-start i) := by
            have ht : List.range' (start i) (i+1-start i) = List.range' i 1 :=
              congrArg₂ (fun (s n : Nat) => List.range' s n) hs hlen
            exact (show [i] = List.range' i 1 from rfl).trans ht.symm
  change walk nodes 267 266 = List.range 267
  rw [List.range_eq_range']
  have hh := traversal 267 266 (by decide +kernel) (by decide +kernel)
  change walk nodes 267 266 = List.range' 0 267 at hh
  exact hh

private theorem checked_nodes_0 : ∀ k : Fin 16, NodeOK 50 true nodes (0+k.val) := by decide +kernel

private theorem checked_nodes_16 : ∀ k : Fin 16, NodeOK 50 true nodes (16+k.val) := by decide +kernel

private theorem checked_nodes_32 : ∀ k : Fin 16, NodeOK 50 true nodes (32+k.val) := by decide +kernel

private theorem checked_nodes_48 : ∀ k : Fin 16, NodeOK 50 true nodes (48+k.val) := by decide +kernel

private theorem checked_nodes_64 : ∀ k : Fin 16, NodeOK 50 true nodes (64+k.val) := by decide +kernel

private theorem checked_nodes_80 : ∀ k : Fin 16, NodeOK 50 true nodes (80+k.val) := by decide +kernel

private theorem checked_nodes_96 : ∀ k : Fin 16, NodeOK 50 true nodes (96+k.val) := by decide +kernel

private theorem checked_nodes_112 : ∀ k : Fin 16, NodeOK 50 true nodes (112+k.val) := by decide +kernel

private theorem checked_nodes_128 : ∀ k : Fin 16, NodeOK 50 true nodes (128+k.val) := by decide +kernel

private theorem checked_nodes_144 : ∀ k : Fin 16, NodeOK 50 true nodes (144+k.val) := by decide +kernel

private theorem checked_nodes_160 : ∀ k : Fin 16, NodeOK 50 true nodes (160+k.val) := by decide +kernel

private theorem checked_nodes_176 : ∀ k : Fin 16, NodeOK 50 true nodes (176+k.val) := by decide +kernel

private theorem checked_nodes_192 : ∀ k : Fin 16, NodeOK 50 true nodes (192+k.val) := by decide +kernel

private theorem checked_nodes_208 : ∀ k : Fin 16, NodeOK 50 true nodes (208+k.val) := by decide +kernel

private theorem checked_nodes_224 : ∀ k : Fin 16, NodeOK 50 true nodes (224+k.val) := by decide +kernel

private theorem checked_nodes_240 : ∀ k : Fin 16, NodeOK 50 true nodes (240+k.val) := by decide +kernel

private theorem checked_nodes_256 : ∀ k : Fin 11, NodeOK 50 true nodes (256+k.val) := by decide +kernel

private theorem checked_root : ∀ k, (node nodes (nodes.size-1)).box k = rootBox k := by decide +kernel

theorem accepted : check 50 true nodes=true := by
  apply decide_eq_true
  refine ⟨by decide +kernel, ?_, checked_walk, checked_root⟩
  intro i
  have hi : i.val < 267 := i.isLt
  by_cases hsplit_128 : i.val < 128
  · by_cases hsplit_64 : i.val < 64
    · by_cases hsplit_32 : i.val < 32
      · by_cases hsplit_16 : i.val < 16
        · have hlocal : i.val-0 < 16 := by omega
          have hh := checked_nodes_0 ⟨i.val-0,hlocal⟩
          have heq : 0+(i.val-0)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-16 < 16 := by omega
          have hh := checked_nodes_16 ⟨i.val-16,hlocal⟩
          have heq : 16+(i.val-16)=i.val := by omega
          simpa only [heq] using hh
      · by_cases hsplit_48 : i.val < 48
        · have hlocal : i.val-32 < 16 := by omega
          have hh := checked_nodes_32 ⟨i.val-32,hlocal⟩
          have heq : 32+(i.val-32)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-48 < 16 := by omega
          have hh := checked_nodes_48 ⟨i.val-48,hlocal⟩
          have heq : 48+(i.val-48)=i.val := by omega
          simpa only [heq] using hh
    · by_cases hsplit_96 : i.val < 96
      · by_cases hsplit_80 : i.val < 80
        · have hlocal : i.val-64 < 16 := by omega
          have hh := checked_nodes_64 ⟨i.val-64,hlocal⟩
          have heq : 64+(i.val-64)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-80 < 16 := by omega
          have hh := checked_nodes_80 ⟨i.val-80,hlocal⟩
          have heq : 80+(i.val-80)=i.val := by omega
          simpa only [heq] using hh
      · by_cases hsplit_112 : i.val < 112
        · have hlocal : i.val-96 < 16 := by omega
          have hh := checked_nodes_96 ⟨i.val-96,hlocal⟩
          have heq : 96+(i.val-96)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-112 < 16 := by omega
          have hh := checked_nodes_112 ⟨i.val-112,hlocal⟩
          have heq : 112+(i.val-112)=i.val := by omega
          simpa only [heq] using hh
  · by_cases hsplit_192 : i.val < 192
    · by_cases hsplit_160 : i.val < 160
      · by_cases hsplit_144 : i.val < 144
        · have hlocal : i.val-128 < 16 := by omega
          have hh := checked_nodes_128 ⟨i.val-128,hlocal⟩
          have heq : 128+(i.val-128)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-144 < 16 := by omega
          have hh := checked_nodes_144 ⟨i.val-144,hlocal⟩
          have heq : 144+(i.val-144)=i.val := by omega
          simpa only [heq] using hh
      · by_cases hsplit_176 : i.val < 176
        · have hlocal : i.val-160 < 16 := by omega
          have hh := checked_nodes_160 ⟨i.val-160,hlocal⟩
          have heq : 160+(i.val-160)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-176 < 16 := by omega
          have hh := checked_nodes_176 ⟨i.val-176,hlocal⟩
          have heq : 176+(i.val-176)=i.val := by omega
          simpa only [heq] using hh
    · by_cases hsplit_224 : i.val < 224
      · by_cases hsplit_208 : i.val < 208
        · have hlocal : i.val-192 < 16 := by omega
          have hh := checked_nodes_192 ⟨i.val-192,hlocal⟩
          have heq : 192+(i.val-192)=i.val := by omega
          simpa only [heq] using hh
        · have hlocal : i.val-208 < 16 := by omega
          have hh := checked_nodes_208 ⟨i.val-208,hlocal⟩
          have heq : 208+(i.val-208)=i.val := by omega
          simpa only [heq] using hh
      · by_cases hsplit_240 : i.val < 240
        · have hlocal : i.val-224 < 16 := by omega
          have hh := checked_nodes_224 ⟨i.val-224,hlocal⟩
          have heq : 224+(i.val-224)=i.val := by omega
          simpa only [heq] using hh
        · by_cases hsplit_256 : i.val < 256
          · have hlocal : i.val-240 < 16 := by omega
            have hh := checked_nodes_240 ⟨i.val-240,hlocal⟩
            have heq : 240+(i.val-240)=i.val := by omega
            simpa only [heq] using hh
          · have hlocal : i.val-256 < 11 := by omega
            have hh := checked_nodes_256 ⟨i.val-256,hlocal⟩
            have heq : 256+(i.val-256)=i.val := by omega
            simpa only [heq] using hh
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N50B
