#!/usr/bin/env python3
"""Exact finite library for every binary9qs central-leaf layout.

The 1024 layouts independently assign each9qs central role to leaf4 orleaf5.
Each layout selects one entire priority95 family, used for every corner/query.
Only pinned640 and658 sibling certificates are inputs.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,product
from math import prod,lcm
from hashlib import sha256
from collections import Counter
import argparse,json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path)
args=parser.parse_args();checks=Counter()
def ck(name,value):
 if not value:raise ArithmeticError(name)
 checks[name]+=1
PINS={'remaining33_global_root_exclusion_certificate.json':'dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4','joint_square_pair_225_star_certificate.json':'cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5'}
sources={}
for name,pin in PINS.items():
 raw=(args.directory/name).read_bytes();ck('source_pin',sha256(raw).hexdigest()==pin);sources[name]=json.loads(raw)
base=sources['remaining33_global_root_exclusion_certificate.json'];network=sources['joint_square_pair_225_star_certificate.json']
Q=(7,11,13,17,19);I=(0,1,2,4,5);J=tuple(m for m in range(20)if m!=5)
CELLS=tuple(product(range(6),range(20)));LIVE=tuple((l,m)for l,m in product(I,J)if not(l<3 and m<5));CASES=tuple(product((0,4,5),(0,6,10,15)))
EDGES=tuple(combinations(range(5),2));EM=tuple(sum(1<<q for q in e)for e in EDGES);PAIRS=tuple((e,f)for e,f in combinations(range(10),2)if not EM[e]&EM[f])
g=F(200163067,201247200);r=tuple(F(1,q-1)for q in Q);a=tuple(F(1,q*(q-2))for q in Q)
B0=tuple(a[u]*r[v]+r[u]*a[v]for u,v in EDGES);B1=tuple(r[u]*r[v]for u,v in EDGES)
C=list(map(F,base['combined512_coefficients']));ck('complete512_nonnegative',len(C)==512 and min(C)>=0)
ck('same_unit_gate_coefficient',g==F(base['constants']['g'])==F(network['g']))
for u in range(1,5):C[32*9+(1<<u)]+=g*a[u]
DC=lcm(g.denominator,*(x.denominator for x in C));GI=int(g*DC);CI=[int(x*DC)for x in C]

# Exact matching polynomial coefficients for four unary profiles.
polys={}
for n in range(4):
 Z=tuple(F(5,6)-F(n,35)if q==7 else F(q-2,q-1)-2*a[u]for u,q in enumerate(Q))
 ck('uniform_strict_shearer_box',1-sum((B0[e]+B1[e])/(Z[u]*Z[v])for e,(u,v)in enumerate(EDGES))>=F(754111121894423,876550251053789))
 for T in range(32):
  def zprod(mask):return prod((Z[u]for u in range(5)if not mask>>u&1),start=F(1))
  es=[e for e in range(10)if not T&EM[e]];ps=[(e,f)for e,f in PAIRS if not T&(EM[e]|EM[f])]
  b=zprod(T)-sum((B0[e]*zprod(T|EM[e])for e in es),F())+sum((B0[e]*B0[f]*zprod(T|EM[e]|EM[f])for e,f in ps),F())
  us=[F()]*10
  for e in es:us[e]=-B1[e]*zprod(T|EM[e])+sum((B1[e]*B0[f]*zprod(T|EM[e]|EM[f])for f in es if not EM[e]&EM[f]),F())
  vs=[B1[e]*B1[f]*zprod(T|EM[e]|EM[f])if(e,f)in ps else F()for e,f in PAIRS]
  polys[n,T]=(b,us,vs)
DH=lcm(*(x.denominator for b,us,vs in polys.values()for x in[b]+us+vs))
responses={}
for(n,T),(b,us,vs)in polys.items():
 bi=int(b*DH);ui=[int(x*DH)for x in us];vi=[int(x*DH)for x in vs]
 for mask in range(1024):
  value=bi+sum(ui[e]for e in range(10)if mask>>e&1)+sum(v for(e,f),v in zip(PAIRS,vi)if mask>>e&1 and mask>>f&1)
  ck('all_local_subset_responses_positive',value>0);responses[n,T,mask]=value

def orbit(i,j,l,m):return('r'if i<3 else str(i),('eq'if i==l else'other')if i<3 and l<3 else'r'if l<3 else str(l),j//5,m//5,j==m)
KEYS=sorted({orbit(i,j,l,m)for i,j in product(I,J)for l,m in LIVE});INDEX={key:k for k,key in enumerate(KEYS)}
ck('orbit_count',len(KEYS)==180)
def profile(l,m):return(0 if l<3 else 2 if l==4 else 4)+int(m//5==2)
# BEGIN LITERAL LIBRARY
FAMILIES=[{'denominator': 180, 'numerators': [165, 165, 165, 171, 165, 165, 165, 165, 171, 165, 165, 165, 171, 171, 165, 165, 165, 171, 165, 165, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 160, 165, 160, 160, 160, 165, 160, 160, 165, 165, 160, 160, 165, 160, 160, 160, 160, 160, 165, 160, 160, 160, 160, 165, 160, 160, 160, 165, 165, 160, 160, 160, 165, 160, 160, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 160, 165, 160, 160, 160, 165, 160, 160, 165, 165, 160, 160, 165, 160, 160, 160, 160, 160, 165, 160, 160, 160, 160, 165, 160, 160, 160, 165, 165, 160, 160, 160, 165, 160, 160, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 180, 165, 171, 165, 165, 165, 171, 165, 165, 171, 171, 165, 165, 171, 165, 165, 160, 165, 160, 160, 160, 165, 160, 160, 165, 165, 160, 160, 165, 160, 160]}, {'denominator': 1048576, 'numerators': [748129, 1048576, 786173, 755795, 755802, 1048576, 1048576, 1048576, 1048575, 1048576, 861089, 1019333, 881529, 1048575, 861321, 850636, 1039426, 850639, 866552, 1048576, 678146, 967318, 725806, 713479, 687578, 967318, 969584, 977423, 964035, 966654, 793238, 936380, 851581, 964035, 792574, 800953, 977423, 820015, 825266, 966654, 639847, 662796, 639756, 896100, 896100, 887204, 885086, 795946, 758448, 887204, 736952, 772273, 751269, 760869, 885086, 748129, 1048576, 786173, 755795, 755802, 1048576, 1048576, 1048576, 1048575, 1048576, 861089, 1019333, 881446, 1048575, 861321, 850636, 1039426, 850639, 866552, 1048576, 722964, 1012726, 759907, 729971, 730279, 1012726, 1012871, 1012871, 1012725, 1012726, 833977, 984803, 853031, 1012725, 831851, 820607, 1012871, 820015, 835751, 1012726, 689836, 703954, 679449, 942233, 942233, 975962, 942095, 919275, 819514, 975962, 774490, 941876, 791066, 777749, 942095, 451807, 787508, 662703, 507911, 532358, 641332, 711827, 828208, 658414, 636203, 521441, 678553, 521649, 776094, 524585, 643246, 828208, 653504, 529666, 943543, 495756, 749660, 617917, 506483, 488848, 612576, 667881, 737409, 621479, 610199, 467763, 618629, 509793, 639638, 501748, 635192, 732922, 639638, 562305, 954479, 689836, 703954, 679449, 942233, 942233, 975962, 942095, 919275, 819514, 975962, 774490, 941876, 791066, 777749, 942095, 527597, 348056, 379309, 583070, 583070, 565427, 540213, 566792, 503578, 565427, 464930, 581026, 464007, 420222, 861259]}, {'denominator': 1048576, 'numerators': [760803, 1048567, 790886, 793701, 766597, 1048567, 1048576, 1048576, 1048576, 1048576, 858258, 1032539, 894517, 1048576, 858879, 850747, 1037942, 857105, 870180, 1048576, 769788, 1047846, 788863, 773679, 772786, 1047846, 1047918, 1047918, 1047834, 1047860, 859281, 1030916, 875256, 1047834, 857999, 847747, 1047918, 850065, 863051, 1047860, 708838, 711808, 687398, 943738, 943738, 977641, 943721, 934154, 819593, 977641, 774569, 942213, 797182, 784619, 943721, 741102, 1034403, 786622, 746814, 749705, 1034403, 1034778, 1034778, 1034343, 1034458, 827708, 996482, 827311, 1034343, 822832, 832300, 1034778, 832420, 844733, 1034458, 769788, 1047846, 788863, 773679, 772786, 1047846, 1047918, 1047918, 1047834, 1047860, 859281, 1030916, 875256, 1047834, 857999, 847747, 1047918, 850065, 863051, 1047860, 705080, 710389, 685815, 931075, 931075, 932614, 931000, 891775, 816681, 932614, 766851, 929893, 777340, 763806, 931000, 417645, 757977, 641107, 574537, 268372, 757977, 992615, 992615, 520511, 776511, 0, 872487, 549716, 659761, 728484, 668570, 802677, 659761, 381009, 776511, 573703, 722478, 172931, 580746, 574920, 63453, 953609, 953609, 839711, 785643, 722478, 786921, 643128, 839711, 438762, 683049, 830594, 0, 670350, 785643, 708838, 711808, 687398, 943738, 943738, 977641, 943721, 934154, 819593, 977641, 774569, 942213, 797182, 784619, 943721, 520439, 499613, 496696, 789616, 789616, 733608, 719377, 716737, 733608, 733608, 694168, 609304, 621801, 573978, 719377]}, {'denominator': 1048576, 'numerators': [729334, 1019108, 764211, 763535, 736364, 1019108, 1019317, 1019317, 1048576, 1019113, 827152, 1012385, 878641, 1048576, 827327, 826966, 1019317, 857546, 842650, 1019113, 750882, 1048573, 786459, 757904, 758013, 1048573, 1048576, 1048576, 1048572, 1048576, 844719, 1018047, 858514, 1048572, 845396, 848150, 1015108, 847530, 864704, 1048576, 692065, 692124, 668015, 924579, 924579, 957721, 924428, 924558, 808209, 957721, 762598, 921222, 777954, 765077, 924428, 727289, 988167, 757061, 729438, 686265, 988167, 1014710, 1014710, 988213, 988008, 776174, 973699, 802870, 988213, 779956, 792095, 980384, 780016, 842650, 988008, 750882, 1048573, 786459, 757904, 758013, 1048573, 1048576, 1048576, 1048572, 1048576, 844719, 1018047, 858514, 1048572, 845396, 848150, 1015108, 847530, 864704, 1048576, 686881, 686073, 662351, 920222, 920222, 928537, 896316, 897381, 785533, 928537, 739991, 868956, 760088, 753565, 896316, 467091, 622976, 579718, 347099, 465017, 622976, 640757, 696552, 631341, 622265, 537995, 505320, 603741, 631341, 534313, 542893, 696552, 384291, 330103, 622265, 334321, 637481, 550450, 491733, 465719, 637481, 633200, 685252, 623242, 597891, 548609, 560677, 532748, 623242, 428374, 575822, 685252, 582408, 597891, 597891, 692065, 692124, 668015, 924579, 924579, 957721, 924428, 924558, 808209, 957721, 762598, 921222, 777954, 765077, 924428, 404298, 445344, 425540, 570762, 570762, 548907, 565575, 510818, 540997, 548907, 507824, 527167, 513127, 521211, 565575]}]
SELECTION=[0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 0, 3, 3, 2, 0, 3, 3, 3, 0, 3, 3, 2, 0, 3, 3, 2, 3, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 0, 3, 0, 0, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 0, 3, 3, 2, 0, 3, 3, 3, 0, 3, 3, 2, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 0, 3, 3, 2, 0, 3, 3, 3, 0, 3, 3, 2, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 0, 3, 3, 2, 0, 3, 3, 3, 0, 3, 3, 2, 0, 3, 3, 3, 3, 3, 3, 1, 0, 3, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 1, 3, 2, 3, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 0, 3, 0, 0, 0, 3, 0, 3, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 0, 3, 3, 2, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 0, 3, 3, 2, 0, 3, 0, 3, 0, 3, 3, 2, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 0, 3, 3, 2, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 0, 3, 3, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 1, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 0, 3, 3, 2, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 2, 3, 3, 3, 1, 0, 0, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 3, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 3, 3, 3, 3, 3, 3, 1, 0, 3, 3, 2, 3, 3, 3, 1, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 1, 0, 3, 3, 3, 3, 3, 3, 2, 0, 3, 3, 2, 3, 3, 3, 1, 0, 3, 3, 3, 0, 3, 3, 2, 0, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 1, 3, 1, 2, 1]
# END LITERAL LIBRARY
ck('library_size',len(FAMILIES)==4)
ck('complete_layout_selector',len(SELECTION)==1024 and all(isinstance(s,int)and 0<=s<4 for s in SELECTION))
for family in FAMILIES:
 den=family['denominator'];nums=family['numerators'];ck('field_shape',len(nums)==180 and den>0)
 for num in nums:ck('field_value_bounds',isinstance(num,int)and 0<=num<=den)
 for i,j in product(I,J):
  for l,m in LIVE:
   val=nums[INDEX[orbit(i,j,l,m)]]
   ck('ternary_priority',nums[INDEX[orbit(l,j,l,m)]]>=val)
   ck('quinary_priority',nums[INDEX[orbit(i,m,l,m)]]>=val)

def reduced_selectors(family,i,j):
 nums=family['numerators'];x=[0 if l==3 else 1 if l==i else 2 for l in range(6)];y=[0 if m==5 else 3 if m==j else 4 for m in range(20)]
 MX=[[x],[[x[l]if l//3==b else 0 for l in range(6)]for b in range(2)],[[x[l]if l==b else 0 for l in range(6)]for b in I],[[9 if l==b else 0 for l in range(6)]for b in I]]
 MY=[[y],[[y[m]if m//5==b else 0 for m in range(20)]for b in range(4)],[[y[m]if m==b else 0 for m in range(20)]for b in J],[[60 if m==b else 0 for m in range(20)]for b in J]]
 menus=[];raw_count=0
 for e3,e5 in product(range(4),repeat=2):
  rows=[]
  for xx in MX[e3]:
   for yy in MY[e5]:
    raw_count+=1;vec=[0]*6
    for l,m in LIVE:vec[profile(l,m)]+=xx[l]*yy[m]*nums[INDEX[orbit(i,j,l,m)]]
    rows.append(tuple(vec))
  unique=sorted(set(rows));kept=[u for u in unique if not any(u!=v and all(a<=b for a,b in zip(u,v))for v in unique)]
  for u in rows:ck('selector_preserved_or_dominated',any(all(a<=b for a,b in zip(u,v))for v in kept))
  menus.append([tuple((p,w)for p,w in enumerate(v)if w)for v in kept])
 ck('all_literal_selectors_count',raw_count==559)
 return menus
MENUS={(s,i,j):reduced_selectors(family,i,j)for s,family in enumerate(FAMILIES)for i,j in CASES}
records=[];minimum=None;readings=0
for mask in range(1024):
 s=SELECTION[mask];family=FAMILIES[s];den=675*family['denominator']*DH*DC
 # Profiles are regular/noncolumn2,regular/column2,leaf4/{other,column2},leaf5/{other,column2}.
 V=[[responses[0,T,0],responses[1,T,0],responses[1,T,mask],responses[2,T,mask],responses[2,T,1023^mask],responses[3,T,1023^mask]]for T in range(32)]
 corners=[]
 for i,j in CASES:
  menus=MENUS[s,i,j];screens=[]
  for mode,ss in enumerate(menus):
   for T in range(32):
    value=max(sum(V[T][p]*w for p,w in sel)for sel in ss);screens.append(value);readings+=1
  gate=F(GI*screens[0]-sum(c*z for c,z in zip(CI,screens)),den)
  ck('complete_branch_corner_gate',gate>=F(1864487415907319442048626989,931162766019912935308800000000))
  row=dict(weak3=i,weak5=j,gate=str(gate));corners.append(row)
  if minimum is None or gate<F(minimum['gate']):minimum=dict(layout_mask=mask,family=s,**row)
 records.append(dict(layout_mask=mask,family=s,corner_gates=corners))
ck('all1024_layouts',len(records)==1024 and readings==1024*12*512)
gate=F(minimum['gate']);alpha=F(network['projection_alpha']);policies=[]
for policy in network['policies']:
 fee=F(network['finite_fee_upper'])+F(network['complete_five_parent_tail'])+F(network['ordinary_typeI_fee'])+F(policy['fee'])
 margin=alpha*(gate-fee);ck('complete_network_density',margin>F(1,420000))
 policies.append(dict(kind=policy['kind'],K=policy['K'],complete_fee=str(fee),projected_margin=str(margin),density_denominator=420000))
out=dict(schema='binary-leaf-pair-library-cover-v1',status='PASS',new_lean_verification=False,source_sha256=PINS,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),scope='All ten9qs central roles independently leaf4/leaf5, fixed low phases/nulls/square7roles/50incidences and existing ordinary/private networks',edges=[list(e)for e in combinations(Q,2)],orbit_keys=KEYS,families=FAMILIES,selection=SELECTION,corner_representatives=CASES,layout_count=1024,represented_corner_count=95,computed_corner_count=12,complete_screen_count=readings,minimum=minimum,layout_records=records,policies=policies,checks=dict(checks),check_count=sum(checks.values()))
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status='PASS',check_count=out['check_count'],minimum=minimum,policies=[dict(kind=p['kind'],projected=float(F(p['projected_margin'])))for p in policies]),indent=2))
