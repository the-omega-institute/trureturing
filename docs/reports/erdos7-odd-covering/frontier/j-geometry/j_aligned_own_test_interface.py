"""Exact category and cell-table arithmetic for the aligned equality source.

Mathematical scope: actual countable J source, original45/135 aligned,
qJ=1 and rho=2/675. This does not decide realizability from a table.
"""
from fractions import Fraction as F
import argparse
from hashlib import sha256
from pathlib import Path
import importlib.util
import json
import sys
sys.dont_write_bytecode=True
CERTIFICATE='certificates/source_norms/j-geometry/j_aligned_own_test_interface.json'
PINS={
 'profile-notes/001-064/57-common-deleted-measure-coupling.md':'d21cccdff1069cf7f1f15d14ad616cd259e0071b8c2a20244b22b88da7974be7',
 'profile-notes/129-192/130-the-whole-j-face-forces-source-anti-alignment.md':'c9c11d0250836f7abc67eed901716f867b7a916a9797afcaa14b3f70584e33a8',
 'profile-notes/257-320/311-imperfect-j-source-alignment-forces-a-sharp-sector-surplus.md':'cb1d7434b43a9e8d6091ff691cd022d479f9c898c7c5678a81e546d34659662f',
 'certificates/source_norms/cover-geometry/common_deleted_measure_coupling.json':'97e24c96d6fcea0e47f335d0f3ab18680df2d8ce1ecc1a03fbc4f3478a6dff51',
 'certificates/source_norms/j-geometry/j_face_alignment.json':'75433cab317fb492b5e8a9b36bc9b8d8671f5bcfe450cc7a2e37efe5378108d5',
 'certificates/source_norms/j-geometry/j_leading_alignment_surplus.json':'8be57ff7cc2565cc53a5eaf5db9ad8360e30fc9673b76dd55bca48c3dfc7e2af',
}
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
parser.add_argument('--output',type=Path,help='Optional isolated staging certificate path.')
mode=parser.add_mutually_exclusive_group()
mode.add_argument('--write',action='store_true')
mode.add_argument('--check',action='store_true')
args=parser.parse_args()
BASE=args.base.resolve()
OUTPUT=args.output if args.output is not None else BASE/CERTIFICATE

def require(ok,msg):
    if not ok: raise ValueError(msg)

spec=importlib.util.spec_from_file_location('aligned_equality_io',BASE/'certificate_io.py')
require(spec is not None and spec.loader is not None,'canonical IO')
io=importlib.util.module_from_spec(spec);spec.loader.exec_module(io)
inputs={}
for rel,pin in PINS.items():
    raw=io.read_artifact_bytes(BASE/rel)
    require(sha256(raw).hexdigest()==pin,'pinned mathematical source '+rel)
    if rel.endswith('.json'): inputs[rel]=json.loads(raw)
source57=inputs['certificates/source_norms/cover-geometry/common_deleted_measure_coupling.json']
source130=inputs['certificates/source_norms/j-geometry/j_face_alignment.json']
source311=inputs['certificates/source_norms/j-geometry/j_leading_alignment_surplus.json']
require(F(source130['linear_upper'])==F(16,25),'unchanged original saturated own-test interface')
require(F(source311['aligned_sector_limiting_rho'])==F(2,675),'actual sharp aligned surplus')
require(F(source311['aligned_sector_limiting_survivor_mass'])==F(413,2700),'actual limiting source mass')
joint_moments={k:F(v) for k,v in source57['joint_cost_moment_constants'].items()}
require(joint_moments=={'(1, 1)':F(2227,640),'(1, 2)':F(13481,320),
                       '(2, 1)':F(13481,320),'(2, 2)':F(884579,1280)},
        'complete independent-test moment constants reused exactly')
require(F(17,90)+F(2,5)*F(1,72)==F(7,36),'off-face epsilon coefficient from actual S0-D and lambda bounds')
g=F(1,135)
eta=(F(1,18),)+(F(1,9),)*4
qcols=(F(0),F(1,5),F(1,5),F(3,20),F(1,5))
rows=[]
for L in (2,3,4):
    others=[l for l in (2,3,4) if l!=L]
    for late_cell in others:
        raw=[]
        weighted=[]
        for l in range(5):
            values=(F(0),F(1,5),F(1,5),F(3,20),F(1,5)) if l<2 else (
                (F(0),F(0),F(0),F(1,10),F(1,5)) if l==L else
                (F(0),F(0),F(1,5),F(1,10),F(1,5)))
            raw_row=[eta[l]*v for v in values]
            if l==L: raw_row[4]-=g
            if l==late_cell: raw_row[2]-=F(1,270)
            require(min(raw_row)>=0,'nonnegative current upper cell table')
            raw.append(raw_row)
            weighted.append([v*(1-F(int(l<2)+int(l==1)+int(j==4)+int(l>=2 and j==4),5))
                             for j,v in enumerate(raw_row)])
        cols=[sum(row[j] for row in weighted)-qcols[j]/90 for j in range(5)]
        rootcols=[[sum(weighted[l][j] for l in root) for j in range(5)] for root in ((0,1),(2,3,4))]
        require(cols==[F(0),F(1,50),F(41,675),F(29,600),F(11,225)],'all exact whole-column bounds')
        require(max(cols)==F(41,675),'test5 bound attained in table at B')
        require(rootcols[1]==[F(0),F(0),F(11,270),F(1,30),F(8,225)],'root1 exact column bounds')
        require(max(v for row in rootcols for v in row)==F(11,270),'test15 maximum over all roots and columns')
        rows.append({'leading_cell':L,'remaining_b1_late_cell':late_cell,'raw_upper':raw,
                     'four_deletion_weighted_upper':weighted,'whole_column_caps_after_pure3':cols,'root_column_caps':rootcols})
# Actual ternary formula: lambda(T) already loses zeta on its literal27 cylinder.
root_caps=(F(3,40),F(11,120)+2*g/5)
require(root_caps[1]==F(511,5400),'modified root1 cap')
require(F(2,45)-F(1,45)-g+2*g/5==F(4,225)<F(2,45),'aligned cell cannot become the maximizing9 cell')
require(F(2,5)-F(1,5)<F(11,20),'literal135 subtraction cannot increase the deep ternary maximum')
categories={
    'test3':F(11,120)+2*g/5,
    'test9':F(2,45),
    'pure3_depth_ge3':F(11,360),
    'test5':F(41,675),
    'pure5_depth_ge2':F(13,600),
    'test15':F(11,270),
    'three_five_depth_ge2':F(1,60),
    'nine_five_depth_ge1':F(1,36),
    'deep3_positive5':F(1,72)}
zero7=sum(categories.values())
require(zero7==F(79,225),'all nonunit zero7 categories sum exactly')
positive7=(F(1,4)+F(1,2)-2*g)/5
S=F(3,20)+2*g/5
mean=S+zero7+positive7
hinge1=mean-S
reserve=6*S-mean
require(positive7==F(397,2700),'all positive7 cap sum retains both unavoidable source holes')
require(S==F(413,2700) and mean==F(293,450),'complete own-test mean bound')
require(hinge1==F(269,540) and reserve==F(4,15),'complete H1 and barrier6 reserve')

def encode(value):
    if isinstance(value,F): return str(value)
    if isinstance(value,dict): return {k:encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)): return [encode(v) for v in value]
    return value

out=encode({'schema':'erdos7-aligned-own-test-interface-v1','source_sha256':PINS,
            'residual_interface':{'rho_floor':F(2,675),'delta_coefficient':F(7,36),
                'complete_joint_moment_constants':joint_moments,
                'budget':'epsilon_* = S-D-(2/5)*(1/135-lambda) <= rho-2/675+7*delta/36',
                'scope':'For the same actual V and actual deletion; this alone does not transport the exact endpoint cell table.'},
            'scope':'Exact limiting actual source with qJ=1, aligned original45/135, rho=2/675; ordinary proof supplies source forcing, this checks only complete table/category arithmetic.',
            'g':g,'remaining_b1_late':F(1,270),'cases':rows,'ternary_root_caps':root_caps,
            'zero7_categories':categories,'zero7_nonunit_total':zero7,'positive7_total':positive7,
            'source_mass':S,'complete_mean_upper':mean,'complete_hinge1_upper':hinge1,'barrier6_reserve_lower':reserve})
if args.write:
    io.write_certificate_text(OUTPUT,json.dumps(out,indent=2)+'\n')
require(json.loads(io.read_artifact_bytes(OUTPUT))==out,'exact canonical endpoint and residual interface certificate')
print('PASS: six actual-cell upper table endpoints; complete category sums; mean',mean,'H1',hinge1,'6S-mean',reserve)
