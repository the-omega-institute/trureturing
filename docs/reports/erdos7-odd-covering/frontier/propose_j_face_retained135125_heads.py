#!/usr/bin/env python3
"""Propose retained J135/125 duals; exact arithmetic verifies every column."""
from fractions import Fraction as F
from pathlib import Path
from time import perf_counter
import argparse,importlib.util,json,sys
sys.dont_write_bytecode=True

def require(condition,message):
 if not condition: raise ValueError(message)

class Solver:
 def __init__(self,lp):
  import numpy as np
  from scipy.sparse import csr_matrix
  self.np=np
  self.lp=lp
  def matrix(rows):return csr_matrix(([float(a)for row in rows for a in row.values()],([i for i,row in enumerate(rows)for _ in row],[k for row in rows for k in row])),shape=(len(rows),lp.nvars))
  self.A,self.Ae=matrix(lp.rows),matrix(lp.equalities);self.b=np.array(list(map(float,lp.rhs)));self.be=np.array(list(map(float,lp.erhs)))
 def solve(self,obj):
  from scipy.optimize import linprog
  np=self.np
  lp=self.lp;started=perf_counter();res=linprog(-np.array(list(map(float,obj))),A_ub=self.A,b_ub=self.b,A_eq=self.Ae,b_eq=self.be,bounds=(0,None),method='highs')
  require(res.success,res.message)
  y=[max(F(0),F(round(float(-x)*10**12),10**12))for x in res.ineqlin.marginals];z=[F(round(float(-x)*10**12),10**12)for x in res.eqlin.marginals]
  for k in range(lp.nvars):
   gap=obj[k]-sum(a*y[i]for i,a in lp.columns[k])-sum(a*z[i]for i,a in lp.eqcolumns[k])
   if gap>0:y[lp.unit_rows[k]]+=gap
  value=sum(a*b for a,b in zip(y,lp.rhs))+sum(a*b for a,b in zip(z,lp.erhs));record={'nonzero_inequality_duals':{str(i):str(x)for i,x in enumerate(y)if x},'equality_duals':list(map(str,z)),'raw_objective_upper':str(value)}
  require(lp.checker.check(obj,record)==value,'Every3306 exact dual column passes independently of numerical optimality')
  return record

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1])
 parser.add_argument('--dependency-directory',type=Path)
 parser.add_argument('--checkpoint',type=Path,help='Optional temporary complete result before canonical publication')
 args=parser.parse_args()
 if args.dependency_directory:sys.path.insert(0,str(args.dependency_directory))
 sp=importlib.util.spec_from_file_location('j_pair_core',args.base/'frontier/j-source/j_face_retained135125_heads.py')
 core=importlib.util.module_from_spec(sp);sp.loader.exec_module(core)
 solver=[None]
 def propose(lp,obj):
  if solver[0]is None:solver[0]=Solver(lp)
  return solver[0].solve(obj)
 result=core.calculate(args.base,proposer=propose)
 if args.checkpoint:args.checkpoint.write_text(json.dumps(result,indent=2)+'\n')
 io=core.module('j_pair_writer_io',args.base/'certificate_io.py')
 io.write_certificate_text(args.base/core.CERTIFICATE,json.dumps(result,indent=2)+'\n')
 print('WROTE complete actual J135/125 heads',flush=True)

if __name__=='__main__':main()
