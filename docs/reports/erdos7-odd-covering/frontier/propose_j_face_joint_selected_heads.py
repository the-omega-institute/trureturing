#!/usr/bin/env python3
"""Propose rational duals; the canonical J checker verifies all columns exactly."""
from fractions import Fraction as F
from pathlib import Path
import argparse, importlib.util, json, sys
sys.dont_write_bytecode=True
class Solver:
 def __init__(self,lp):
  import numpy as np
  from scipy.sparse import csr_matrix
  self.np=np
  self.lp=lp
  def mat(rows):return csr_matrix(([float(a)for r in rows for a in r.values()],([i for i,r in enumerate(rows)for _ in r],[k for r in rows for k in r])),shape=(len(rows),lp.nvars))
  self.A,self.b=mat(lp.rows),np.array(list(map(float,lp.rhs)));self.Ae,self.be=mat(lp.equalities),np.array(list(map(float,lp.erhs)))
 def solve(self,obj):
  from scipy.optimize import linprog
  np=self.np
  lp=self.lp;r=linprog(-np.array(list(map(float,obj))),A_ub=self.A,b_ub=self.b,A_eq=self.Ae,b_eq=self.be,bounds=(0,None),method='highs')
  if not r.success:raise ValueError(r.message)
  y=[max(F(0),F(round(float(-v)*10**12),10**12))for v in r.ineqlin.marginals];z=[F(round(float(-v)*10**12),10**12)for v in r.eqlin.marginals]
  def deficit(k):return obj[k]-sum(a*y[i]for i,a in lp.columns[k])-sum(a*z[i]for i,a in lp.eqcolumns[k])
  for s in range(5):z[6+s]+=max(F(0),deficit(825+s),deficit(830+s))
  for c in range(5):z[11+c]+=max([F(0)]+[deficit(850+5*c+s)for s in range(5)])
  for k,row in lp.e3_zero.items():y[row]+=max(F(0),deficit(k))
  for k,row in enumerate(lp.y_link):y[row]+=max(F(0),deficit(425+k))
  for group,cols in enumerate(lp.lambda_groups):z[group]+=max([F(0)]+[deficit(k)for k in cols])
  for cell in range(25):y[cell]+=max([F(0)]+[deficit(k)for k in range(16*cell,16*(cell+1))])
  y[lp.theta_upper]+=max(F(0),deficit(875))
  value=sum(v*a for v,a in zip(y,lp.rhs))+sum(v*a for v,a in zip(z,lp.erhs))
  record={'nonzero_inequality_duals':{str(i):str(v)for i,v in enumerate(y)if v},'equality_duals':list(map(str,z)),'raw_objective_upper':str(value)}
  lp.check_dual(obj,record)
  return value,record,r.x

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--dependency-directory',type=Path)
    args=parser.parse_args()
    if args.dependency_directory:sys.path.insert(0,str(args.dependency_directory))
    s=importlib.util.spec_from_file_location('j_joint',args.base/'frontier/j_face_joint_selected_heads.py')
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
    solver=[None]
    def propose(lp,obj):
        if solver[0] is None:solver[0]=Solver(lp)
        return solver[0].solve(obj)[1]
    result=m.calculate(args.base,proposer=propose)
    io=m.module('j_joint_writer',args.base/'certificate_io.py')
    io.write_certificate_text(args.base/m.CERTIFICATE,json.dumps(result,indent=2)+'\n')
    print('WROTE complete J joint selected heads',flush=True)
if __name__=='__main__':main()
