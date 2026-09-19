#!/usr/bin/env python3
"""Propose complete J second-depth duals, with exact full-column verification."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    if spec is None or spec.loader is None:raise ValueError('Loadable original source')
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[1])
    parser.add_argument('--dependency-directory',type=Path)
    parser.add_argument('--checkpoint',type=Path)
    args=parser.parse_args()
    if args.dependency_directory:sys.path.insert(0,str(args.dependency_directory))
    core=load('j_depth_propose_core',args.base/'frontier/j_face_second_depth_retained_heads.py')
    previous=load('j_depth_existing_solver',args.base/'frontier/propose_j_face_retained135125_heads.py')
    solver=[None]
    def propose(lp,obj):
        if solver[0] is None:solver[0]=previous.Solver(lp)
        return solver[0].solve(obj)
    result=core.calculate(args.base,proposer=propose)
    text=json.dumps(result,indent=2)+'\n'
    if args.checkpoint:args.checkpoint.write_text(text)
    io=load('j_depth_proposal_writer',args.base/'certificate_io.py')
    io.write_certificate_text(args.base/core.CERTIFICATE,text)
    print('WROTE all three complete second-depth J heads',flush=True)


if __name__=='__main__':main()
