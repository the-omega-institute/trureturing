"""Torch 2.8 Metal transport and explicitly recorded, synthetic device probes."""

import math
import os
from pathlib import Path
import time

from . import certify
from .exact import require


class MpsRunner:
    def __init__(self, constants, record):
        # Must precede the first Torch import; no CPU transport or fallback exists.
        os.environ['PYTORCH_ENABLE_MPS_FALLBACK'] = '0'
        import torch
        require(torch.__version__ == '2.8.0', 'torch pin mismatch')
        require(torch.backends.mps.is_built() and torch.backends.mps.is_available(),
                'actual MPS device unavailable; CPU fallback prohibited')
        self.torch, self.record, self.gpu_seconds = torch, record, 0.0
        self.record('compile',dict(status='started',kernel_calls=0))
        self.library = torch.mps.compile_shader(Path(__file__).with_name('search.metal').read_text())
        self.record('compile',dict(status='compiled',kernel_calls=0,
                                  max_threads=self.library.search.max_threads_per_threadgroup,
                                  thread_execution_width=self.library.search.thread_execution_width))
        flat = [value for row in constants for value in row['primes']+row['sorted_masks']]
        self.table = self.tensor(flat)

    def tensor(self, data, floating=False):
        t = self.torch.tensor(data,dtype=self.torch.float32 if floating else self.torch.int32,device='mps')
        require(t.device.type == 'mps','tensor is not on MPS')
        return t

    def empty(self, shape, floating=False):
        # Initialization makes partial writes fail coverage or become explicit NaNs.
        return self.torch.full(shape,float('nan') if floating else -1,
                               dtype=self.torch.float32 if floating else self.torch.int32,device='mps')

    def dispatch(self, name, *args, threads):
        event = dict(status='started',kernel=name,threads=threads)
        self.record('dispatch',event)
        start = time.perf_counter()
        try:
            # Documented v2.8 callable interface; scalar configuration uses int32 buffers.
            getattr(self.library,name)(*args,threads=threads)
            self.torch.mps.synchronize()
        except BaseException as error:
            event.update(status='failed',error=repr(error))
            raise
        else:
            event['status']='returned'
        finally:
            elapsed=time.perf_counter()-start
            self.gpu_seconds += elapsed
            event['dispatch_and_synchronize_seconds']=elapsed
            self.record('dispatch_result',event)

    def search(self, first, last):
        count=25*(last-first+1)
        integers=self.empty((count,18)); floats=self.empty((count,14),True)
        config=self.tensor([25*first,count])
        self.dispatch('search',integers,floats,self.table,config,threads=count)
        ints=integers.cpu().tolist(); fp=floats.cpu().tolist()
        return [dict(integers=v,floats=[float(x).hex() for x in f]) for v,f in zip(ints,fp)]

    def device_tests(self):
        """Four dispatches: arithmetic, guards, IDs only, synthetic real grids."""
        def limbs(n): return [(n>>(8*k))&255 for k in range(64)]
        modulus=256**64
        cases=[(255,19,1,4846),(256**63-1,19,1,(256**63-1)*19),
               (1,19,102,19**102-1),(modulus-1,19,1,(modulus-19)),
               (1,2,511,2**511),(1,2,512,0)]
        inp=self.tensor([limbs(a)+[p,n] for a,p,n,_ in cases])
        targets=self.tensor([limbs(target) for _,_,_,target in cases]); out=self.empty((len(cases),66))
        self.dispatch('limb_probe',out,inp,targets,threads=len(cases))
        actual=out.cpu().tolist()
        expected=[]
        for a,p,n,target in cases:
            value=a*p**n; reduced=value%modulus
            expected.append(limbs(reduced)+[int(value>=modulus),int(reduced>target)-int(reduced<target)])
        self.record('probe',dict(name='limb_probe',actual=actual,expected=expected,passed=actual==expected))
        require(actual==expected,'device limb carry/overflow/comparison disagreement')

        operands=[[5041,10,11,121,130,129,131], [5040,10,11,121,130,129,131],
                  [5041,11,11,121,130,129,131], [5041,10,11,121,121,120,122],
                  [5041,10,11,121,130,130,131], [5041,10,11,121,130,129,130]]
        inp=self.tensor([[x for v in row for x in limbs(v)] for row in operands]); out=self.empty((6,))
        self.dispatch('guard_probe',out,inp,threads=6)
        actual=out.cpu().tolist(); expected=[31,30,29,27,23,15]
        self.record('probe',dict(name='guard_probe',operands=operands,actual=actual,expected=expected,
                                 passed=actual==expected))
        require(actual==expected,'device strict cutoff/equality disagreement')

        expected=[[0,0,0,0,0,0,0],[102399,4095,24,0,15,15,15],
                  [102400,4096,0,1,0,0,0],[5734399,229375,24,55,15,15,15],
                  [76800,3072,0,0,12,0,0]]
        inp=self.tensor([row[0] for row in expected]); out=self.empty((5,7))
        self.dispatch('decode_probe',out,inp,threads=5)
        actual=out.cpu().tolist()
        self.record('probe',dict(name='decode_probe',actual=actual,expected=expected,passed=actual==expected,
                                 exponent_box_search=False))
        require(actual==expected,'device stable ID decoding disagreement')

        cases=[([2,2,2],[4,4,4],8,64),([2,2,2],[4,4,4],8,512),
               ([2,3,5],[16,6,10],64,512)]
        inp=self.tensor([[math.log(x) for x in C+D+[q0,q1]] for C,D,q0,q1 in cases],True)
        out=self.empty((3,14),True); errors=self.empty((3,))
        self.dispatch('numerical_probe',out,errors,inp,threads=3)
        actual=out.cpu().tolist(); flags=errors.cpu().tolist(); expected=[]
        from flint import ctx
        with ctx.workprec(128):
            for C,D,q0,q1 in cases:
                values=certify.evaluate(C,D,q0,q1)
                expected.append(float(values['G']*values['ell'].exp()))
        # A bounded API/numerical sanity test, emphatically not a roundoff certificate.
        passed=flags==[0,0,0] and all(math.isfinite(row[6]) and abs(row[6]-v)<1e-4
                                                    for row,v in zip(actual,expected))
        self.record('probe',dict(name='numerical_probe',synthetic_cases=cases,actual=actual,flags=flags,
                                 arb_scaled_midpoints=expected,sanity_tolerance=1e-4,passed=passed,
                                 rigorous_gpu_error_bound=False))
        require(passed,'device synthetic mixture evaluation disagreement')
