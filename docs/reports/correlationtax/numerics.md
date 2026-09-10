# 独立数值复算

NumPy 2.0.2，seed=20260911，complex128，单位为自然对数。
160 例的分布、判据和对照已在 preregistration-v1.md 写定。
互信息由联合矩阵的两次偏迹和三个谱熵计算，相对熵由矩阵对数迹另算。
不把 D 定义成 S(diag rho)-S(rho)，故主检验不是自指的恒等测试。

{
  "seed": 20260911,
  "tolerance": 1e-10,
  "count": 160,
  "main_max": 1.2212453270876722e-15,
  "main_pass": 160,
  "minus_control_count": 120,
  "minus_control_fail": 120,
  "entropy_max": 9.992007221626409e-16,
  "marginal_max": 0.0,
  "cq_max": 0.0,
  "numpy": "2.0.2"
}

首版将非正小谱值的 log 替换为 log(1e-300)，主残差 1.1302070390684094e-13。
该版 160/160 仍通过预登记的 1e-10 容差，但与仓内总定义 log(0)=0 不一致。
修订为绝对阈值 1e-14 下取 log 值 0；熵也用相同零谱阈值。
初版结果 numeric-floor-log.json 和正式结果 numeric.json 均保留在 runner attempt。
两版样本与判据未改变；以上数值不是 kernel 证明。

复现代码（亦保存为 attempt/numeric.py）：

```python
import json
from pathlib import Path
import numpy as np
rng = np.random.default_rng(20260911)
def entropy(a):
    e=np.linalg.eigvalsh(a); e=e[e>1e-14]
    return float(-np.sum(e*np.log(e)))
def rel(a,b):
    e,u=np.linalg.eigh(a); f,v=np.linalg.eigh(b)
    le=np.zeros_like(e); lf=np.zeros_like(f)
    le[e>1e-14]=np.log(e[e>1e-14]); lf[f>1e-14]=np.log(f[f>1e-14])
    la=(u*le)@u.conj().T
    lb=(v*lf)@v.conj().T
    return float(np.trace(a@(la-lb)).real)
def mi(a,d):
    t=a.reshape(d,d,d,d)
    l=np.einsum('abad->bd',t); r=np.einsum('abcb->ac',t)
    return entropy(l)+entropy(r)-entropy(a),l,r
rows=[]
for d in range(2,6):
    v=np.zeros((d*d,d),complex)
    v[np.arange(d)*(d+1),np.arange(d)]=1
    for kind in ['diagonal','pure','full','low']:
        for k in range(10):
            rank={'pure':1,'full':d,'low':max(1,d-1),'diagonal':d}[kind]
            z=rng.normal(size=(d,rank))+1j*rng.normal(size=(d,rank))
            rho=z@z.conj().T
            if kind=='diagonal': rho=np.diag(np.diag(rho))
            rho=rho/np.trace(rho); pinch=np.diag(np.diag(rho))
            joint=v@rho@v.conj().T
            val,l,r=mi(joint,d); tax=rel(rho,pinch); sp=entropy(pinch)
            cq=v@pinch@v.conj().T; cqmi,_,_=mi(cq,d)
            rows.append(dict(d=d,kind=kind,index=k,main=val-sp-tax,minus=val-sp+tax,
              entropy=entropy(joint)-entropy(rho),left=float(np.max(np.abs(l-pinch))),
              right=float(np.max(np.abs(r-pinch))),cq=cqmi-sp))
res=dict(seed=20260911,tolerance=1e-10,count=len(rows),
    main_max=max(abs(x['main']) for x in rows),
    main_pass=sum(abs(x['main'])<1e-10 for x in rows),
    minus_control_count=sum(x['kind']!='diagonal' for x in rows),
    minus_control_fail=sum(x['kind']!='diagonal' and abs(x['minus'])>1e-10 for x in rows),
    entropy_max=max(abs(x['entropy']) for x in rows),
    marginal_max=max(max(x['left'],x['right']) for x in rows),cq_max=max(abs(x['cq']) for x in rows),
    numpy=np.__version__,rows=rows)
p=Path(__file__).with_name('numeric.json');p.write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:v for k,v in res.items() if k!='rows'},indent=2))
```
