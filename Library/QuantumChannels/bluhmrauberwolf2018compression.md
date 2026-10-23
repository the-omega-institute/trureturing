---
bibkey: bluhmrauberwolf2018compression
authors: Andreas Bluhm, Lukas Rauber, and Michael M. Wolf
year: 2018
title: Quantum compression relative to a set of measurements
doi: null
url: https://arxiv.org/html/1708.04898v4
claim: "Sections 4 and 7.1: compression uses a finite quantum block with classical side information; maximal algebra block size admits explicit coding and decoding channels."
strata_touched:
  - D5/S3/Quantum/Reduction/CoherentFlagPort
license: citation-only
triage: anchor
---

# Quantum compression relative to a set of measurements

Sections 4 and 7.1: compression uses a finite quantum block with classical side information; maximal algebra block size admits explicit coding and decoding channels.

The finite complex-matrix results use completely positive trace-preserving maps and all density inputs.

## Verified locator

https://arxiv.org/html/1708.04898v4

arXiv DOI: https://doi.org/10.48550/arXiv.1708.04898

## Common encoding, decoding and finite classical flags

Bluhm–Rauber–Wolf，*Quantum Compression Relative to a Set of Measurements*，
arXiv:1708.04898v4，Definition 4.1、Theorems 5.1、7.1。

Definition 4.1 令编码进入 $M_q\otimes\mathbb C^n\simeq\bigoplus_{f=1}^nM_q$，
共同 CPTP 解码返回原矩阵空间，并要求对全部输入态及声明的可观测量保持期望。
经典标记的分布可以依赖输入，故不能把标记误设为独立外部随机数。

Theorem 5.1 对紧可观测量族给存在性的正误差阈值，低于精确压缩维数的量子块
不能在任意有限经典标记辅助下跨过该阈值。它不给任意具体菜单的显式最优常数。
Theorem 7.1 以生成代数的最大矩阵块维数给压缩上界；生成代数一般不能替代
实际可观测量实线性空间来判定最小压缩维数。

小块等距填入统一 $q$ 维块时，解码须在整个块上 CPTP。若 $U^\dagger U=P$、
$UU^\dagger=Q$，可取

$$
\operatorname{Dec}(Y)=U^\dagger YU+\operatorname{tr}((I-Q)Y)\tau,
$$

其中 $\tau$ 为固定密度态；第二项补齐正交补的迹。
[AURIC Ω 第 10 节](../../docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)
显式使用这个全块合法补全。其两个实际等待设置的显式下界另由该卷证明。
