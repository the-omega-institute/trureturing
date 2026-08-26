# DECT v1.2 有限模型对抗回放

日期：2026-08-25  
范围：定义逃逸、潜表示充分性、残差覆盖与生产性对角线的有限模型复核。  
状态：计算证据。不是 Lean kernel 证明，不产生冻结真值节点。

## 1. 远端状态勘误

先前曾声称本报告已经同步到 PR #2904。对远端 PR 的文件清单复核后，该说法不成立。PR #2904 包含 DefinitionEscape、ResidualCoverage、RefinementGeometry、Promotion 的 Lean 工件及冻结收据，没有本报告，也没有有限回放程序。

本文件是该缺失项的首次远端落地。

## 2. 计数勘误

准备包中的旧版散文报告写有以下数字：

- residual_join：431,096
- adequacy_strict_witness：1,528
- finite_cover：1,962
- productive_diagonal：2,070
- operational_effective_cases：342

这些数字无法由准备包中随附的 `model_check.py` 复算得到，因此不继续沿用。对随附程序进行 fresh rerun 后，得到下面的可复算读数。

```text
residual_join_law_cases=7088
adequacy_fiber_cases=11132
inadequacy_witness_cases=11132
join_strictness_cases=11132
operational_question_cases=156
finite_cover_cases=22480
productive_diagonal_semantic_cases=200376
productive_diagonal_question_cases=2808
FINITE_MODEL_ADVERSARIAL_CHECK=PASS
```

逐项合计为：

```text
266,304 checks
```

程序 SHA-256：

```text
1f9fe8118140f7060fdfc92dd28f5089892d97c77c8344cf4d2f39ee7d0be400
```

输出 SHA-256：

```text
44c08b23762fb1ea93ce9e59d700730bc9614e9a8f720be15c34788c4e685c05
```

## 3. 被检验的命题族

### 3.1 Residual join law

对所有枚举载体，验证：

\[
R(q\vee d,T)(x,y)
\iff
R(q,T)(x,y)\land d(x)=d(y).
\]

### 3.2 Adequacy、纤维恒定与严格联合

验证以下三个等价方向：

\[
T=h\circ z
\iff
z(x)=z(y)\Rightarrow T(x)=T(y),
\]

\[
T\text{ 不可由 }z\text{ 恢复}
\iff
\exists x,y,\ z(x)=z(y)\land T(x)\ne T(y),
\]

以及：

\[
z\vee T\text{ 严格细化 }z
\iff
T\text{ 不可由 }z\text{ 恢复}.
\]

### 3.3 Operational question law

在满射的有限读数与联合读数上，验证：目标不可恢复，当且仅当存在一个二值问题可由联合读数回答、却不能由原 latent 回答。

### 3.4 Finite residual cover

对两个候选定义的所有有限选择，验证：

\[
\text{所选定义覆盖全部 residual pairs}
\iff
R(q\vee D,T)=\varnothing.
\]

### 3.5 Productive diagonal law

对有限 decoder catalog 的取反对角线，验证：

- 对角候选不属于原 catalog；
- 候选作为新语义加入时产生严格精化，当且仅当旧表示对该语义不充分；
- 在满射有限模型中，这等价于出现新的可回答二值问题。

## 4. 结论边界

在上述枚举范围内没有发现反例。这个结果支持 Lean 定理的有限语义回放，不能替代证明，也不能推出未枚举载体上的普遍正确性。

严格真值仍由 Base 中的 Lean 声明、证明项与 axiom closure 裁决。此报告只记录可复算的对抗性有限检查。

## 5. 完整复算程序

```python
from __future__ import annotations

from itertools import combinations, product
from typing import Iterable, Sequence


def functions(domain_size: int, codomain_size: int) -> Iterable[tuple[int, ...]]:
    return product(range(codomain_size), repeat=domain_size)


def factors_through(coarse: Sequence[int], finer: Sequence[int], coarse_size: int, finer_size: int) -> bool:
    """coarse = decoder ∘ finer for some total decoder."""
    decoder: list[int | None] = [None] * finer_size
    for x, z in enumerate(finer):
        value = coarse[x]
        if decoder[z] is None:
            decoder[z] = value
        elif decoder[z] != value:
            return False
    return True


def join(left: Sequence[int], right: Sequence[int], right_size: int) -> tuple[int, ...]:
    return tuple(l * right_size + r for l, r in zip(left, right, strict=True))


def residual_pair(current: Sequence[int], target: Sequence[int], x: int, y: int) -> bool:
    return current[x] == current[y] and target[x] != target[y]


def residual_join_law() -> int:
    cases = 0
    for x_size in range(1, 4):
        for current_size in range(1, 3):
            for added_size in range(1, 3):
                for target_size in range(1, 3):
                    for current in functions(x_size, current_size):
                        for added in functions(x_size, added_size):
                            joined = join(current, added, added_size)
                            for target in functions(x_size, target_size):
                                for x in range(x_size):
                                    for y in range(x_size):
                                        lhs = residual_pair(joined, target, x, y)
                                        rhs = residual_pair(current, target, x, y) and added[x] == added[y]
                                        assert lhs == rhs
                                        cases += 1
    return cases


def adequacy_laws() -> tuple[int, int, int]:
    fiber_cases = witness_cases = strict_cases = 0
    for x_size in range(1, 5):
        for latent_size in range(1, 4):
            for target_size in range(1, 4):
                for latent in functions(x_size, latent_size):
                    for target in functions(x_size, target_size):
                        adequate = factors_through(target, latent, target_size, latent_size)
                        fiber_constant = all(
                            latent[x] != latent[y] or target[x] == target[y]
                            for x in range(x_size)
                            for y in range(x_size)
                        )
                        witness = any(
                            residual_pair(latent, target, x, y)
                            for x in range(x_size)
                            for y in range(x_size)
                        )
                        joined = join(latent, target, target_size)
                        strict = (
                            factors_through(latent, joined, latent_size, latent_size * target_size)
                            and not factors_through(joined, latent, latent_size * target_size, latent_size)
                        )
                        assert adequate == fiber_constant
                        assert (not adequate) == witness
                        assert strict == (not adequate)
                        fiber_cases += 1
                        witness_cases += 1
                        strict_cases += 1
    return fiber_cases, witness_cases, strict_cases


def operational_question_law() -> int:
    cases = 0
    for x_size in range(1, 5):
        for latent_size in range(1, 4):
            for target_size in range(1, 4):
                for latent in functions(x_size, latent_size):
                    if set(latent) != set(range(latent_size)):
                        continue
                    for target in functions(x_size, target_size):
                        joined = join(latent, target, target_size)
                        join_size = latent_size * target_size
                        if set(joined) != set(range(join_size)):
                            continue
                        inadequate = not factors_through(target, latent, target_size, latent_size)
                        exists_question = False
                        for question in functions(x_size, 2):
                            through_join = factors_through(question, joined, 2, join_size)
                            through_latent = factors_through(question, latent, 2, latent_size)
                            if through_join and not through_latent:
                                exists_question = True
                                break
                        assert inadequate == exists_question
                        cases += 1
    return cases


def subsets(size: int) -> Iterable[tuple[int, ...]]:
    for length in range(size + 1):
        yield from combinations(range(size), length)


def finite_cover_law() -> int:
    cases = 0
    for x_size in range(1, 4):
        for current_size in range(1, 3):
            for target_size in range(1, 3):
                for current in functions(x_size, current_size):
                    for target in functions(x_size, target_size):
                        for candidate_0 in functions(x_size, 2):
                            for candidate_1 in functions(x_size, 2):
                                candidates = (candidate_0, candidate_1)
                                for chosen in subsets(2):
                                    covers = all(
                                        not residual_pair(current, target, x, y)
                                        or any(candidates[index][x] != candidates[index][y] for index in chosen)
                                        for x in range(x_size)
                                        for y in range(x_size)
                                    )
                                    selected = tuple(
                                        tuple(candidates[index][x] for index in chosen)
                                        for x in range(x_size)
                                    )
                                    selected_ids = {value: index for index, value in enumerate(sorted(set(selected)))}
                                    selected_encoded = tuple(selected_ids[value] for value in selected)
                                    selected_size = max(1, len(selected_ids))
                                    joined = join(current, selected_encoded, selected_size)
                                    closed = all(
                                        not residual_pair(joined, target, x, y)
                                        for x in range(x_size)
                                        for y in range(x_size)
                                    )
                                    assert covers == closed
                                    cases += 1
    return cases


def diagonal(twist: Sequence[int], catalog: Sequence[Sequence[int]]) -> tuple[int, ...]:
    return tuple(twist[catalog[a][a]] for a in range(len(catalog)))


def productive_diagonal_law() -> tuple[int, int]:
    semantic_cases = operational_cases = 0
    symbol_size = 2
    twist = (1, 0)
    for address_size in (1, 2):
        rows = list(functions(address_size, symbol_size))
        for catalog_indices in product(range(len(rows)), repeat=address_size):
            catalog = tuple(rows[index] for index in catalog_indices)
            candidate = diagonal(twist, catalog)
            assert candidate not in catalog
            for world_size in range(1, 5):
                for current_size in range(1, 4):
                    for expression_size in range(1, 4):
                        for current in functions(world_size, current_size):
                            for semantics in functions(world_size, expression_size):
                                joined = join(current, semantics, expression_size)
                                productive = (
                                    candidate not in catalog
                                    and factors_through(current, joined, current_size, current_size * expression_size)
                                    and not factors_through(joined, current, current_size * expression_size, current_size)
                                )
                                inadequate = not factors_through(semantics, current, expression_size, current_size)
                                assert productive == inadequate
                                semantic_cases += 1
                                if set(current) == set(range(current_size)) and set(joined) == set(
                                    range(current_size * expression_size)
                                ):
                                    exists_question = any(
                                        factors_through(question, joined, 2, current_size * expression_size)
                                        and not factors_through(question, current, 2, current_size)
                                        for question in functions(world_size, 2)
                                    )
                                    assert productive == exists_question
                                    operational_cases += 1
    return semantic_cases, operational_cases


def main() -> None:
    residual_cases = residual_join_law()
    fiber_cases, witness_cases, strict_cases = adequacy_laws()
    question_cases = operational_question_law()
    cover_cases = finite_cover_law()
    productive_cases, productive_question_cases = productive_diagonal_law()
    print(f"residual_join_law_cases={residual_cases}")
    print(f"adequacy_fiber_cases={fiber_cases}")
    print(f"inadequacy_witness_cases={witness_cases}")
    print(f"join_strictness_cases={strict_cases}")
    print(f"operational_question_cases={question_cases}")
    print(f"finite_cover_cases={cover_cases}")
    print(f"productive_diagonal_semantic_cases={productive_cases}")
    print(f"productive_diagonal_question_cases={productive_question_cases}")
    print("FINITE_MODEL_ADVERSARIAL_CHECK=PASS")


if __name__ == "__main__":
    main()
```
