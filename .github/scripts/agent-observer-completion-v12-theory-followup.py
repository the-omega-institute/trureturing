from pathlib import Path

path = Path("docs/develop/theory/FORMAL_OBSERVER_COMPLETION_REFLECTION.md")
text = path.read_text(encoding="utf-8")


def replace_once(old: str, new: str, label: str) -> None:
    global text
    if new in text:
        return
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected one old block, found {count}")
    text = text.replace(old, new, 1)


old_version = "**版本：v1.2，2026-08-29**"
new_version = "**版本：v1.2.1，2026-08-29**"
replace_once(old_version, new_version, "version")

history_marker = "并勘正公共固定点的超限迭代条件**。"
history_replacement = (
    history_marker[:-1]
    + " → **v1.2.1 勘误：把 pointed holonomy 明确定义为可见回返与隐藏状态变化的合取，"
    + "并使公共 closure 的联合推进在空指标族上仍为扩张算子**。"
)
replace_once(history_marker, history_replacement, "version history")

old_holonomy = r'''若同时

$$
F_wx\ne x,
$$

则称其具有非平凡 pointed holonomy。若

$$
s(F_wx)\ne s(x),
$$

则该 holonomy 对策略可见。'''
new_holonomy = r'''定义 pointed holonomy 谓词

$$
\operatorname{Hol}_q(w,x)
\Longleftrightarrow
q(F_wx)=q(x)\ \land\ F_wx\ne x.
$$

因此 holonomy 同时包含可见基点回返与隐藏状态变化。只满足 $F_wx\ne x$ 时，本文称其为非平凡 transport。若

$$
s(F_wx)\ne s(x),
$$

则该 pointed holonomy 对策略可见。'''
replace_once(old_holonomy, new_holonomy, "pointed holonomy definition")

old_detection = r'''$$
q(F_wx)=q(x)
\ \land\ 
s(F_wx)\ne s(x)
\Longrightarrow
F_wx\ne x.
$$'''
new_detection = r'''$$
q(F_wx)=q(x)
\ \land\ 
s(F_wx)\ne s(x)
\Longrightarrow
\operatorname{Hol}_q(w,x).
$$'''
replace_once(old_detection, new_detection, "holonomy detection theorem")

old_joint_kernel_tail = (
    "加入新坐标只会缩小联合 kernel；若新坐标分离了旧联合 kernel 中的一对状态，则该精化严格。"
)
new_joint_kernel_tail = old_joint_kernel_tail + r'''

### 顺序方向约定

接口侧采用“更细信息更大”的顺序，因此联合读出是 supremum，行为 completion 是扩张 closure。kernel 侧顺序相反：联合读出对应关系交，接口 completion 对应 kernel 收缩。后文在关系格上讨论迭代时，必须显式翻转这一方向，不能把接口侧的扩张性原样写成 kernel 侧的扩张性。'''
replace_once(old_joint_kernel_tail, new_joint_kernel_tail, "order-direction convention")

old_advance = r'''$$
T(x)=\bigvee_{i\in I}C_i(x).
$$'''
new_advance = r'''$$
T(x)=x\vee\bigvee_{i\in I}C_i(x).
$$

前置的 $x\vee(-)$ 使定义也覆盖空指标族；此时 $T=\operatorname{id}$。当 $I$ 非空时，由每个 $C_i$ 的扩张性可省略该前置项。'''
replace_once(old_advance, new_advance, "common-closure advance")

path.write_text(text, encoding="utf-8")
