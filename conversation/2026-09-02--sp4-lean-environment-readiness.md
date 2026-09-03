# Sp4 Lean 环境与形式化边界检查

日期：2026-09-02

本轮只通读材料并搭建环境，不开始论文证明。

## 材料定位

- `Sp4_Degree4_Vanishing_Word_Lifting_Patched.tex` 是证明主体，主结论为
  $H_{\mathrm{cb}}^4(\operatorname{Sp}(4,\mathbb C);\mathbb R)=0$。
- `Sp4_Degree4_Vanishing_Lean_Readiness_Specification.tex` 是 Lean 准备说明，
  将工作分为 `CORE`、`INFRA`、`EXTERNAL`、`CERTIFICATE` 和 `ASSEMBLY`，
  并给出模块结构、分期与验收清单。

推荐的首个具体目标是 Pfaffian 复形的有界正合性

$$
\ker\!\left(E:L^\infty(\mathcal U_5)\to L^\infty(\mathcal U_6)\right)
=
\operatorname{im}\!\left(D:L^\infty(\mathcal U_4)\to L^\infty(\mathcal U_5)\right).
$$

## 已确认的边界

文章原创且承重的 Gram/Pfaffian 代数、缺陷恒等式、有限对应与紧回归、
纤维正则化、低阶双复形计算、仿射差 cocycle、双锥扩散以及二阶极点证书，
均须由 Lean 内核验证。旧文献结果可先通过单一外部接口模块使用，但接口必须
精确定义并记录原始来源、定理编号、假设及实际使用的自然性。

## 环境

- Lean `v4.33.1`
- mathlib tag `v4.33.1`
- mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`
- `lake build` 与 `lake env lean Sp4.lean` 均已通过。

当前 `Sp4.lean` 只是 `import Mathlib` 的烟雾测试；尚未写入文章定义、定理、
公理或证明。
