# 哈希证明

[![License: CC0-1.0](https://img.shields.io/badge/License-CC0_1.0-lightgrey.svg)](https://creativecommons.org/publicdomain/zero/1.0/)

## 主定理

令 $R=\mathbb Z/2^{32}\mathbb Z$，定义 $h(x,y,z)=P(y,z)\oplus H(x)$。
其中 $P(y,z)$ 将 $y$、$z$ 分别放入高、低 32 位，$H$ 对零扩展后的 $x$ 应用 `mix64`。

对任意 $A\in M_3(R)$ 和 $t\in R^3$，若对所有 $v\in R^3$ 都有 $h(Av+t)=h(v)$，则

$$ A=I_3,\qquad t=0. $$

主定理是 `HashProof.no_nontrivial_general_affine_collision`。

## 构建与审计

项目使用 Lean 4.35.0 和 Lean 标准库。安装 [Elan](https://lean-lang.org/install/) 后，在项目根目录运行以下命令。

```sh
lake build
lake env lean Audit.lean
```

`Audit.lean` 输出关键定理的公理依赖。
