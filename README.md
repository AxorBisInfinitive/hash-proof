# 哈希证明

## 主定理

若

$$
h(ax+i,by+j,cz+k)=h(x,y,z)
$$

对所有 32 位坐标 $x,y,z$ 成立，其中坐标运算按 $2^{32}$ 回绕，则
$(a,b,c,i,j,k)=(1,1,1,0,0,0)$。

主定理是 `HashProof.no_nontrivial_affine_collision`。

## 构建与审计

项目使用 Lean 4.35.0 和 Lean 标准库。安装 [Elan](https://lean-lang.org/install/) 后，在项目根目录运行以下命令。

```sh
lake build
lake env lean Audit.lean
```

`Audit.lean` 输出关键定理的公理依赖。
