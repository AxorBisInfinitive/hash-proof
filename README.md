# 哈希证明

```java
public static long hash(long x, long y, long z) {
    long xb = ((y & 0xFFFFFFFFL) << 32) | (z & 0xFFFFFFFFL);
    long ha = x & 0xFFFFFFFFL;
    ha ^= ha >>> 33;
    ha *= 0xFF51AFD7ED558CCDL;
    ha ^= ha >>> 33;
    ha *= 0xC4CEB9FE1A85EC53L;
    ha ^= ha >>> 33;

    long h = xb ^ ha;
    h ^= h >>> 33;
    h *= 0xFF51AFD7ED558CCDL;
    h ^= h >>> 33;
    h *= 0xC4CEB9FE1A85EC53L;
    h ^= h >>> 33;
    return h;
}
```

令 $\bar x,\bar y,\bar z$ 为 Java 参数各自低 32 位的零扩展，定义 $P(y,z)=2^{32}\bar y+\bar z$。由于两部分占据互不重叠的 32 位区间，该加法等价于 Java 代码中的按位或。

令 $S(v)=v\oplus\mathrm{lshr}(v,33)$，其中 $\mathrm{lshr}(v,33)$ 表示对 v 逻辑右移 33 位，对应 Java 的 `>>>`。

$M^{(1)},M^{(2)}$ 为代码中依次出现的两个乘数。乘法按 $2^{64}$ 回绕。

$$
F(v)=S\bigl(S(vM^{(1)})M^{(2)}\bigr),\qquad
h(x,y,z)=P(y,z)\oplus F(\bar{x}).
$$

Java 方法返回 $F(S(h(x,y,z)))$。内层首次右移异或在零扩展的 $\bar{x}$ 上不改变值。外层 $F\circ S$ 是双射，因此 Java 哈希相等当且仅当 Lean 中的 $h$ 相等。

## 主定理

若

$$
h(ax+i,by+j,cz+k)=h(x,y,z)
$$

对所有 32 位坐标 $x,y,z$ 成立，其中坐标运算按 $2^{32}$ 回绕，则
$(a,b,c,i,j,k)=(1,1,1,0,0,0)$。

主定理是 `HashProof.no_nontrivial_affine_collision`。

| 文件                       | 内容                                                             |
| -------------------------- | ---------------------------------------------------------------- |
| `HashProof/Mix.lean`       | 证明 64 位混合与逆混合互逆，并刻画混合函数在 32 位输入上的像集。 |
| `HashProof/AffineXor.lean` | 分类与固定掩码异或等价的四种仿射映射。                           |
| `HashProof.lean`           | 检查 15 个非零掩码并证明主定理。                                 |

## 构建与审计

项目使用 Lean 4.35.0 和 Lean 标准库。安装 [Elan](https://lean-lang.org/install/) 后，在项目根目录运行以下命令。

```sh
lake build
lake env lean Audit.lean
```

`Audit.lean` 输出关键定理的公理依赖。
