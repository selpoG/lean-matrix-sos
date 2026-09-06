# 証明アーキテクチャ

[English](PROOF_ARCHITECTURE.md)

この文書は `lean-matrix-sos` の証明方針と module の依存関係を説明します。

## 主定理

主定理は全直線上の行列 SOS 分解です。

```lean
MatrixSOS.fullLine_posSemidef_iff_sos
```

実対称多項式行列 `P : PolyMat m` の各成分の次数が `2 * d` 以下で、
任意の実数 `x` について `P(x)` が半正定値なら、次数制限つきの分解

```text
P = R.transpose * R
```

を得ます。因子 `R` は矩形で、

```lean
R : Matrix (Fin (m + 1)) (Fin m) (Polynomial ℝ)
```

という固定行数の形です。

端点つき半直線の Markov-Lukacs 型 SOS 証明書は系です。

```lean
MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_sos
```

まず内部で正規化された `[0, ∞)` 版を示します。これは全直線版を `M(t^2)` に適用し、
得られた因子を偶部分と奇部分に分けるものです。公開定理では affine pullback により
`[a, ∞)` 版を直接出します。

## 証明方針

証明ルートは次です。

```text
complex function field/Pfister source
  + 有理指数 Hahn 体の非負元平方性
  -> ℝ(X) 上の二項平方和補題
  + 共通分母消去と既約因子降下
  -> full-line polynomial matrix factorization
  -> parity split
  -> normalized half-line Markov-Lukacs-type SOS certificate
  -> half-line and finite-interval certificates
  -> optional Gram repackaging
```

local-global endpoint は、任意の非負元が平方である順序拡大体に対して定式化されています。
行列分解部分は、Hahn/Tsen/Pfister 側には直接依存せず、
`MatrixSOS.fracPoly_binaryForm_represents_one_of_nonnegWhereDefined` だけを
境界として使います。この補題は、定義点で非負な非零有理関数 `a, b` に対して
`1 = a * u^2 + b * v^2` となる `u, v : ℝ(X)` が存在する、という主張です。

## 有理指数 Hahn 体

`MatrixSOS/Proof/RationalHahn.lean` は、実係数・有理数値群の Hahn 級数体に
辞書式順序を入れた体を定義します。

```lean
abbrev RationalHahnField := Lex (HahnSeries ℚ ℝ)
```

そして次を証明します。

```lean
theorem rationalHahnNonnegSquareStatement :
    forall {x : RationalHahnField}, 0 <= x -> IsSquare x
```

証明では、非零 Hahn 級数を先頭単項式と正次数誤差を持つ unit に分けます。
先頭係数は `ℝ` で平方根を取り、有理数値群 `ℚ` により先頭指数を半分にし、
unit の平方根は mathlib の Hahn-series binomial family で構成します。

## Tsen と複素有理関数体 / Pfister 部分

projective common-zero theorem は
`MatrixSOS/Proof/ProjectiveIdealHeight.lean` の可換代数の高さ補題を使います。
複素有理関数体側は `MatrixSOS/Proof/ComplexFunctionField` 以下にあります。
非負元平方閉な local-global endpoint で使う Pfister 型の isotropy 補助を供給します。
行列 SOS 本体は、次節の有理関数境界を通してこの部分を使います。
独立した Tsen statement は `MatrixSOS/Proof/Tsen.lean` で公開しています。

## 有理関数境界

順序体・Pfister 側から対角行列 reduction 側へ渡る境界は、次のファイルです。

```text
MatrixSOS/Proof/RationalFunction/BinarySum.lean
```

endpoint は次です。

```lean
theorem fracPoly_binaryForm_represents_one_of_nonnegWhereDefined
```

downstream file は、この endpoint か、明示的に `FracBinaryRepresentsOneStatement`
を引数に取る theorem に依存します。Hahn、Tsen、Pfister の証明 module を
直接 import しない構造にしています。

## 既約因子降下

全直線分解では、共通分母を払った後、既約分母因子を多項式係数のまま取り除きます。
関連ファイルは次の下にまとまっています。

```text
MatrixSOS/Proof/DiagonalReduction
MatrixSOS/Proof/NoRealRootDescent
MatrixSOS/Proof/FullLineAlgebra
MatrixSOS/Proof/FullLine
```

`DiagonalReduction` は、有理関数係数の対角化 route を担当し、双線形形式による
対角化と determinant-zero 分岐で使う Smith-kernel compression もここに閉じます。
`NoRealRootDescent` は
実根を持たない既約二次因子に対する polynomial block cancellation を担当します。
実根を持つ因子は `FullLine/Irreducible.lean` で直接処理します。
`FullLineAlgebra` は共通分母消去、square-extension、矩形 factor 抽出を担当します。
`FullLine` はこれらを組み合わせて exact polynomial matrix factorization を作ります。
bounded full-line theorem は次数パラメータについて一様です。exact factorization
自体は `d` に依存せず、次数評価は `P = R.transpose * R` の対角成分から取り出します。

## Certificates

full-line certificate layer は `MatrixSOS/Certificates/FullLine*.lean` です。
constant matrix の系は `MatrixSOS/Certificates/Constant.lean` に分けています。
`MatrixSOS/Proof/HalfLine.lean` の正規化半直線 layer は、
公開する端点つき半直線証明書のための内部段階です。半直線 API は
`MatrixSOS/Certificates/HalfLine.lean` です。有限区間では
`MatrixSOS/Proof/Interval/Certificates.lean` が証明書 predicate、
`MatrixSOS/Proof/Interval/Normalized.lean` が証明側の `[0,1]` 正規化構成、
`MatrixSOS/Certificates/Interval.lean` が端点つき `[a,b]` の公開 API を担当します。

安定した public API は次です。

```lean
MatrixSOS.fullLine_posSemidef_iff_sos
MatrixSOS.fullLine_posSemidef_iff_gram
MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_sos
MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_sos
MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_gram
MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_gram
MatrixSOS.Certificates.Interval.posSemidefOn_Icc_affinePullback_iff
MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_even
MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_odd
MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_even
MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_odd
MatrixSOS.Certificates.Scalar.polynomial_nonnegOn_univ_iff_sos
MatrixSOS.Certificates.Constant.posSemidef_iff_exists_gram
```

半直線 API は元の変数での直接の Markov-Lukacs 型証明書を公開します。
右半直線では `M = S0 + (X - a) • S1`、左半直線では
`M = S0 + (a - X) • S1` を使います。内部証明では affine pullback で
正規化しますが、public API の次数仮定は `M` 自身に対して述べます。

有限区間 API は直接の Markov-Lukacs 型証明書を公開します。次数上限 `2 * d` では

```text
M = S0 + (X - a) * (b - X) • S1
```

を使い、次数上限 `2 * d + 1` では

```text
M = (X - a) • S0 + (b - X) • S1
```

を使います。偶数次数側では `S0` の因子次数境界は `d`、`S1` の因子次数境界は
`d` の自然数 predecessor です。奇数次数側では両方とも `d` です。
各 bounded SOS 成分は `MatrixSOS.boundedMatrixSOS_to_gramTerm` により
実半正定値 Gram 行列へ変換できます。

証明は `[a, b]` を `[0, 1]` に正規化し、半直線 chart `x = u / (1 + u)` に適用し、
得られた SOS 分解を脱同次化して元の区間へ戻します。奇数次数側では、第一半直線因子に
現れる余分な最高次数を、対角成分の最高係数と有限個の実平方和が零なら各項が零であることから除去します。

スカラー版は full-line theorem を `m = 1` に特殊化し、
`p = q ^ 2 + r ^ 2` という形で公開します。定数行列版は次数 0 の edge case で、
実半正定値行列が `R.transpose * R` という矩形 Gram 行列であること、かつ full-line theorem
と同じく行数を `m + 1` に固定して表せることを述べます。

## Edge Cases

保守対象の statement は `m : Nat` と `d : Nat` に一様です。

- `d = 0` は同じ full-line factorization theorem と、最後の対角成分からの次数評価で
  処理されます。公開用の zero-degree 専用 branch は不要です。
- `m = 0` は同じ polymorphic statement に含まれます。
- zero matrix も同じ exact factorization と次数抽出の route に含まれます。
- singular matrix polynomial も含まれます。正則性や determinant 非零は仮定しません。
- 奇数次数の entry は構文上許されます。必要なのは `natDegree (P i j) <= 2 * d` だけです。

## Verification

通常の確認コマンド:

```bash
lake build MatrixSOS.Certificates
lake build MatrixSOS
```

local axiom audit:

```lean
#print axioms MatrixSOS.fullLine_posSemidef_iff_sos
#print axioms MatrixSOS.fullLine_posSemidef_iff_gram
#print axioms MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_sos
#print axioms MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_gram
#print axioms MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_even
#print axioms MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_odd
#print axioms MatrixSOS.Certificates.Scalar.polynomial_nonnegOn_univ_iff_sos
#print axioms MatrixSOS.Certificates.Constant.posSemidef_iff_exists_gram
```

documentation-only の変更では Lean build は不要です。
