# lean-matrix-sos

[English](README.md)

このリポジトリは、実対称一変数多項式行列に対する SOS
(sum of squares, 平方和) 分解定理を Lean 4 で形式化します。

スカラーの場合、SOS は有限個の多項式平方の和
`p = sum i, q i ^ 2` を意味します。行列の場合はその自然な一般化として、
矩形多項式行列 `R` による分解

```text
P = R.transpose * R
```

を意味します。次数制限つき SOS 因子は、単項式基底で展開することで同値な
実 Gram 行列証明書としても表せます。

主定理は全直線上の行列 SOS 分解です。

```lean
#check MatrixSOS.fullLine_posSemidef_iff_sos
```

実対称多項式行列 `P : PolyMat m` の各成分の次数が `2 * d` 以下のとき、
この定理は、全ての実数 `x` で `P(x)` が半正定値であることと、矩形多項式行列
`R : Matrix (Fin (m + 1)) (Fin m) (Polynomial ℝ)` が存在し、
`R` の各成分の次数を `d` 以下に取れて、

```text
P = R.transpose * R
```

となることが同値である、と述べます。ここで `R` は `m` 列と `m + 1` 行を持ちます。
同じ内容は、単項式基底上の実半正定値 Gram 行列としても公開しています。

```lean
#check MatrixSOS.fullLine_posSemidef_iff_gram
```

## 半直線と有限区間

一般の端点を持つ半直線の Markov-Lukacs 型 SOS 証明書は系として得られます。

```lean
#check MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_sos
#check MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_sos
#check MatrixSOS.Certificates.HalfLine.posSemidefOn_Ici_iff_gram
#check MatrixSOS.Certificates.HalfLine.posSemidefOn_Iic_iff_gram
```

最初の定理は `[a, ∞)` 上の半正定値性を、元の変数での重み付き SOS 表示

```text
M = S0 + (X - a) • S1
```

で特徴づけます。`S0`, `S1` は SOS 行列多項式で、次数境界は
`evenPartDegreeBound d = d / 2`, `oddPartDegreeBound d = (d - 1) / 2`
で与えられます。二つ目は `(-∞, a]` 版で、重み `a - X` を使います。
Gram 版は同じ SOS データを係数行列にまとめたものです。

有限区間には直接の Markov-Lukacs 型 SOS 証明書があります。半直線と同様に、
領域上で非負な重みと SOS 項で非負性を表します。次数上限の偶奇で形が変わります。

```lean
#check MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_even
#check MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsSOS_odd
#check MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_even
#check MatrixSOS.Certificates.Interval.posSemidefOn_Icc_iff_lukacsGram_odd
```

`a < b` とします。偶数次数側では、各成分の次数が `2 * d` 以下のとき、
`[a, b]` 上の半正定値性は

```text
M = S0 + (X - a) * (b - X) • S1
```

という形の SOS 証明書と同値です。奇数次数側では、各成分の次数が
`2 * d + 1` 以下のとき、

```text
M = (X - a) • S0 + (b - X) • S1
```

という形になります。偶数次数側では `S0` の因子次数は `d` 以下、`S1` は
`max (d - 1) 0` 以下です。奇数次数側では両方とも `d` 以下です。
いずれも `MatrixSOS.boundedMatrixSOS_to_gramTerm` により各 SOS 成分を Gram 形に変換できます。
偶数次数側は
`M = GramTerm d m Y0 + (X - a) * (b - X) • GramTerm (max (d - 1) 0) m Y1`、
奇数次数側は
`M = (X - a) • GramTerm d m Y0 + (b - X) • GramTerm d m Y1`
となり、各 `Y0`, `Y1` は実半正定値行列です。

スカラー版と定数行列版も公開 API として用意しています。

```lean
#check MatrixSOS.Certificates.Scalar.polynomial_nonnegOn_univ_iff_sos
#check MatrixSOS.Certificates.Constant.posSemidef_iff_exists_gram
```

スカラー版の bounded theorem は、`natDegree p ≤ 2 * d` のもとで、
実直線上の非負性と `p = q ^ 2 + r ^ 2` かつ
`natDegree q ≤ d`, `natDegree r ≤ d` であることを同値にします。
定数行列版は、実半正定値行列がちょうど `R.transpose * R` という
矩形 Gram 行列であり、行数を `m + 1` に固定して表せることを述べます。

証明内部で使う有理関数境界も公開 API として用意しています。

```lean
#check MatrixSOS.fracPoly_binaryForm_represents_one_of_nonnegWhereDefined
```

この定理は、非零な `a b : ℝ(X)` が実定義点で非負なら、二変数対角形式
`⟨a,b⟩` が `1` を表す、すなわちある `u v : ℝ(X)` により
`a * u^2 + b * v^2 = 1` となることを述べます。

## Build

このプロジェクトは Lake 経由で Lean 4 と mathlib を使います。

```bash
lake build
```

ビルド前に、固定された mathlib のビルドキャッシュを取得するには次を実行します。

```bash
lake exe cache get
```

公開 certificate API は次でも確認できます。

```bash
lake build MatrixSOS.Certificates
lake build MatrixSOS
```

公開定理の監査と API 使用例は次で確認できます。

```bash
lake build MatrixSOS.Audit MatrixSOS.Examples
```

`MatrixSOS/Audit.lean` には、公開定理に対する再現性のある
`#print axioms`, `#check`, `#guard_msgs` の確認を置いています。
監査対象の公開定理はプロジェクト固有の axiom を使いません。確認された axiom は、
Lean/mathlib の標準的な古典数学用 axiom である
`[propext, Classical.choice, Quot.sound]` です。

監査対象のいずれかの定理で依存公理がこの集合と異なる場合、検査は失敗します。

`MatrixSOS/Examples.lean` は、全直線、半直線、有限区間、スカラー版の公開定理を
直接使う小さな API 使用例です。

source scan は次で確認できます。

```bash
rg -n "^\s*(axiom|unsafe|set_option)\b|\b(sorry|admit)\b" MatrixSOS MatrixSOS.lean -S
```

mathlib の text-based style linter は次で確認できます。

```bash
lake exe lint-style MatrixSOS MatrixSOS.Audit MatrixSOS.Examples
```

PDF は `go-task` / [Task](https://taskfile.dev/) で生成できます。

```bash
task pdf
```

これには `uplatex` と `dvipdfmx` が必要です。

生成物:

- `docs/matrix_sos_proof_ja.pdf`
- `docs/matrix_sos_proof_en.pdf`

## 証明ルート

全直線版は次の三つから証明します。

1. 有理関数体上の complex function field/Pfister reduction。
2. 有理指数 Hahn 体を用いた非負元平方閉な順序拡大。
3. 厳密な多項式行列分解のための共通分母消去と既約因子降下。

正規化された半直線版は全直線版を `P(t) = M(t^2)` に適用し、得られた因子を
偶奇分解して得ます。端点つき半直線は affine pullback で得ます。有限区間版は
`[a, b]` を `[0, 1]` に正規化し、半直線 chart を経由してから脱同次化して得ます。
Gram 証明書は、得られた bounded SOS 因子を係数行列にまとめたものです。

## 有理指数 Hahn 体の役割

証明で使う `RationalHahnField` は、実係数・有理数値群の Hahn 級数体に辞書式順序を入れたものです。

```lean
RationalHahnField = Lex (HahnSeries ℚ ℝ)
```

表示中の `ℚ` は指数/値群、`ℝ` は係数体です。このリポジトリでは、この順序 Hahn 体の
非負元が平方であることを、先頭項による正規化と残る unit の二項級数平方根により直接証明します。
この証明では mathlib の Hahn 級数、辞書式順序、二項級数の基盤を使います。

詳細な module map は [PROOF_ARCHITECTURE.ja.md](PROOF_ARCHITECTURE.ja.md) にあります。

## Repository Layout

- `MatrixSOS/Polynomial.lean`: 実一変数多項式の基本記法。
- `MatrixSOS/PolyMatrix.lean`: 多項式行列、SOS predicate、affine pullback、
  Gram form などの公開 certificate 側の基礎定義。
- `MatrixSOS/Proof/Polynomial`: 有理関数・既約因子降下で使う実一変数多項式補題。
- `MatrixSOS/Proof/RationalFunction`: 有理関数の positivity、local-global statement、
  行列証明が使う binary sum-of-squares 境界。
- `MatrixSOS/Proof/ProjectiveIdealHeight`: Tsen/projective common-zero theorem が使う
  可換代数の高さ補題。
- `MatrixSOS/Proof/ComplexFunctionField`: 複素有理関数体/Pfister 補助。
- `MatrixSOS/Proof/RationalHahn`: Rational Hahn 平方根と positivity witness。
- `MatrixSOS/Proof/NoRealRootDescent`: 実根を持たない既約二次因子の
  polynomial block cancellation。
- `MatrixSOS/Proof/DiagonalReduction`: 有理関数係数の対角化 reduction。
  双線形形式による対角化と Smith kernel compression もここに含む。
- `MatrixSOS/Proof/FullLineAlgebra`: 全直線証明のための共通分母、square-extension、
  矩形 factor 抽出。
- `MatrixSOS/Proof/FullLine`: exact full-line 多項式行列分解と bounded theorem 用の次数評価。
- `MatrixSOS/Proof/HalfLine.lean` と `MatrixSOS/Proof/Interval`: 半直線・有限区間の
  certificate predicate と正規化された proof-side construction。
- `MatrixSOS/Certificates`: 全直線、半直線、有限区間の公開 certificate API と、
  スカラー・定数行列の系。
- `MatrixSOS/Audit.lean`: 公開定理の再現可能な監査。
- `MatrixSOS/Examples.lean`: 公開 API の小さな使用例。

## References

全直線上の行列 SOS 定理の主な数学的参照は次です。

- Christoph Hanselka and Rainer Sinn,
  *Positive Semidefinite Univariate Matrix Polynomials*,
  Mathematische Zeitschrift 292 (2019), no. 1-2, 83-101,
  DOI: 10.1007/s00209-018-2137-7.

このリポジトリは有限行数の矩形 SOS 因子の存在を形式化しています。最小行数の主張や、
行列式の二平方表示との一般的な対応は形式化の対象に含みません。

関連文献:

- Grigoriy Blekherman, Daniel Plaumann, Rainer Sinn, and Cynthia Vinzant,
  *Low-Rank Sum-of-Squares Representations on Varieties of Minimal Degree*,
  International Mathematics Research Notices 2019, no. 1, 33-54.
- Igor Klep and Markus Schweighofer,
  *Pure States, Positive Matrix Polynomials and Sums of Hermitian Squares*,
  Indiana Univ. Math. J. 59 (2010), no. 3, 857-874.
- Victoria Powers and Bruce Reznick,
  *Polynomials That Are Positive on an Interval*,
  Transactions of the American Mathematical Society 352 (2000), no. 10,
  4677-4692.

スカラーの Markov-Lukacs 型の半直線・有限区間表示については、Powers--Reznick が参照先です。

## Citation and License

著者: **Mocho Go**（[selpoG](https://github.com/selpoG)）。
[ORCID: 0009-0000-8123-9408](https://orcid.org/0009-0000-8123-9408).

ソフトウェアとしての引用情報は [CITATION.cff](CITATION.cff) に記載しています。
引用した形式化を再現できるよう、使用したリリースまたは commit を明記してください。

[Apache License 2.0](LICENSE) の下で公開しています。
