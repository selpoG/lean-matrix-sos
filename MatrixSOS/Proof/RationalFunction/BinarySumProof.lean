/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.RationalFunction.BinarySumBridge
import MatrixSOS.Proof.ComplexFunctionField.PfisterValue
import MatrixSOS.Proof.ComplexFunctionField.PolynomialReduction
import MatrixSOS.Proof.RationalFunction.LocalGlobal
import MatrixSOS.Proof.RationalHahn

/-!
Proof of the binary rational-function boundary used by the matrix SOS proof.

The downstream matrix-polynomial argument should depend on
`MatrixSOS.Proof.RationalFunction.BinarySum`, not on this file.  Replacing that
boundary file by an assumed theorem for `FracBinaryRepresentsOneStatement`
would remove the need for this proof package.
-/

open Matrix Polynomial
open scoped Matrix RatFunc

noncomputable section

namespace MatrixSOS

theorem fracPfister2ValueComplexI :
    FracPfister2ValueComplexIStatement :=
  fracPfister2ValueComplexIStatement_of_complexPolyDiagonalQuad4SquareDetIsotropicStatement
    (complexPolyDiagonalQuad4SquareDetIsotropicStatement_of_monicStatement
      (complexPolyMonicDiagonalQuad4SquareDetIsotropicStatement_of_noPairSquareStatement
        (complexPolyMonicDiagonalQuad4SquareDetNoPairSquareIsotropicStatement_of_productStatement
          (complexPolyMonicQuad4ProductSquareNoPairSquareIsotropicStatement_of_tripleProductStatement
            (complexPolyMonicTripleProductQuad4IsotropicStatement_of_noPairSquareStatement
              (complexPolyMonicTripleProductNoPairSquareQuad4Statement_of_threeNoPairSquareStatement
                (complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_projectiveQuadraticDimensionStatement
                  (complexProjectiveQuadraticDimensionStatement_of_polynomialDimensionStatement
                    (complexProjectiveQuadraticPolynomialDimensionStatement_of_homogeneousDimensionStatement
                      complexProjectiveQuadraticHomogeneousDimensionStatement_theorem)))))))))

theorem fracTernarySquareClosedLocalGlobal :
    FracTernarySquareClosedLocalGlobalStatement :=
  fracTernarySquareClosedLocalGlobalStatement_of_isotropicStatement
    (fracTernaryIsotropicSquareClosedLocalGlobalStatement_of_complexI_and_ccddNonnegWhereDefinedStatement
      fracPfister2ValueComplexI
      (fracCCDDPlainIsotropicOverSquareClosedExtensionsNonnegWhereDefinedStatement_of_strictPosNonnegWhereDefinedStatement
        fracStrictPosOverSquareClosedExtensionsNonnegWhereDefinedStatement_of_rationalHahnNonnegSquare))

theorem fracTernaryIsotropicSqAddSq : FracTernaryIsotropicSqAddSqStatement :=
  fracTernaryIsotropicSqAddSqStatement_of_squareClosedLocalGlobalStatement
    fracTernarySquareClosedLocalGlobal

theorem fracBinaryRepresentsOne_proof : FracBinaryRepresentsOneStatement :=
  fracBinaryRepresentsOneStatement_of_sqAddSqStatement
    (fracBinaryRepresentsOneSqAddSqStatement_of_ternaryIsotropicSqAddSqStatement
      fracTernaryIsotropicSqAddSq)

end MatrixSOS
