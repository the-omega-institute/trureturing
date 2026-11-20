using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Polynomials;

internal sealed class ComplexPolynomialCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Algebra/Polynomials/ComplexPolynomialCoefficients";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, "Real and imaginary coefficient projections commute with evaluation on real inputs.",
            "evidence-not-specified-by-formal-manifest",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Algebra.MvPolynomial.Eval")),
        H("Real and imaginary coefficients of multivariate polynomials"),
        Blocks(Describe.Lean(DescribeId.Create("complex-polynomial-coefficient-evaluation"),
            DeclarationHandle.Create(Module + ".coefficient_eval"),
            H("Evaluation of the coefficient projections"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Taking real and imaginary parts coefficientwise gives two real polynomials. After extending the coefficients to the complex numbers, their sum with the imaginary projection multiplied by the imaginary unit recovers the original polynomial. At real inputs the two projections evaluate to the real and imaginary parts of the original evaluation."))),
            DescribeRole.Theorem))));
}
