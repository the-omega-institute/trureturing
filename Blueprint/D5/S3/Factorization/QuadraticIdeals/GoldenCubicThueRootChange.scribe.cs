using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicThueRootChangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A monic companion gives exact local readouts without changing the generated Thue field.",
        H("Rational root change and local arithmetic of the native Thue cubic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-thue-monic-root"),
                DeclarationHandle.Create("D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.monic_root"),
                H("The squared depressed root satisfies the monic equation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "After depressing the cubic, square the root and divide by the role prime. "
                    + "This gives the new monic cubic without choosing any roots of unity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-thue-simple-field-unchanged"),
                DeclarationHandle.Create("D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.same_simple_field"),
                H("The monic root generates the same simple field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An explicit rational inverse recovers the original coordinate. "
                    + "The generated intermediate fields therefore agree exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-thue-chart-two-derivative"),
                DeclarationHandle.Create("D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.binary_form_mod_two_chart_derivative"),
                H("Both affine charts have unit derivative modulo two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Odd primary coordinates reduce the homogeneous form to the product "
                    + "of the three distinct projective linear factors over F₂. "
                    + "Either chart then gives a polynomial with derivative one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-thue-polynomial-local-depths"),
                DeclarationHandle.Create("D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange.discriminant_arithmetic_depths"),
                H("Exact valuation of the polynomial discriminant expression"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the stated local-unit conditions, the polynomial discriminant expression "
                    + "has valuation two at the role prime and four at three. "
                    + "Field-discriminant and maximal-order claims are separate."))),
                DescribeRole.Theorem))));
}
