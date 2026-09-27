using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class MultiplicativeSliceParametersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multiplicative Slice Parameters.",
        H("Multiplicative Slice Parameters"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("multiplicative-slice-parameters-forcedequations"),
                DeclarationHandle.Create("D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.ForcedEquations"),
                H("The coefficient equations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all positive integers m and n, the coefficients satisfy (1 - p(m))(1 - p(n))c(m,n) = 1 - p(m+n) and p(m)p(n)c(m,n) = -p(m+n)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("multiplicative-slice-parameters-geometricfamily"),
                DeclarationHandle.Create("D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.GeometricFamily"),
                H("The geometric family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A real parameter t different from 1 and -1 gives p(m) = t^m/(t^m - 1) and c(m,n) = -((t^m - 1)(t^n - 1))/(t^(m+n) - 1) at positive indices. The parameter zero gives p(m) = 0 and c(m,n) = 1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("multiplicative-slice-parameters-unitfamily"),
                DeclarationHandle.Create("D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.UnitFamily"),
                H("The unit family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every positive index p(m) = 1, and at every pair of positive indices c(m,n) = -1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("multiplicative-slice-parameters-result"),
                DeclarationHandle.Create("D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters.result"),
                H("Exhaustive classification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two coefficient equations hold if and only if the coefficients belong to the geometric family or the unit family. Any zero entry at a positive index forces all positive entries of p to be zero; any unit entry forces them all to be one. In every other case all positive entries avoid both zero and one. Values at index zero are unrestricted."))),
                DescribeRole.Theorem))));
}
