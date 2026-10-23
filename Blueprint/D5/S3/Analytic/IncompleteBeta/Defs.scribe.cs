using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.IncompleteBeta;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Definitions for the coefficient form of the incomplete beta conjecture.",
        H("Incomplete beta coefficients"), Blocks(
            Describe.Lean(DescribeId.Create("incomplete-beta-coeff"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta.coeff"),
                H("Gamma coefficient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient indexed by j is Gamma(a+b+j) divided by Gamma(b) times Gamma(a+j+1)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("incomplete-beta-phi"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta.phi"),
                H("Coefficient difference"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The nth coefficient difference is the finite convolution difference obtained from two parameter shifts."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("incomplete-beta-claim"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBeta.claim"),
                H("Positivity claim"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive real parameters, every finite coefficient difference is positive."))),
                DescribeRole.Theorem))));
}
