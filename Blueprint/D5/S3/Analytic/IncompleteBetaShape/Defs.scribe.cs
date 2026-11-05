using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.IncompleteBetaShape;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karp2016incompletebeta");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient inequalities for real shifts of the first incomplete beta parameter.",
        H("First parameter coefficient differences"), Blocks(
            Describe.Lean(DescribeId.Create("incomplete-beta-shape-psi"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBetaShape/Defs.psi"),
                H("Coefficient difference"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The nth coefficient is the sum, for k from zero to n, of c_k(a+alpha,b)c_(n-k)(a+beta,b) minus c_k(a,b)c_(n-k)(a+alpha+beta,b). The Gamma coefficient c is reused from the incomplete beta coefficient definitions. By the series expansion and product identity, this is the coefficient of x^n after division of the product difference by x^(2a+alpha+beta)(1-x)^(2b). It is independent of x, so the source's restriction on x imposes no further condition on the coefficient."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("incomplete-beta-shape-claim"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBetaShape/Defs.claim"),
                H("Strict signs for positive real shifts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every positive a, b, alpha and beta and every natural n, the coefficient difference is negative when b is less than one and positive when b is greater than one."))),
                DescribeRole.Definition))));
}
