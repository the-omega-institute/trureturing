using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MeijerZeroCount;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpprilepkina2016gammaratio");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-component Gamma quotient violates the proposed comparison of interior zero counts.",
        H("The zero-count refutation"), Blocks(
            Describe.Lean(DescribeId.Create("meijer-zero-count-family"),
                DeclarationHandle.Create("D5/S3/Analytic/MeijerZeroCount/Result.family"),
                H("The counterexample family"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n and d at least two and every positive real c, set a=(n+c,n+c) and b=(c,2n+d+c). In the unit interval with endpoints excluded, Meijer's G has exactly n distinct zeros and the control function has exactly one zero. Mellin inversion identifies G with the Rodrigues kernel, whose zero count follows from Rolle's theorem and the polynomial degree. The control zero count follows from strict monotonicity of its normalized factor."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("meijer-zero-count-refutation"),
                DeclarationHandle.Create("D5/S3/Analytic/MeijerZeroCount/Result.result"),
                H("Failure of the comparison"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The proposition claim is false. Taking n=d=2 and c=1 gives nonnegative a=(3,3), b=(1,7), and sum of b(i)-a(i) equal to two, which is greater than one. The interior zero counts are two for G and one for the control function, contradicting the proposed inequality. The family theorem also exhibits arbitrarily large discrepancies while keeping two components and d=2."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("karp-prilepkina-2015-meijer-zero-count"),
                    ResolutionKind.Refuted)))));
}
