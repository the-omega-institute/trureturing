using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Self;

internal sealed class AgencyCompletionMinimalityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Agency/Self/AgencyCompletionMinimality."
            + "paired_completion_factors_through_summary";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Componentwise recoverability induces recoverability of the paired agency completion.",
        H("Agency Completion Minimality"),
        Blocks(Describe.Lean(
            DescribeId.Create("agency-completion-minimality"),
            DeclarationHandle.Create(Declaration),
            H("Agency Completion Minimality"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The current observer state and the strategy profile are treated as the two coordinates of agency completion.")),
                Paragraph(Text(
                    "Any summary that reconstructs both coordinates also reconstructs their pair through a canonical pairing map."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("component_factorizations"), Sp, Rightarrow, Sp,
            F.Id("paired_factorization"), Dot));
}
