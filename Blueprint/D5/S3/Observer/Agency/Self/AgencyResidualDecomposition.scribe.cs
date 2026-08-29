using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Self;

internal sealed class AgencyResidualDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Agency/Self/AgencyResidualDecomposition."
            + "current_relation_decomposition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The current-state kernel decomposes into completed and strategy-residual pairs.",
        H("Agency Residual Decomposition"),
        Blocks(Describe.Lean(
            DescribeId.Create("agency-residual-decomposition"),
            DeclarationHandle.Create(Declaration),
            H("Agency Residual Decomposition"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Pairs collapsed by current-state observation are partitioned according to whether the strategy profile also agrees.")),
                Paragraph(Text(
                    "The two cases are the completed kernel and the hidden strategy residual, and they are logically disjoint."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("same_current_state"), Sp, Rightarrow, Sp,
            F.Id("completed_or_residual"), Dot));
}
