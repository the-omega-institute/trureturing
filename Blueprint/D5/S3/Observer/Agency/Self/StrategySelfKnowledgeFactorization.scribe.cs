using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Self;

internal sealed class StrategySelfKnowledgeFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Agency/Self/StrategySelfKnowledgeFactorization."
            + "factorization_refines_strategy_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strategy self-knowledge factorization refines the current-state observation kernel.",
        H("Strategy Self-Knowledge Factorization"),
        Blocks(Describe.Lean(
            DescribeId.Create("strategy-self-knowledge-factorization"),
            DeclarationHandle.Create(Declaration),
            H("Strategy Self-Knowledge Factorization"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A strategy profile is self-visible when it factors through the current observer state.")),
                Paragraph(Text(
                    "Under this factorization, equal current states necessarily have equal strategies, so pairing adds no separation."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("strategy_factors_through_current"), Sp, Rightarrow, Sp,
            F.Id("current_kernel_refines_strategy_kernel"), Dot));
}
