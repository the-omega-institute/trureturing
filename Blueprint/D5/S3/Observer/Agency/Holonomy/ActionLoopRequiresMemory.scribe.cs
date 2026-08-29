using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Holonomy;

internal sealed class ActionLoopRequiresMemoryDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Agency/Holonomy/ActionLoopRequiresMemory."
            + "policy_change_implies_memory_change";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A policy-visible loop effect requires nontrivial memory transport.",
        H("Action Loop Requires Memory Transport"),
        Blocks(Describe.Lean(
            DescribeId.Create("action-loop-requires-memory"),
            DeclarationHandle.Create(Declaration),
            H("Action Loop Requires Memory Transport"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Holonomy acts on memory after an observer traverses an action loop.")),
                Paragraph(Text(
                    "If the resulting policy action changes, the transported memory could not have remained fixed."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("policy_changes_after_loop"), Sp, Rightarrow, Sp,
            F.Id("memory_changes_after_loop"), Dot));
}
