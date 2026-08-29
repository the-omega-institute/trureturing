using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Holonomy;

internal sealed class HolonomyCompositionInvarianceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Agency/Holonomy/HolonomyCompositionInvariance."
            + "invisible_transports_compose";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Policy-invisible memory transports are closed under composition.",
        H("Holonomy Composition Invariance"),
        Blocks(Describe.Lean(
            DescribeId.Create("holonomy-composition-invariance"),
            DeclarationHandle.Create(Declaration),
            H("Holonomy Composition Invariance"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Policy invisibility means that a memory transport leaves every policy readout unchanged.")),
                Paragraph(Text(
                    "Two invisible transports remain invisible when composed, and identity transport is invisible."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("first_and_second_invisible"), Sp, Rightarrow, Sp,
            F.Id("composite_invisible"), Dot));
}
