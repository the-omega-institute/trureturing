using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMCoefficientTreeBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMCoefficientTreeBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sound recursive amplitude checking for the original coefficient-tree interpreter.",
        H("Every stored coefficient and every missing-key return is bounded"),
        Blocks(
            Paragraph(Text("The checker visits both children of every node and compares the absolute value of each stored integer coefficient with the proposed bound. Empty nodes check that the bound also covers zero, since zero is the original lookup's return for an absent key. The induction follows the original interpreter's equality and ordering branches; it needs neither sorted keys nor a completeness assertion about outcome orbits.")),
            Describe.Lean(DescribeId.Create("lookup-amplitude"),
                DeclarationHandle.Create(Prefix + "checked_get_abs_bound"),
                H("A full-tree check bounds every lookup"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer bound and arbitrary coefficient tree, acceptance of the recursive absolute-value check bounds the original lookup at every natural-number key. This is the generic soundness step used by the concrete EJM coefficient amplitude receipts; acceptance of those actual trees is a separate kernel computation."))),
                DescribeRole.Theorem))));
}
