using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class AgohCoefficientReadoutTemplateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three indexed readings of signed coefficient codes.",
        H("Three coefficient-code cuts"),
        Blocks(
            Node("coefficientSignature", "The signature has three CUT indices, each returning "
                + "a code in Fin(9), and no anchors. Codes can represent real coefficients "
                + "from -4 through 4 by subtracting four.", DescribeRole.Definition),
            Node("coefficientRealization", "The supplied coefficient reader is evaluated at "
                + "the state and the selected index. Its full word is available through "
                + "the three readings; no proposition or theorem is stored in the reader.",
                DescribeRole.Definition))));

    private static DocumentBlock Node(string name, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("agoh-coefficient-" + name.ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/AgohCoefficientReadoutTemplate." + name),
        H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);
}
