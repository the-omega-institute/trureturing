using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class FiniteFreeCoproductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/FiniteFreeCoproduct.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite coordinates for an integer coproduct.", H("Finite coordinates for an integer coproduct"), Blocks(
            Node("coordinateiso", "coordinateIso", "Concrete finite coordinates",
                "For decidable types I and J with I finite and a bijection e from I to J, the categorical coproduct of copies of the integer module indexed by J is isomorphic to integer-valued functions on I. The construction uses the concrete finitely supported coproduct cocone, reindexes by e, and passes to finite function coordinates.", DescribeRole.Definition),
            Node("iota-coordinate-iso", "\u03b9_coordinateIso", "Every summand inclusion",
                "For every j in J, the summand map followed by the coordinate isomorphism sends z to the function equal to z at the unique i with e(i)=j and zero elsewhere. This identifies the actual categorical inclusion with the finite basis map.", DescribeRole.Theorem),
            Node("coordinateiso-basis", "coordinateIso_basis", "Standard basis vectors",
                "For each i in I, one in the e(i) summand maps to Pi.single i 1. The formula identifies the basis vectors in the signed boundary comparisons.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
