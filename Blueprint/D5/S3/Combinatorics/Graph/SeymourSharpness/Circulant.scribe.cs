using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SeymourSharpness;

internal sealed class SeymourSharpnessCirculantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SeymourSharpness/Circulant.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Short-arc modular circulants", H("Short-arc modular circulants"),
        Blocks(
            Paragraph(Text("For a positive modulus n, let t be the integer part of (n-1)/2. The relation on ZMod n has an arc from x to y exactly when the residue y-x has value between one and t. The inequality 2t<n prevents wraparound in a sum of two allowed offsets.")),
            Node("circulant-asymm", "Orientation of the circulant", "circulant_asymm",
                "The sum of two opposite positive allowed offsets would be a strictly positive integer below n representing zero modulo n, which is impossible."),
            Node("circulant-exact-second", "The interval of exact second offsets", "circulant_exact_second",
                "The literal exact second neighbors have offsets strictly greater than t and at most 2t. For an offset in this interval, the intermediate vertex with offset t supplies the two-edge witness. This includes moduli one and two, where both intervals of neighbors are empty."),
            Node("circulant-degrees", "Equal first and exact second degrees", "circulant_degrees",
                "Translation and the residue-value bijection identify the first neighborhood with the integer interval (0,t] and the exact second neighborhood with (t,2t]. Both cardinalities are t.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
