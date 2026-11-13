using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class RadicalQuotientIsometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/RadicalQuotientIsometry.";
    private static DocumentBlock Item(string id, string declaration, string title,
        string text, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(
            LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual bilinear radical quotients and induced isometries.",
        H("Full original spaces, radicals and quotient forms"),
        Blocks(
            Item("reduced", "reduced", "The entire quotient form",
                "For every reflexive bilinear form over any field, lift the original form to the quotient by its entire kernel. No finite dimension or selected basis is assumed.", DescribeRole.Definition),
            Item("radical-map", "radical_map", "Actual isometries map full radicals",
                "Surjectivity and the full pairing-preservation law prove that every original radical maps onto the entire target radical.", DescribeRole.Theorem),
            Item("nondegenerate", "reduced_nondegenerate", "The induced form is nondegenerate",
                "Quotient induction shows that every vector annihilating the entire quotient is the zero quotient class. This includes zero spaces and degenerate original forms.", DescribeRole.Theorem),
            Item("result", "result", "Descend the entire actual isometry",
                "The radical map equality constructs a linear equivalence of full quotient spaces. Quotient induction proves exact preservation of the actual induced forms. The orthogonality profile obstruction consumes this bridge on its original adjacent lines.", DescribeRole.Definition)),
        []));
}
