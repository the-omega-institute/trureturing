using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Mordell;

internal sealed class PointVariableChangeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/tauceti2026canonicalheight");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elliptic point groups under a variable change.",
        H("Elliptic point groups under a variable change"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("point-variable-change"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/PointVariableChange.equivVariableChange"),
                H("Elliptic point groups under a variable change"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For an elliptic Weierstrass curve W over a field and an admissible variable change C with nonzero scale, the coordinate transformation induces an additive equivalence from the nonsingular point group of C acting on W to the point group of W. The equivalence includes infinity.")),
                    Paragraph(Text("The coordinate and derivative identities preserve the curve equation and nonsingularity. The inverse change supplies the inverse map. The finite-point addition, doubling and negation identities prove preservation of the point group law."))),
                DescribeRole.Definition))));
}
