using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCurrentBorcherdsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise finite signed current residues",
        H("Pointwise finite signed current residues"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentborcherds-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherds.rightTerm_finite"),
                H("Finite right residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For arbitrary integer product order, half-mode and cover exponent, both original right-residue sequences have finite pointwise support. The first sequence uses native lower truncation on the actual target. The second uses physical current upper truncation on that same target. Their bounds do not truncate a field globally."))),
                DescribeRole.Theorem),
            Paragraph(Text("The left sequence has finite support because the original source current vanishes above its state-dependent frequency bound, including arbitrary signed shifts of the source mode. Integer phase powers and generalized complex binomial coefficients remain in the residue definitions.")))));
}
