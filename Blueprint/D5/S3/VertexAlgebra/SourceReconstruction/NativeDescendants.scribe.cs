using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SourceReconstruction;

internal sealed class NativeDescendantsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-order native triangular descendant recurrence",
        H("All-order native triangular descendant recurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-nativedescendants-nativeFirst-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/NativeDescendants.nativeFirst_finite"),
                H("The actual first native term is pointwise finite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original Ytw lower truncation gives finite support before multiplication by the natural binomial coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-nativedescendants-nativeSecond-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/NativeDescendants.nativeSecond_finite"),
                H("The actual second native term is pointwise finite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual tensor-current truncation bounds the nonnegative current on the arbitrary target vector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-nativedescendants-nativeCorrection-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/NativeDescendants.nativeCorrection_finite"),
                H("The actual correction term is pointwise finite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Original source-current truncation bounds the correction states before the half-binomial is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcereconstruction-nativedescendants-native-descendant"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SourceReconstruction/NativeDescendants.native_descendant"),
                H("Isolating degree zero of the completed current identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The actual signed current Borcherds identity is evaluated at order -d-1 and mode zero. Splitting its left degree-zero term gives first cover exponent E+1-2j, second exponent E+2d+3+2j, and correction exponent E+2j+2. The second term has phase (-1)^d. The correction coefficient is choose(1/2,j+1). All indices and casts are proved in Lean. This identity is consumed by the finite natural-weight reconstruction, not asserted as arbitrary-first-source twisted Jacobi."))),
                DescribeRole.Theorem))));
}
