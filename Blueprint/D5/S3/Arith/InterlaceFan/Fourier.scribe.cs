using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.InterlaceFan;

internal sealed class FourierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cosine coordinates for the interlace fan.",
        H("Evaluation and closed faces"), Blocks(
            Describe.Lean(DescribeId.Create("interlace-constant-values-zero"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Fourier.eq_zero_of_I_const"),
                H("Constant certificate values force the zero vector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic")),
                Blocks(Paragraph(Text("For n at least two, if all certificate values of a sigma-coordinate vector equal the same real number, the vector is zero. Augment the coordinates by the constant cosine mode. The cosine nodes at angles between zero and pi are distinct. A Chebyshev expansion of degree at most floor(n/2) that vanishes on all floor(n/2)+1 nodes is the zero polynomial. Linear independence of the Chebyshev sequence then gives injectivity of the augmented evaluation map."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interlace-face-antitone"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Fourier.face_antitone"),
                H("Certificate inclusion reverses face inclusion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("mathlib/module/Mathlib.Data.Finset.Max")),
                Blocks(Paragraph(Text("If S is contained in T, every vector at which the certificates in T attain the maximum also has this property for the certificates in S. Thus the closed face for T is contained in the closed face for S."))),
                DescribeRole.Theorem))));
}
