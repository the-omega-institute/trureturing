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
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n at least two, if all certificate values of a sigma-coordinate vector equal the same real number, the vector is zero. Augment the coordinates by the constant cosine mode. The cosine nodes at angles between zero and pi are distinct. A Chebyshev expansion of degree at most floor(n/2) that vanishes on all floor(n/2)+1 nodes is the zero polynomial. Linear independence of the Chebyshev sequence then gives injectivity of the augmented evaluation map."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interlace-face-antitone"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Fourier.face_antitone"),
                H("Certificate inclusion reverses face inclusion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If S is contained in T, every vector at which the certificates in T attain the maximum also has this property for the certificates in S. Thus the closed face for T is contained in the closed face for S."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interlace-weighted-mean"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Fourier.I_weighted_sum"),
                H("Zero weighted mean"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum of all certificate values, with weight one at zero and at the midpoint for even n and weight two elsewhere, is zero. Reflection pairs the two halves of a full period. The full-period cosine sum vanishes for every positive frequency less than n; the geometric trigonometric sum identity supplies this cancellation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interlace-value-realization"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Fourier.exists_of_I_values"),
                H("Realization of zero-mean certificate data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every n at least two, every real family on the certificate indices whose weighted mean is zero is realized by a sigma-coordinate vector. The injective square augmented cosine evaluation map is surjective by finite-dimensional linear algebra. Its weighted mean is n times the constant coordinate, so the given mean condition forces that coordinate to vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interlace-exact-face"),
                DeclarationHandle.Create("D5/S3/Arith/InterlaceFan/Fourier.exists_face_exact"),
                H("Exact maximizing certificate sets"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every nonempty proper subset S of the certificate indices is exactly the maximizing set of a nonzero vector in its closed face. Subtract the weighted average from the indicator of S, then realize the resulting data. The two resulting levels differ by one. Every index outside S has strictly smaller value than the interlace number. Together with reversal of face inclusion, this gives the face structure used in the rational-point classification."))),
                DescribeRole.Theorem))));
}
