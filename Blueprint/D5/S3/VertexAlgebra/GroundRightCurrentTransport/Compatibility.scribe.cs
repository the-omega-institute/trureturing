using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GroundRightCurrentTransport;

internal sealed class CompatibilityDocument : IScribeDocumentDefinition
{

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite inverse recovery and signed coefficient propagation",
        H("Finite inverse recovery and signed coefficient propagation"),
        Blocks(
            Paragraph(Text("The source sequence U(r) and the two target fields A,B remain independent. The left coefficient is choose(p+s/2,j) U(r+j)[p+q-j]x. The first ordered coefficient is (-1)^j choose(r,j) A[p+r-j]B[q+j]x; the second retains the signed factor (-1)^r and the reversed composition B[q+r-j]A[p+j]x.")),
            Paragraph(Text("The three sequences have separate finite supports: the source tail in r+j, the lower truncation of B on x, and the lower truncation of A on x. A common finite cutoff is used only after both the original source tail and complete-residue tail have been certified. Convolution by choose(s/2,j) and choose(-s/2,j) cancels via the accepted finite convolution theorem, including every signed shift s.")),
            Paragraph(Text("The p=0 identity is equivalent to the inverse-residue equality. The discrepancy satisfies E(p+1,q,r)=E(p,q+1,r)+E(p,q,r+1), with each finite support retained. Uniform shifted locality gives a high-r seed at every signed p. Nonnegative p induction and the nested negative-p, high-r-distance induction recover every signed p,q,r. Conversely, the p=0 full law recovers the exact inverse product. Both directions are consumed by Propagation.")))));
}
