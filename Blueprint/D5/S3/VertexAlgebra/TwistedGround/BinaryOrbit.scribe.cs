using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class BinaryOrbitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary Weyl actions yield a nonzero projector and a complete character orbit.",
        H("A Nonzero Character Orbit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binaryorbit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/BinaryOrbit.orbit_independent"),
                H("A Nonzero Character Orbit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For binary halves x and y, let E_x and F_y satisfy the binary group laws and F_y E_x=(-1)^(dot(y,x)) E_x F_y. These are operator hypotheses, not an assumed nonzero vector or an assumed equivalence. The character projector P_t is 2^(-n) times the sum of (-1)^(dot(y,t)) F_y.")),
                    Paragraph(Text("A translation by one coordinate flips any nontrivial binary character, so its complete character sum is zero. The trivial character sum is 2^n. Nonzero-charge trace vanishing and dimension 2^n therefore give trace(P_0)=1. A nonzero image vector is derived from this trace, rather than assumed.")),
                    Paragraph(Text("Each E_x P_0 v has F-character x. The projectors isolate these vectors in any finite linear combination, and invertibility of E_x proves every orbit vector nonzero. The orbit is independent; when dimension is 2^n, its basis also spans the entire original carrier."))),
                DescribeRole.Theorem))));
}
