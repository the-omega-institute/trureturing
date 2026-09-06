using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class CanonicalZetaMirrorFundamentalSymmetryDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Midline/Cayley/CanonicalZetaMirrorFundamentalSymmetry.";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The same-height zeta-zero mirror lifts to an involutive self-adjoint isometry with explicit negative odd directions.",
            H("Canonical zeta mirror fundamental symmetry"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("mirror-fundamental-symmetry-self-adjoint"),
                    DeclarationHandle.Create(Module + "mirrorFundamentalSymmetry_inner_left"),
                    H("The mirror is self-adjoint in inner-product form"),
                    StatementSource.FromAuthor(Disp(F.Id("<J psi,phi> = <psi,J phi>"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The multiplicity-preserving mirror permutation is represented by the repository's ell-two reindexing linear isometry."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("mirror-odd-vector-negative"),
                    DeclarationHandle.Create(Module + "mirror_odd_vector_strictly_negative"),
                    H("Every moved mirror coordinate gives a strict negative direction"),
                    StatementSource.FromAuthor(Disp(Seq(
                        F.Id("M(v) != v"), Sp, Implies, Sp,
                        F.Id("[v_-,v_-]_J < 0")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Antisymmetrizing a coordinate basis vector produces a nonzero minus-one eigenvector of the mirror."))),
                    DescribeRole.Theorem))));
    }
}
