using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class CanonicalZetaMirrorEvenOddDecompositionDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Midline/Cayley/CanonicalZetaMirrorEvenOddDecomposition.";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Normalized mirror spectral projections split the Krein form into even positive energy minus odd positive energy.",
            H("Canonical mirror even-odd decomposition"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("mirror-even-odd-projections-orthogonal"),
                    DeclarationHandle.Create(Module + "mirror_even_odd_inner_eq_zero"),
                    H("Mirror parity sectors are Hilbert orthogonal"),
                    StatementSource.FromAuthor(Disp(Seq(
                        F.Id("<P_+ psi,P_- phi>"), Sp, EqualTo, Sp, D(0)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The proof uses the self-adjoint involution laws rather than introducing an abstract orthogonal decomposition axiom."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("mirror-krein-energy-decomposition"),
                    DeclarationHandle.Create(Module + "mirrorKreinForm_re_eq_even_norm_sq_sub_odd_norm_sq"),
                    H("The Krein form is even energy minus odd energy"),
                    StatementSource.FromAuthor(Disp(Seq(
                        F.Id("Re[psi,psi]_J"), Sp, EqualTo, Sp,
                        F.Id("||P_+ psi||^2 - ||P_- psi||^2")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The normalized projections are idempotent, mutually annihilating, and reconstruct every vector."))),
                    DescribeRole.Theorem))));
    }
}
