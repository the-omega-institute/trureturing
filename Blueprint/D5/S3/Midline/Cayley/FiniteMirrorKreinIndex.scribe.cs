using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class FiniteMirrorKreinIndexDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Midline/Cayley/FiniteMirrorKreinIndex.";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "A finite symmetric zero window has one strictly negative odd coordinate per nonfixed mirror pair and analytic multiplicity.",
            H("Finite mirror Krein index"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("finite-mirror-index-critical-criterion"),
                    DeclarationHandle.Create(Module + "finite_mirror_krein_index_zero_iff_critical"),
                    H("The finite mirror index vanishes exactly on critical windows"),
                    StatementSource.FromAuthor(Disp(Seq(
                        F.Id("kappa_T = 0"), Sp, Iff, Sp,
                        F.Id("forall n in S_T, Re(rho_n) = 1/2")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The smaller index in each two-point mirror orbit selects one representative, while multiplicity supplies the odd-coordinate fiber."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("finite-mirror-odd-sector-negative"),
                    DeclarationHandle.Create(Module + "finiteMirrorOddQuadratic_strictly_negative"),
                    H("The finite odd-sector form is strictly negative"),
                    StatementSource.FromAuthor(Disp(Seq(
                        F.Id("v != 0"), Sp, Implies, Sp,
                        F.Id("Q_T^-(v) < 0")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The odd-coordinate type has cardinality kappa_T and carries the standard negative norm-square form."))),
                    DescribeRole.Theorem))));
    }
}
