using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform;

internal sealed class SpectrumCompressionDocument : IScribeDocumentDefinition
{
    private static Formula Int(long n) => n < 0
        ? new Formula.Negate(Num(-n)) : Num(n);
    private static Formula Tuple(IEnumerable<Formula> xs) =>
        Seq(Open, Seq(xs.SelectMany((v, i) => i == 0
            ? new[] { v } : new[] { Comma, v }).ToArray()), Close);
    private static Formula MatrixStatement()
    {
        int[][] rows = [
            [-1,-2,-3,-3,-3,-3,-3,-3,-3,-3,-2,-1,0,1,2,3],
            [-1,-2,-3,-4,-5,-6,-5,-4,-3,-2,-1,0,1,2,3,4],
            [-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,0,1,2]];
        Formula Fin(int n) => new Formula.Apply(F.Id("Fin"), [Int(n)]);
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var matrix = new Formula.Apply(F.Id("Matrix"), [Fin(3), Fin(16), real]);
        return Seq(F.Id("A"), Colon, matrix, F.Eq,
            Tuple(rows.Select(row => Tuple(row.Select(v => Int(v))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometry of spectral compression.",
        H("Geometry of spectral compression"), Blocks(
            Paragraph(Text("The real matrix A has rows (-1,-2,-3,-3,-3,-3,-3,-3,-3,-3,-2,-1,0,1,2,3), " +
                    "(-1,-2,-3,-4,-5,-6,-5,-4,-3,-2,-1,0,1,2,3,4), and " +
                    "(-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,0,1,2). All sixteen slots are retained.")),
            Describe.Lean(DescribeId.Create("appt-quadbit-spectrumcompression-a"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A"),
                H("Three boundary rows"), StatementSource.FromAuthor(Disp(MatrixStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A has three rows and sixteen ordered gap slots. Its minus-identity slack block retains " +
                    "every original row equation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("appt-quadbit-spectrumcompression"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.positions_strict"),
                H("Ordered boundary and middle positions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural N at least 67 and middle position j from 6 through N-10, " +
                    "the sixteen natural step positions 1,2,3,4,5,j,N-9 through N are strictly increasing. " +
                    "These positions and A are shared by the exact ray moments, the cofactor checker and " +
                    "the spectrum compression proof. The latter remains with the scalar endpoint and " +
                    "handles positive middle mass by barycentric weights and zero middle mass without division."))), DescribeRole.Theorem),
            Paragraph(Text("These statements concern real scalar spectra and finite cofactor certificates. Connecting " +
                    "the boundary inequalities to a physical APPT model, constructing an attaining state, and " +
                    "determining a purity supremum require additional results.")))));
}
