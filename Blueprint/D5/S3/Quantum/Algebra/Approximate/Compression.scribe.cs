using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Approximate;

internal sealed class CompressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A convergent inverse-square-root Taylor series corrects an almost involution in an associative Banach algebra.",
        H("Taylor correction of compression operators"),
        Blocks(
            Paragraph(Text("Let A be a complete real normed associative algebra with norm-one identity. For an operator T with norm of T squared minus identity strictly less than one, define S by the Taylor series of (1+z) to the power minus one half, evaluated at T squared minus identity. The corrected compression is one half of the sum of identity and TS. This is the construction in Kitaev, Almost-idempotent quantum channels and approximate C*-algebras, arXiv:2405.02434v2, equations (3.4)-(3.6) and (7.1).")),
            Describe.Lean(
                DescribeId.Create("taylor-compression-idempotent"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/Compression.correction_idempotent"),
                H("The Taylor compression is idempotent"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("T"), InMacro, Sp, F.Id("A"), Comma, Sp,
                    Vert, Sp, F.Id("T"), Caret, Grp(D(2)), Minus, D(1), Vert, Sp, Lt, D(1),
                    Sp, Implies, Sp,
                    Call("correction", F.Id("T")), Caret, Grp(D(2)), Eq,
                    Call("correction", F.Id("T"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Absolute convergence follows by comparison with the scalar binomial series. Its Cauchy product is evaluated by the Chu-Vandermonde identity, giving S squared equal to the geometric series in identity minus T squared. The geometric-series identity gives T squared times S squared equal to identity. Commutation then proves exact idempotence.")),
                    Paragraph(Text("The intended algebra A is the associative algebra of continuous linear endomorphisms. No multiplication instance is imposed on the nonassociative target space. This result supplies the analytic correction after the operator smallness estimate has been proved; it does not supply mixed-corner saturation, the corrected matrix action, or a matrix-block extension."))),
                DescribeRole.Theorem))));
}
