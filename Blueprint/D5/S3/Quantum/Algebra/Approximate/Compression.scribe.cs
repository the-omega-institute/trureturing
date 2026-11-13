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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("taylor-compression-closeness"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/Compression.correction_closeness"),
                H("The Taylor correction is close to the midpoint"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("T"), InMacro, Sp, F.Id("A"), Comma, Sp,
                    Call("norm", Seq(Call("correction", F.Id("T")), Minus,
                        Multiply(new Formula.Fraction(D(1), D(2)),
                            Seq(Open, D(1), Plus, F.Id("T"), Close)))), Sp,
                    Le, Sp, Multiply(Multiply(new Formula.Fraction(D(1), D(2)),
                        Call("norm", F.Id("T"))),
                        Call("norm", Seq(Call("inverseSqrt", Seq(F.Id("T"), Caret,
                            Grp(D(2)), Minus, D(1))), Minus, D(1)))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The correction differs from the uncorrected midpoint by one half of T "
                        + "times the inverse-square-root Taylor tail. Submultiplicativity gives "
                        + "the displayed bound without adding any structure to the target space."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("taylor-tail-linear"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/Compression.inverseSqrt_tail_linear"),
                H("A linear bound for the Taylor tail"),
                StatementSource.FromAuthor(Disp(Seq(Call("norm", Seq(Call("inverseSqrt", F.Id("d")), Minus, D(1))), Le, Call("norm", F.Id("d"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In every complete real normed associative algebra with norm-one identity, if the norm of d is at most one half, then the norm of the inverse-square-root Taylor tail is at most the norm of d. The coefficients are identified with the already established central-binomial coefficients in OriginalHalfBinomialIntegral.b_multichoose. Its binomial_hasSum gives the scalar majorant 1/sqrt(1-norm(d))-1. This is at most norm(d) on the stated interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("taylor-intertwines"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/Approximate/Compression.correction_intertwines"),
                H("Taylor correction preserves real intertwiners"),
                StatementSource.FromAuthor(Disp(Seq(Call("s", Call("correction", F.Id("T")), F.Id("x")), Eq, Call("correction", F.Id("U"), Call("s", F.Id("x")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let E and F be complete nontrivial complex normed spaces, s a continuous real-linear map from E to F, and T and U continuous complex-linear endomorphisms. If s(Tx)=U(sx) for every x, and both square defects have norm strictly less than one, then the same intertwining identity holds for their Taylor corrections. The proof transports the convergent series term by term; it applies to the actual conjugate-linear star symmetry without imposing an associative algebra structure on H."))),
                DescribeRole.Theorem)))));
}
