using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource.LogDet;

internal sealed class PathSpectralClassicalDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/Resource/LogDet/PathSpectralClassical.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The log-determinant divergence has matching path, spectral, geometric-kernel, and classical forms.",
        H("Path and Spectral Forms of the Log-Determinant Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("trace-cfc-eigenvalue-sum"),
                DeclarationHandle.Create(LeanPrefix + "trace_cfc_eq_sum"),
                H("The trace of functional calculus is the eigenvalue sum"),
                StatementSource.FromAuthor(TraceCfcFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a Hermitian complex matrix on any finite carrier and any real-valued "
                        + "function, the real part of the trace of its Hermitian functional "
                        + "calculus is the sum of the function over the matrix eigenvalues. "
                        + "Unitary diagonalization and cyclicity of trace give the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-log-det-divergence-has-path-spectral-kernel-and-classical-forms"),
                DeclarationHandle.Create(LeanPrefix + "log_det_path_spectral_classical"),
                H("The log-det divergence has path, spectral, kernel, and classical forms"),
                StatementSource.FromAuthor(PathSpectralClassicalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive-definite complex matrices, the divergence is the weighted "
                            + "trace energy along their affine segment. Congruence by the inverse "
                            + "positive square root of sigma gives a positive-definite relative "
                            + "matrix whose eigenvalues yield the same divergence through the "
                            + "profile h(t) = t - log(t) - 1.")),
                    Paragraph(Text(
                        "For positive scalar arguments, the reciprocal-product kernel is exactly "
                            + "the square of half the geometric kernel. Restricting the matrices to "
                            + "positive real diagonals gives the coordinatewise Itakura-Saito sum.")),
                    Paragraph(Text(
                        "The proof derives the scalar integral by an explicit antiderivative, "
                            + "uses Hermitian functional calculus for the matrix path, and applies "
                            + "the trace and determinant eigenvalue formulas for the spectral form."))),
                DescribeRole.Theorem))));

    private static Formula TraceCfcFormula()
    {
        Formula n = F.Id("n"), a = F.Id("A"), h = F.Id("h"), f = F.Id("f"), i = F.Id("i");
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula complex = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        Formula body = F.Seq(
            Call("re", Call("trace", Call("cfc", f, a))), F.Sp, F.Eq, F.Sp,
            F.Sum, F.Underscore, F.Grp(i, F.Colon, n), F.Sp,
            new Formula.Apply(f, [Call("eigenvalues", h, i)]));
        body = All("f", Parenthesized(F.Seq(real, F.Sp, F.To, F.Sp, real)), body);
        body = All("h", Call("IsHermitian", a), body);
        body = All("A", Call("Matrix", n, n, complex), body);
        return F.Disp(All("n", F.Seq(F.Operatorname, F.Grp(F.Id("Type"))),
            F.Seq(F.OpenBracket, Call("Fintype", n), F.CloseBracket, F.Sp,
                F.OpenBracket, Call("DecidableEq", n), F.CloseBracket, F.Sp, body)));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Seq(F.Operatorname, F.Grp(F.Id(name))), [.. arguments]);

    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);

    private static Formula PathSpectralClassicalFormula() => F.Disp(F.Seq(
        F.Begin, F.Grp(F.Id("gathered")),
        F.Id("n"), F.Sp, F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id("N")),
        F.Comma, F.Quad, F.Rho, F.Comma, F.Sp, F.SigmaLower,
        F.Sp, F.InMacro, F.Sp, MatrixSpace(), F.Comma, F.Sp,
        PosDef(F.Rho), F.Sp, F.Land, F.Sp, PosDef(F.SigmaLower),
        F.Sp, F.Longrightarrow, F.Sp, F.RowBreak, F.Sp,
        F.Open,
        LogDet(F.Rho, F.SigmaLower), F.Sp, F.Eq, F.Sp,
        F.Int, F.Underscore, F.Grp(F.D(0)), F.Caret, F.Grp(F.D(1)),
        F.Open, F.D(1), F.Minus, F.Id("s"), F.Close, F.Sp,
        F.Re, F.Grp(
            F.Operatorname, F.Grp(F.Id("tr")), F.Open,
            F.Open, Inverse(Segment()), F.Sp, F.Delta, F.Close,
            F.Caret, F.Grp(F.D(2)), F.Close),
        F.Sp, F.Id("d"), F.Id("s"), F.Comma, F.Sp,
        Segment(), F.Sp, F.Eq, F.Sp,
        F.Open, F.D(1), F.Minus, F.Id("s"), F.Close, F.SigmaLower,
        F.Sp, F.Plus, F.Sp, F.Id("s"), F.Rho, F.Comma, F.Sp,
        F.Delta, F.Sp, F.Eq, F.Sp, F.Rho, F.Sp, F.Minus, F.Sp, F.SigmaLower,
        F.Close, F.Sp, F.Land, F.Sp, F.RowBreak, F.Sp,
        F.Open,
        LogDet(F.Rho, F.SigmaLower), F.Sp, F.Eq, F.Sp,
        F.Sum, F.Underscore, F.Grp(F.Id("i")), F.Sp,
        F.Id("h"), F.Open, F.Lambda, F.Underscore, F.Grp(F.Id("i")), F.Close,
        F.Comma, F.Sp,
        F.Open, F.Lambda, F.Underscore, F.Grp(F.Id("i")), F.Close,
        F.Underscore, F.Grp(F.Id("i")), F.Sp, F.Eq, F.Sp,
        F.Operatorname, F.Grp(F.Id("spec")), F.Open,
        InverseSqrt(F.SigmaLower), F.Sp, F.Rho, F.Sp, InverseSqrt(F.SigmaLower),
        F.Close, F.Comma, F.Sp,
        F.Id("h"), F.Open, F.Id("t"), F.Close, F.Sp, F.Eq, F.Sp,
        F.Id("t"), F.Sp, F.Minus, F.Sp,
        F.Operatorname, F.Grp(F.Id("log")), F.Open, F.Id("t"), F.Close,
        F.Sp, F.Minus, F.Sp, F.D(1), F.Close,
        F.Sp, F.Land, F.Sp, F.RowBreak, F.Sp,
        F.Open,
        F.Forall, F.Sp, F.Id("a"), F.Comma, F.Sp, F.Id("b"), F.Sp, F.Gt, F.Sp, F.D(0),
        F.Comma, F.Quad, F.Frac, F.Grp(F.D(1)), F.Grp(F.Id("a"), F.Id("b")),
        F.Sp, F.Eq, F.Sp,
        F.Open, F.Frac,
        F.Grp(F.Id("k"), F.Underscore, F.Grp(F.Id("G")),
            F.Open, F.Id("a"), F.Comma, F.Sp, F.Id("b"), F.Close),
        F.Grp(F.D(2)), F.Close, F.Caret, F.Grp(F.D(2)), F.Comma, F.Sp,
        F.Id("k"), F.Underscore, F.Grp(F.Id("G")),
        F.Open, F.Id("a"), F.Comma, F.Sp, F.Id("b"), F.Close,
        F.Sp, F.Eq, F.Sp,
        F.Frac, F.Grp(F.D(2)), F.Grp(F.Sqrt, F.Grp(F.Id("a"), F.Id("b"))),
        F.Close, F.Sp, F.Land, F.Sp, F.RowBreak, F.Sp,
        F.Open,
        F.Forall, F.Sp, F.Id("p"), F.Comma, F.Sp, F.Id("q"),
        F.Sp, F.InMacro, F.Sp,
        F.Mathbb, F.Grp(F.Id("R")), F.Caret, F.Grp(F.Id("n")), F.Comma, F.Quad,
        F.Open, F.Forall, F.Sp, F.Id("i"), F.Comma, F.Sp,
        F.D(0), F.Sp, F.Lt, F.Sp,
        F.Id("p"), F.Underscore, F.Grp(F.Id("i")), F.Sp, F.Land, F.Sp,
        F.D(0), F.Sp, F.Lt, F.Sp,
        F.Id("q"), F.Underscore, F.Grp(F.Id("i")), F.Close,
        F.Sp, F.Longrightarrow, F.Sp,
        LogDet(Diagonal(F.Id("p")), Diagonal(F.Id("q"))),
        F.Sp, F.Eq, F.Sp,
        F.Sum, F.Underscore, F.Grp(F.Id("i")),
        F.Open,
        F.Frac, F.Grp(F.Id("p"), F.Underscore, F.Grp(F.Id("i"))),
            F.Grp(F.Id("q"), F.Underscore, F.Grp(F.Id("i"))),
        F.Sp, F.Minus, F.Sp,
        F.Operatorname, F.Grp(F.Id("log")), F.Open,
        F.Frac, F.Grp(F.Id("p"), F.Underscore, F.Grp(F.Id("i"))),
            F.Grp(F.Id("q"), F.Underscore, F.Grp(F.Id("i"))),
        F.Close, F.Sp, F.Minus, F.Sp, F.D(1), F.Close,
        F.Close, F.Sp, F.End, F.Grp(F.Id("gathered"))));

    private static Formula LogDet(Formula left, Formula right) => F.Seq(
        F.Operatorname, F.Grp(F.Id("logDetDivergence")), F.Open,
        left, F.Comma, F.Sp, right, F.Close);

    private static Formula PosDef(Formula matrix) => F.Seq(
        F.Operatorname, F.Grp(F.Id("PosDef")), F.Open, matrix, F.Close);

    private static Formula Inverse(Formula matrix) => F.Seq(
        matrix, F.Caret, F.Grp(F.Minus, F.D(1)));

    private static Formula InverseSqrt(Formula matrix) => F.Seq(
        matrix, F.Caret, F.Grp(F.Minus, F.Frac, F.Grp(F.D(1)), F.Grp(F.D(2))));

    private static Formula Diagonal(Formula vector) => F.Seq(
        F.Operatorname, F.Grp(F.Id("diag")), F.Open, vector, F.Close);

    private static Formula Segment() => F.Seq(
        F.Id("m"), F.Underscore, F.Grp(F.Id("s")));

    private static Formula MatrixSpace() => F.Seq(
        F.Id("M"), F.Underscore, F.Grp(F.Id("n")), F.Open,
        F.Mathbb, F.Grp(F.Id("C")), F.Close);
}
