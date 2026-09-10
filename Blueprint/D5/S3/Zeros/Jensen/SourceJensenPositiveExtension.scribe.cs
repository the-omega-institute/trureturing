using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class SourceJensenPositiveExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative source residues exactly characterize positive real extension.",
        H("Source Jensen Positive Extension"),
        Blocks(Describe.Lean(
            DescribeId.Create("source-jensen-positive-extension"),
            DeclarationHandle.Create(
                "D5/S3/Zeros/Jensen/SourceJensenPositiveExtension.source_jensen_positive_extension"),
            H("The residue criterion and its arrow matrix"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let d=n+2, a_k=sourceThetaCoefficient k, and let q_d be the real "
                    + "sourceQ defined by Polynomial.reflect in SourceJensenIntegralExtension. "
                    + "Its complexification is the reflection of the actual sourceJensenPolynomial. "
                    + "All indices i range over Fin(n+1), so there are exactly d-1 nodes. "
                    + "The hypothesis a_0=1 is the source normalization; the frozen "
                    + "source_theta_normalization then supplies strict positivity of every a_k.")),
                Paragraph(Math(Definitions())),
                Paragraph(Text("K is the concrete matrix arrow n a_1 t eta on Fin(1) + Fin(n+1). "
                    + "Its first diagonal entry is a_1/d, its other diagonal entries are t_i, "
                    + "and its first row and column have entries sqrt(eta_i); all remaining "
                    + "off-diagonal entries are zero. PosDef means strictly positive definite. "
                    + "PositiveSplit(q) means that q splits over the reals and every real zero "
                    + "is strictly positive. The theorem permits eta_i=0 and repeated zeros of q_d.")),
                Paragraph(Text("The previous roots lambda_i are assumed distinct and strictly "
                    + "positive, and satisfy q_(d-1)(lambda_i)=0. The derivative formula proves "
                    + "that t_i are critical nodes; their positive values and nonzero second "
                    + "derivatives are explicit conclusions. No charpoly identity or target "
                    + "positive definiteness is assumed.")),
                Paragraph(Text("The proof binds Mathlib's Schur determinant formula and Lagrange "
                    + "interpolation to this arrow matrix, then uses Hermitian characteristic "
                    + "polynomial factorization and the positive eigenvalue criterion. The "
                    + "converse residue sign uses the upstream split-polynomial logarithmic "
                    + "derivative, differentiation of its finite sum, and nonnegativity of "
                    + "squares. There is no factor induction or additional analytic estimate."))),
            DescribeRole.Theorem))));

    private static Formula Eta => Seq(Mathrm, Grp(F.Id("eta")));
    private static Formula Nn => F.Id("n");
    private static Formula Dd => F.Id("d");
    private static Formula Ii => F.Id("i");
    private static Formula Q => Sub(F.Id("q"), Dd);
    private static Formula Ti => Sub(F.Id("t"), Ii);
    private static Formula Ei => Sub(Eta, Ii);
    private static Formula Li => Sub(LambdaLower, Ii);
    private static Formula Sub(Formula f, Formula i) => Seq(f, Underscore, Grp(i));
    private static Formula Call(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Op(string f, Formula x) => Call(Seq(Operatorname, Grp(F.Id(f))), x);
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Vec(Formula x) => Seq(Open, x, Close, Underscore, Grp(Ii));
    private static Formula Nonneg => Seq(Forall, Sp, Ii, Comma, D(0), Le, Sp, Ei);
    private static Formula Definitions() => Disp(new Formula.Aligned([
        Seq(Dd, Eq, Nn, Plus, D(2), Comma, Quad, Sp,
            Ti, Eq, Div(Seq(Dd, Minus, D(1)), Dd), Li, Comma, Quad, Sp,
            Ei, Eq, Div(Seq(Minus, Dd, Call(Q, Ti)), Call(Seq(Q, Apos, Apos), Ti))),
        Seq(F.Id("K"), Eq, Begin, Grp(F.Id("pmatrix")),
            Div(Sub(F.Id("a"), D(1)), Dd), Amp, Grp(Vec(Seq(Sqrt, Grp(Ei)))), Caret, Grp(F.Id("T")),
            RowBreak, Vec(Seq(Sqrt, Grp(Ei))), Amp, Op("diag", Vec(Ti)), End, Grp(F.Id("pmatrix")))
    ]));
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, Nn, InMacro, Sp, Nat, Comma, Quad, Sp,
            Forall, Sp, LambdaLower, Colon, Op("Fin", Seq(Nn, Plus, D(1))), To, Sp, Reals, Comma),
        Seq(Sub(F.Id("a"), D(0)), Eq, D(1), Land, Sp, Op("Injective", LambdaLower), Land, Sp,
            Open, Forall, Sp, Ii, Comma, D(0), Lt, Sp, Li, Land, Sp,
            Call(Sub(F.Id("q"), Seq(Dd, Minus, D(1))), Li), Eq, D(0), Close, Implies),
        Seq(Open, Forall, Sp, Ii, Comma, D(0), Lt, Sp, Ti, Close, Land, Sp,
            Open, Forall, Sp, Ii, Comma, Call(Seq(Q, Apos, Apos), Ti), Neq, Sp, D(0), Close),
        Seq(Land, Sp, Open, Op("PositiveSplit", Q), Iff, Sp, Open, Nonneg, Close, Close),
        Seq(Land, Sp, Open, Open, Nonneg, Close, Implies, Sp,
            Op("PosDef", F.Id("K")), Land, Sp, Op("charpoly", F.Id("K")), Eq, Q, Close)
    ]));
}
