using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class SourceJensenPositiveExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative source residues exactly characterize positive real extension.",
        H("Source Jensen Positive Extension"),
        Blocks(
            Describe.Lean(DescribeId.Create("laguerre-at"),
                DeclarationHandle.Create("D5/S3/Zeros/Jensen/SourceJensenPositiveExtension.LaguerreAt"),
                H("The Laguerre expression"), StatementSource.FromAuthor(LaguerreDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real polynomial p and real x, LaguerreAt means that "
                    + "p'(x)^2-p(x)p''(x) is nonnegative. The definition includes zero and constant polynomials."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("laguerre-splits"),
                DeclarationHandle.Create("D5/S3/Zeros/Jensen/SourceJensenPositiveExtension.laguerre_splits"),
                H("Splitting implies the Laguerre inequality"), StatementSource.FromAuthor(LaguerreStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every real polynomial splitting over the reals satisfies the "
                    + "Laguerre inequality at every real argument. There is no nonzero, monic, coefficient-sign, "
                    + "root-sign or simple-root hypothesis. At a root the expression is a square. Away from "
                    + "the roots, differentiating the finite logarithmic derivative gives a nonnegative sum "
                    + "of reciprocal squares weighted by root multiplicities."))),
                DescribeRole.Theorem),
            Describe.Lean(
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
                    + "squares. There is no factor induction or additional analytic estimate.")),
                Paragraph(Text("A reciprocal application retains the unchanged fixed theta-moment "
                    + "source. Write J_n(X)=sourceP(n)(-X), Q_n=sourceQ(n), "
                    + "alpha=n/(n+1), and b(k)=(-1)^k sourceThetaCoefficient(k). Define "
                    + "G_n by the exact shifted coefficients (k+1)b(k+1); coefficient "
                    + "embedding identifies J_n and G_n with their canonical normalized "
                    + "Jensen rows. For n>=1, a nonzero real J_n node t with J_n'(t)!=0 "
                    + "satisfies Q_n(x)=x^n J_n(1/x) for nonzero x and "
                    + "Q_n'(1/t)=-(1/t)^n t^2 J_n'(t).")),
                Paragraph(Text("Differentiating the complete canonical derivative transport gives "
                    + "sourceCoupling(n+1,alpha/t)=alpha^2/t^3 "
                    + "J_(n+1)(t/alpha)/J_n'(t) "
                    + "=[n/((n+1)^2 t^2)] G_n(t)/J_n'(t). The final prefactor is "
                    + "positive for either sign of nonzero real t. Coupling nonnegativity "
                    + "is therefore exactly J_n'(t)G_n(t)>=0. This equivalence pays the "
                    + "coordinate change and exact coefficient shift; it does not pay "
                    + "the individual favorable signs.")),
                Paragraph(Text("Under the preceding row's complete distinct positive roots and "
                    + "the stated source normalization, the existing positive-extension "
                    + "criterion consequently asks for these signs at every corresponding "
                    + "node. Zero couplings and repeated roots of the next row remain "
                    + "permitted. The aggregate fourth-cumulant coupling sum does not "
                    + "establish the separate nodal signs. The fixed theta-moment source "
                    + "remains distinct from literal xiSquareSource jets until their "
                    + "analytic coefficient correspondence is proved. These identities "
                    + "establish no global original-core real-rootedness, RH or strict "
                    + "Robin for every integer above 5040."))),
            DescribeRole.Theorem))));

    private static Formula LAll(string x, Formula t, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, body);
    private static Formula LCall(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula LaguerrePredicate => LCall("LaguerreAt", F.Id("p"), F.Id("x"));
    private static Formula RealPolynomials => Seq(Reals, OpenBracket, F.Id("X"), CloseBracket);
    private static Formula LaguerreDefinition()
    {
        var p = F.Id("p"); var x = F.Id("x");
        var first = LCall("eval", LCall("derivative", p), x);
        var second = LCall("eval", LCall("derivative", LCall("derivative", p)), x);
        var expression = Subtract(new Formula.Power(first, D(2)), Multiply(LCall("eval", p, x), second));
        var nonnegative = new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, expression);
        return Disp(LAll("p", RealPolynomials, LAll("x", Reals, Equal(LaguerrePredicate, nonnegative))));
    }
    private static Formula LaguerreStatement() => Disp(LAll("p", RealPolynomials,
        new Formula.Logic(LCall("Splits", F.Id("p")), FormulaLogicOperator.Implies,
            LAll("x", Reals, LaguerrePredicate))));

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
