using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class SourceJensenCouplingBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact source coupling sum is the fourth cumulant budget.",
        H("Source Jensen Coupling Budget"),
        Blocks(Describe.Lean(
            DescribeId.Create("source-jensen-coupling-budget"),
            DeclarationHandle.Create(
                "D5/S3/Zeros/Jensen/SourceJensenCouplingBudget.source_jensen_coupling_budget"),
            H("The coefficient and cumulant sum"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Here d=n+2, a_k=sourceThetaCoefficient k, and q_d is the same "
                    + "real sourceQ as in SourceJensenIntegralExtension. All i range over Fin(n+1), "
                    + "with exactly d-1 terms. The hypotheses are source normalization a_0=1 "
                    + "and the preceding polynomial's distinct strictly positive real roots lambda_i. "
                    + "Set t_i=((d-1)/d)lambda_i and eta_i=sourceCoupling d t_i, exactly the "
                    + "couplings used in SourceJensenPositiveExtension.")),
                Paragraph(Math(Definitions())),
                Paragraph(Text("The stored sourceThetaMoment k is the moment of order 2k: "
                    + "m_2=sourceThetaMoment 1 and m_4=sourceThetaMoment 2. Thus chi_4 is "
                    + "m_4-3m_2^2. Both displayed equalities are explicit conclusions, as is "
                    + "the nonzero second derivative at every node. This algebraic identity "
                    + "requires no assumption that the couplings are nonnegative.")),
                Paragraph(Text("The proof specializes Lagrange.coeff_eq_sum to "
                    + "R=q-d^(-1)Xq'+(a_1/d^2)q'. Its degree, node values, and coefficient "
                    + "are polynomial normalization; B1.1 supplies the critical nodes. The "
                    + "fourth-cumulant equality uses only a_1=m_2/2, a_2=m_4/24 and ring "
                    + "normalization. No root estimate, induction, or finite instance is added."))),
            DescribeRole.Theorem))));

    private static Formula Eta => Seq(Mathrm, Grp(F.Id("eta")));
    private static Formula Chi => Seq(Mathrm, Grp(F.Id("chi")));
    private static Formula Nn => F.Id("n");
    private static Formula Dd => F.Id("d");
    private static Formula Ii => F.Id("i");
    private static Formula Q => Sub(F.Id("q"), Dd);
    private static Formula Ti => Sub(F.Id("t"), Ii);
    private static Formula Ei => Sub(Eta, Ii);
    private static Formula Li => Sub(LambdaLower, Ii);
    private static Formula A(byte k) => Sub(F.Id("a"), D(k));
    private static Formula M(byte k) => Sub(F.Id("m"), D(k));
    private static Formula Sub(Formula f, Formula i) => Seq(f, Underscore, Grp(i));
    private static Formula Pow(Formula f, byte k) => Seq(f, Caret, Grp(D(k)));
    private static Formula Call(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Op(string f, Formula x) => Call(Seq(Operatorname, Grp(F.Id(f))), x);
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Total => Seq(Sum, Underscore, Grp(Ii), Ei);
    private static Formula Definitions() => Disp(Seq(
        Ti, Eq, Div(Seq(Dd, Minus, D(1)), Dd), Li, Comma, Quad, Sp,
        Ei, Eq, Div(Seq(Minus, Dd, Call(Q, Ti)), Call(Seq(Q, Apos, Apos), Ti)), Comma, Quad, Sp,
        Sub(Chi, D(4)), Eq, M(4), Minus, D(3), Pow(M(2), 2)));
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, Nn, InMacro, Sp, Nat, Comma, Quad, Sp,
            Forall, Sp, LambdaLower, Colon, Op("Fin", Seq(Nn, Plus, D(1))), To, Sp, Reals, Comma),
        Seq(A(0), Eq, D(1), Land, Sp, Op("Injective", LambdaLower), Land, Sp,
            Open, Forall, Sp, Ii, Comma, D(0), Lt, Sp, Li, Land, Sp,
            Call(Sub(F.Id("q"), Seq(Dd, Minus, D(1))), Li), Eq, D(0), Close, Implies),
        Seq(Open, Forall, Sp, Ii, Comma, Call(Seq(Q, Apos, Apos), Ti), Neq, Sp, D(0), Close),
        Seq(Land, Sp, Total, Eq, Div(Seq(Dd, Minus, D(1)), Pow(Dd, 2)),
            Open, Pow(A(1), 2), Minus, D(2), A(2), Close),
        Seq(Land, Sp, Total, Eq, Minus, Div(Seq(Dd, Minus, D(1)), Seq(D(1, 2), Pow(Dd, 2))),
            Sub(Chi, D(4)))
    ]));
}
