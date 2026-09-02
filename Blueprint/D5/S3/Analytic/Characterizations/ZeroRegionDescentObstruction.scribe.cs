using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Characterizations;

internal sealed class ZeroRegionDescentObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Characterizations/ZeroRegionDescentObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "Half-plane threshold positivity propagates automatically only "
                + "toward narrower regions; strict threshold shrinkage alone "
                + "does not supply Wang-style descent.",
            H("Obstruction to Wang-Style Zero-Region Descent"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("threshold-positivity-monotonicity"),
                    DeclarationHandle.Create(
                        Prefix + "threshold_positivity_mono"),
                    H("Threshold positivity is monotone toward narrower regions"),
                    StatementSource.FromAuthor(MonotonicityFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "If positivity holds to the right of 1/2 + a and "
                            + "a <= b, it also holds to the right of 1/2 + b. "
                            + "This is the automatic direction because the "
                            + "second half-plane is contained in the first."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("wang-descent-needs-analytic-input"),
                    DeclarationHandle.Create(
                        Prefix + "wang_style_descent_requires_analytic_input"),
                    H("Strict threshold contraction does not imply descent"),
                    StatementSource.FromAuthor(ObstructionFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The explicit measurement mu(s) = Re(s) - 1 and "
                            + "contraction F(a) = a/2 satisfy positivity at "
                            + "a = 1/2 and F(a) < a for every positive a, "
                            + "but positivity fails both at zero and after the "
                            + "first descent step. Any valid descent theorem "
                            + "therefore requires an additional analytic gain."))),
                    DescribeRole.Theorem))));

    private static Formula MonotonicityFormula()
    {
        Formula mu = F.Id("mu");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        return Disp(Seq(
            Forall, Sp, mu, Colon, Sp, ComplexToReal(), Comma, Sp,
            Forall, Sp, a, Comma, Sp, b, InMacro, Reals(), Comma, Sp,
            a, Sp, Le, Sp, b, Sp, Rightarrow, Sp,
            Open, Threshold(mu, a), Sp, Rightarrow, Sp,
            Threshold(mu, b), Close, Dot));
    }

    private static Formula ObstructionFormula()
    {
        Formula mu = F.Id("mu");
        Formula contraction = F.Id("F");
        Formula a = F.Id("a");
        Formula half = new Formula.Fraction(D(1), D(2));
        return Disp(Seq(
            Exists, Sp, mu, Colon, Sp, ComplexToReal(), Comma, Sp,
            contraction, Colon, Sp, RealToReal(), Comma, RowBreak,
            Threshold(mu, half), Sp, Land, Sp,
            Neg, Sp, Threshold(mu, D(0)), Sp, Land, Sp,
            Open, Forall, Sp, a, InMacro, Reals(), Comma, Sp,
            D(0), Sp, Lt, Sp, a, Sp, Rightarrow, Sp,
            Call("F", a), Sp, Lt, Sp, a, Close, Sp, Land, RowBreak,
            Neg, Open, Threshold(mu, half), Sp, Rightarrow, Sp,
            Threshold(mu, Call("F", half)), Close, Dot));
    }

    private static Formula Threshold(Formula mu, Formula a) =>
        Call("T", mu, a);

    private static Formula ComplexToReal() =>
        Seq(Complexes(), Sp, To, Sp, Reals());

    private static Formula RealToReal() =>
        Seq(Reals(), Sp, To, Sp, Reals());

    private static Formula Complexes() =>
        Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Reals() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
