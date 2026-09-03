using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class RealAxisNonvanishingDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaBridge/RealAxisNonvanishing."
            + "riemannZeta_real_zero_outside_Ioo";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real zeta zeros outside the open unit interval are negative even integers.",
        H("Real-Axis Zeta Zeros Outside the Unit Interval"),
        Blocks(Describe.Lean(
            DescribeId.Create("riemann-zeta-real-zero-outside-ioo"),
            DeclarationHandle.Create(Declaration),
            H("Real zeros outside the open unit interval are trivial"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a positive real input outside the open unit interval, Mathlib's "
                        + "nonvanishing theorem for real part at least one excludes a zero.")),
                Paragraph(Text(
                    "For a nonpositive input, the completed-zeta quotient and its frozen "
                        + "nonvanishing on the closed left half-plane force the real gamma "
                        + "factor to vanish. Mathlib's gamma-zero classification then gives a "
                        + "negative even integer, with zero excluded by the value of zeta at "
                        + "zero.")),
                Paragraph(Text(
                    "This is Mathlib content plus one frozen completed-zeta lemma. It neither constructs zeta zeros nor makes "
                        + "a claim about the Riemann hypothesis."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula x = F.Id("x");
        Formula n = F.Id("n");
        Formula inOpenUnitInterval = And(
            Less(D(0), x),
            Less(x, D(1)));
        Formula outsideOpenUnitInterval =
            Seq(Neg, Sp, Open, inOpenUnitInterval, Close);
        Formula zetaZero = Equal(Call("riemannZeta", x), D(0));
        Formula negativeEven = Seq(
            Exists, Sp, Bound(n, Naturals()), Comma, Sp,
            x, Sp, Eq, Sp,
            Minus, D(2), Sp, Star, Sp, Open, n, Sp, Plus, Sp, D(1), Close);

        return Disp(Seq(
            Forall, Sp, Bound(x, Reals()), Comma, RowBreak, Grp(),
            ImpliesFormula(
                outsideOpenUnitInterval,
                ImpliesFormula(zetaZero, negativeEven)),
            Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Bound(Formula name, Formula type) =>
        Seq(name, Colon, Sp, type);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[0];
        for (var i = 1; i < clauses.Length; i++)
        {
            result = Seq(Open, result, Close, Sp, Land, Sp, Open, clauses[i], Close);
        }

        return result;
    }

    private static Formula Less(Formula left, Formula right) =>
        Seq(left, Sp, Lt, Sp, right);

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula ImpliesFormula(Formula premise, Formula conclusion) =>
        Seq(Open, premise, Close, Sp, Rightarrow, Sp, Open, conclusion, Close);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
}
