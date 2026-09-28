using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Dilation;

internal sealed class EquivariantSeriesObserverDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Dilation/EquivariantSeriesObserver.observed_recovery_iff_power_closed";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Power closure characterizes recovery of unrestricted bivariate class-function series.",
        H("Equivariant Series Observer"),
        Blocks(Describe.Lean(
            DescribeId.Create("equivariant-series-observer-power-closure"),
            DeclarationHandle.Create(Declaration),
            H("Recovery and conjugacy-saturated power closure"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let G be any group, S any subset of G, and K any characteristic-zero "
                        + "field, including the rationals. A family H assigns to each group element a formal bivariate "
                        + "series over K. The domain C consists of every such family whose "
                        + "coefficients vanish when either exponent is zero and whose values "
                        + "agree on conjugate elements. Coefficients may have either sign; no "
                        + "finite-group, convergence, or representation hypothesis is imposed.")),
                Paragraph(Text(
                    "For positive m and n, the coefficient of p^m q^n in the logarithmic "
                        + "history of H at g is the finite sum, over k dividing gcd(m,n), of "
                        + "H at g^k and exponent pair (m/k,n/k), divided by k. Coefficients "
                        + "with a zero exponent vanish. Recovery on S means that equality of "
                        + "these histories on S implies equality of the original families on S "
                        + "for every pair in C.")),
                Paragraph(Text(
                    "Conjugacy saturation contains exactly the elements conjugate to some "
                        + "element of S. The equivalence says that recovery holds precisely when "
                        + "this saturation contains every positive power of each of its elements. "
                        + "For sufficiency, the divisor-one term gives the coefficient at g; all "
                        + "other terms use smaller exponents at powers of g still in the saturation, "
                        + "so induction recovers each coefficient. For necessity, a Mobius-inverted "
                        + "class-function series has logarithmic history concentrated on a missing "
                        + "conjugacy class. If s is observed and s^r lies in that class for a prime "
                        + "r, its original coefficient at s in degree (r,r) is -1/r, so recovery fails. "
                        + "It applies to the unrestricted domain C; actual representation traces "
                        + "and VOA traces form narrower domains for which necessity is not asserted."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula g = F.Id("g"), n = F.Id("n"), s = F.Id("S");
        Formula a = Call("Sat", s);
        Formula h1 = new Formula.Subscript(F.Id("H"), F.D(1));
        Formula h2 = new Formula.Subscript(F.Id("H"), F.D(2));
        Formula c = new Formula.Subscript(F.Id("C"), F.Id("G"));
        Formula restricted(Formula h) => F.Seq(h, F.Bar, F.Underscore, F.Grp(s));
        Formula observation(Formula h) => Call("Phi", h);
        Formula equality(Formula left, Formula right) =>
            new Formula.Relation(left, FormulaRelationOperator.Equal, right);
        Formula recovery = F.Seq(
            F.Forall, F.Sp, h1, F.Comma, F.Sp, h2, F.Sp, F.InMacro, F.Sp, c,
            F.Comma, F.Sp,
            F.Open, equality(restricted(observation(h1)), restricted(observation(h2))),
            F.Close, F.Sp, F.Rightarrow, F.Sp,
            equality(restricted(h1), restricted(h2)));
        Formula closure = F.Seq(
            F.Forall, F.Sp, g, F.Sp, F.InMacro, F.Sp, a, F.Comma, F.Sp,
            F.Forall, F.Sp, n, F.Sp, F.InMacro, F.Sp,
            F.Mathbb, F.Grp(F.Id("N")), F.Comma, F.Sp,
            F.D(0), F.Sp, F.Lt, F.Sp, n, F.Sp, F.Rightarrow, F.Sp,
            F.Seq(g, F.Caret, F.Grp(n)), F.Sp, F.InMacro, F.Sp, a);
        return F.Disp(new Formula.Aligned([
            F.Seq(a, F.Sp, F.Eq, F.Sp, F.OpenBrace, g, F.Sp, F.Mid, F.Sp,
                F.Exists, F.Sp, F.Id("s"), F.Sp, F.InMacro, F.Sp, s, F.Comma, F.Sp,
                F.Id("s"), F.Sp, F.Sim, F.Sp, g, F.CloseBrace, F.Comma),
            F.Seq(Call("Rec", s), F.Sp, F.Colon, F.Eq, F.Sp, recovery, F.Comma),
            F.Seq(Call("Rec", s), F.Sp, F.Leftrightarrow, F.Sp, closure, F.Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
