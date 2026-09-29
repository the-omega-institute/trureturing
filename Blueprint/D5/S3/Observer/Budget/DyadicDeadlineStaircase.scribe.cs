using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class DyadicDeadlineStaircaseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary prefix weights determine the exact second-parity deadline thresholds.",
        H("Exceptional Dyadic Deadline Prefixes"),
        Blocks(
            Paragraph(Text(
                "Fix d>=0, P=2^(d+1), and W=sharpWait(d+1). The earliest final-query time "
                    + "for prefix t is E(t)=P-1+P wt(t)-2t. Every t<2^d has at most d one-bits. "
                    + "The unique prefix with d one-bits is 2^d-1, and each prefix with "
                    + "d-1 one-bits is 2^d-1-2^k for some k<d.")),
            Describe.Lean(
                DescribeId.Create("exceptional-prefix-timing"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/DyadicDeadlineStaircase.exceptional_prefix_timing"),
                H("Exact exceptional-prefix timing"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The all-ones prefix needs slack P for a second terminal parity. "
                        + "Removing bit k gives exact slack 2^(k+1). A prefix with at "
                        + "least two missing one-bits already permits the extra period "
                        + "at W. The binary classification covers d=0 and all k<d. "
                        + "This result does not count eligible prefixes or establish "
                        + "the closed operational minimum."))),
                DescribeRole.Theorem))));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Par(Formula x) => Seq(Left, Open, x, Right, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula LtN(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Pow(Formula a, Formula b) => Call("pow", a, b);

    private static Formula Statement()
    {
        var d = F.Id("d"); var t = F.Id("t"); var k = F.Id("k");
        var power = Pow(D(2), d);
        var period = Pow(D(2), Add(d, D(1)));
        var full = Sub(power, D(1));
        var missing = Sub(full, Pow(D(2), k));
        var weight = Call("wt", t);
        var topTime = Eqn(Add(Call("E", full), period), Add(F.Id("W"), period));
        var missingRight = Add(F.Id("W"), Pow(D(2), Add(k, D(1))));
        var missingTime = All("k", N(), Imp(LtN(k, d),
            Eqn(Add(Call("E", missing), period), missingRight)));
        var lowTime = All("t", N(), Imp(And(LtN(t, power), Leq(Add(weight, D(2)), d)),
            Leq(Add(Call("E", t), period), F.Id("W"))));
        var oneMissing = Seq(Exists, Sp, k, Colon, Sp, N(), Comma, Sp,
            Par(And(LtN(k, d), Eqn(Add(t, Pow(D(2), k)), full))));
        var classified = And(Leq(weight, d), And(
            Imp(Eqn(weight, d), Eqn(t, full)),
            Imp(Eqn(Add(weight, D(1)), d), oneMissing)));
        var classification = All("t", N(), Imp(LtN(t, power), classified));
        return Disp(All("d", N(),
            And(topTime, And(missingTime, And(lowTime, classification)))));
    }
}
