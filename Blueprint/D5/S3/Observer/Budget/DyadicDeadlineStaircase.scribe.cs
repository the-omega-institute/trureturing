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
                        + "This result classifies threshold prefixes but does not itself "
                        + "count labels of the deadline family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("deadline-family-closed-staircase"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/DyadicDeadlineStaircase.deadline_family_closed_staircase"),
                H("Closed operational deadline staircase"),
                StatementSource.FromAuthor(StaircaseStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every d and nonnegative slack h, D is sharpWait(d+1)+h and q "
                        + "counts indices 1<=i<=d+1 with 2^i<=h. The family consists of "
                        + "actual successful raw-bit protocols under D. A single decoder "
                        + "works for every protocol and source; clockTag and tagDecode "
                        + "attain the exact count on realized terminal times. The formula "
                        + "includes d=0, h=0, and h>=2^(d+1). It concerns receiver clock "
                        + "labels, not acquisition workspace or average description length."))),
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
        var weight = Call("length", Call("bitIndices", t));
        var wait = Call("sharpWait", Add(d, D(1)));
        var topTime = Eqn(Add(Call("earliestTime", d, full), period), Add(wait, period));
        var missingRight = Add(wait, Pow(D(2), Add(k, D(1))));
        var missingTime = All("k", N(), Imp(LtN(k, d),
            Eqn(Add(Call("earliestTime", d, missing), period), missingRight)));
        var lowTime = All("t", N(), Imp(And(LtN(t, power), Leq(Add(weight, D(2)), d)),
            Leq(Add(Call("earliestTime", d, t), period), wait)));
        var oneMissing = Seq(Exists, Sp, k, Colon, Sp, N(), Comma, Sp,
            Par(And(LtN(k, d), Eqn(Add(t, Pow(D(2), k)), full))));
        var classified = And(Leq(weight, d), And(
            Imp(Eqn(weight, d), Eqn(t, full)),
            Imp(Eqn(Add(weight, D(1)), d), oneMissing)));
        var classification = All("t", N(), Imp(LtN(t, power), classified));
        return Disp(All("d", N(),
            And(topTime, And(missingTime, And(lowTime, classification)))));
    }

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(LambdaLower, Sp, binder, Colon, Sp, N(), Sp, Mapsto, Sp, Par(body));

    private static Formula StaircaseStatement()
    {
        var d = F.Id("d"); var h = F.Id("h"); var b = F.Id("b");
        var z = F.Id("Z"); var phi = F.Id("phi"); var p = F.Id("p");
        var r = F.Id("r"); var i = F.Id("i");
        var depth = Add(d, D(1));
        var period = Pow(D(2), depth);
        var deadline = Add(Call("sharpWait", depth), h);
        var interval = Seq(F.Id("Finset"), Dot, F.Id("Icc"), Par(Seq(D(1), Comma, Sp, depth)));
        var q = Seq(Par(interval), Dot, F.Id("filter"), Par(Lambda(i,
            Leq(Pow(D(2), i), h))), Dot, F.Id("card"));
        var count = Add(Sub(period, depth), q);
        var family = Call("deadlineFamily", d, b, deadline, p);
        var time = Call("terminalTime", period, b, p, r);
        var raw = Call("snd", Call("terminalRecord", period, b, p, r));
        var source = All("p", Call("Protocol", depth), Imp(family,
            All("r", N(), Imp(LtN(r, period),
                Eqn(Call("recover", Call("phi", time), raw), r)))));
        var lower = All("Z", F.Id("Type"),
            All("phi", Seq(N(), Sp, To, Sp, z),
                All("recover", Seq(z, Sp, To, Sp, Call("Fin", D(2)), Sp, To, Sp, N()),
                    Imp(source, Leq(count,
                        Call("card", Call("familyClockLabels", d, b, deadline, phi)))))));
        var tagged = All("p", Call("Protocol", depth), Imp(family,
            All("r", N(), Imp(LtN(r, period),
                Eqn(Call("tagDecode", d, b, Call("clockTag", d, time), raw), r)))));
        var attained = Eqn(Call("card", Call("familyClockLabels", d, b,
            deadline, Call("clockTag", d))), count);
        return Disp(All("d", N(), All("h", N(), All("b", Call("Fin", D(2)),
            And(lower, And(tagged, attained))))));
    }
}
