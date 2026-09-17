using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class BinaryMixingMemoryDivergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed bound on deterministic observer states fails below the static error floor throughout a sufficiently small positive mixing interval.",
        H("Binary mixing and necessary observer memory"),
        Blocks(
            Paragraph(Text(
                "The hidden state and report alphabets are binary. A chronological word starts "
                + "from the uniform hidden prior. The old hidden bit emits its report before "
                + "the bit flips. For report zero, set a=p and c=1-p; for report one, set "
                + "a=1-p and c=p. The transfer of an unnormalized column is")),
            Paragraph(Math(TransferFormula())),
            Paragraph(Text(
                "Let v(p,r,w) be the successive transfer of the initial column (1/2,1/2) "
                + "along w, with the first coordinate corresponding to hidden zero. Let "
                + "Z(p,r,w) be the sum of its coordinates. The next-zero prediction is the "
                + "ratio of the mass of w followed by zero to the mass of w:")),
            Paragraph(Math(PredictionFormula())),
            Paragraph(Text(
                "An observer has a finite state set S, an initial state s0, two fixed "
                + "updates T0 and T1, and an arbitrary real readout t. Its state s(w) is "
                + "obtained by applying the report-labelled updates chronologically; "
                + "s(empty)=s0 and s(wb)=Tb(s(w)). All evolving memory is in S. "
                + "In particular, readouts in the probability interval are included.")),
            Describe.Lean(
                DescribeId.Create("small-mixing-observer-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/BinaryMixingMemoryDivergence."
                    + "small_mixing_observer_obstruction"),
                H("A uniform obstruction to bounded observer memory"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The interval depends only on p, the error tolerance and N. The "
                        + "observer may be chosen anew at every mixing rate, and its readout "
                        + "may contain arbitrary exact real constants. Nevertheless, some "
                        + "positive-probability finite history has error strictly above "
                        + "the tolerance. The assertion includes all finite history lengths.")),
                    Paragraph(Text(
                        "At zero mixing, the hidden likelihoods along a block of n zeros "
                        + "and k ones are p^n(1-p)^k/2 and (1-p)^n p^k/2. Choose an integer "
                        + "m so that the two histories with net evidence of opposite signs "
                        + "have a prediction gap greater than twice the tolerance. For every "
                        + "positive period l, the histories are n zeros followed by n+ml ones, "
                        + "and n+2ml zeros followed by n+ml ones.")),
                    Paragraph(Text(
                        "Every fixed-word mass is polynomial in the mixing rate, and the "
                        + "denominator is positive at zero. Prediction gaps are therefore "
                        + "continuous there. There are finitely many possible n and l below "
                        + "the state bound, so one positive interval preserves all their "
                        + "strict gaps. The finite-orbit period bound makes the two zero "
                        + "prefixes reach the same state for one such pair. Appending their "
                        + "common one suffix preserves this equality. A single real readout "
                        + "cannot approximate both predictions within the stated tolerance."))),
                DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Half => Seq(Frac, Grp(D(1)), Grp(D(2)));
    private static Formula Sub(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula Add(Formula x, Formula y) => Seq(x, Plus, y);
    private static Formula Mul(params Formula[] factors) => Seq(factors);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new System.Collections.Generic.List<Formula> { Id(name), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i != 0) parts.Add(Comma);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq(parts.ToArray());
    }
    private static Formula Ratio(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Card(Formula s) => Seq(Operatorname, Grp(Id("card")), Par(s));

    private static Formula TransferFormula()
    {
        var r = Id("r");
        var a = Id("a");
        var c = Id("c");
        var x = Id("x");
        var y = Id("y");
        return Disp(Seq(Par(Seq(x, Comma, y)), Sp, Mapsto, Sp,
            Par(Seq(Add(Mul(Par(Sub(D(1), r)), a, x), Mul(r, c, y)), Comma,
                Add(Mul(r, a, x), Mul(Par(Sub(D(1), r)), c, y))))));
    }

    private static Formula PredictionFormula()
    {
        var p = Id("p");
        var r = Id("r");
        var w = Id("w");
        return Disp(Seq(Call("f", p, r, w), Sp, Eq, Sp,
            Ratio(Call("Z", p, r, Seq(w, D(0))), Call("Z", p, r, w))));
    }

    private static Formula ResultFormula()
    {
        var p = Id("p");
        var e = Varepsilon;
        var n = Id("N");
        var d = DeltaLower;
        var r = Id("r");
        var s = Id("S");
        var s0 = Seq(Id("s"), Underscore, Grp(D(0)));
        var t0 = Seq(Id("T"), Underscore, Grp(D(0)));
        var t1 = Seq(Id("T"), Underscore, Grp(D(1)));
        var t = Id("t");
        var w = Id("w");
        var words = Seq(OpenBrace, D(0), Comma, D(1), CloseBrace, Caret, Grp(Star));
        var error = Seq(Lvert, Sp, Call("t", Call("s", w)), Minus,
            Call("f", p, r, w), Rvert);
        return Disp(Seq(
            Forall, Sp, p, Comma, e, InMacro, Sp, Real, Comma, Sp,
            Forall, Sp, n, InMacro, Sp, Nat, Comma, Esc,
            Par(Seq(D(0), Sp, Lt, Sp, p, Sp, Lt, Sp, Half, Sp, Land, Sp,
                D(0), Sp, Lt, Sp, e, Sp, Lt, Sp, Sub(Half, p))),
            Sp, Rightarrow, Sp, Exists, Sp, d, InMacro, Sp, Real, Comma, Esc,
            D(0), Sp, Lt, Sp, d, Sp, Land, Sp,
            Forall, Sp, r, InMacro, Sp, Real, Comma, Esc,
            Par(Seq(D(0), Sp, Lt, Sp, r, Sp, Land, Sp,
                r, Sp, Lt, Sp, Seq(Min, Par(Seq(d, Comma, Half))))), Sp, Rightarrow, Sp,
            Forall, Sp, s, Comma, Sp,
            OpenBracket, Operatorname, Grp(Id("Fintype")), Sp, s, CloseBracket, Comma, Esc,
            Forall, Sp, s0, InMacro, Sp, s, Comma, Sp,
            Forall, Sp, t0, Comma, t1, Colon, Sp, s, Sp, To, Sp, s, Comma, Esc,
            Forall, Sp, t, Colon, Sp, s, Sp, To, Sp, Real, Comma, Esc,
            Card(s), Sp, Leq, Sp, n, Sp, Rightarrow, Sp,
            Exists, Sp, w, InMacro, Sp, words, Comma, Esc,
            D(0), Sp, Lt, Sp, Call("Z", p, r, w), Sp, Land, Sp,
            e, Sp, Lt, Sp, error));
    }
}
