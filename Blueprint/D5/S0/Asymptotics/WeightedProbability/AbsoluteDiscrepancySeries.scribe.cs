using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class AbsoluteDiscrepancySeriesDocument : IScribeDocumentDefinition
{
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula AllTyped(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Rvert);
    private static Formula Log(Formula value) => Call("log", value);
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula Square(Formula value) => Seq(Open, value, Close, Caret, Grp(D(2)));
    private static Formula Apply(Formula function, Formula value) => Seq(function, Open, value, Close);

    public DocumentDefinition Create()
    {
        var x = F.Id("x");
        var j = F.Id("j");
        var c = F.Id("C");
        var s = F.Id("S");
        var e = F.Id("E");
        var omega = F.Id("a");
        var f = F.Id("f");
        var w = F.Id("w");
        var error = Delta;
        var absx = Abs(x);
        var argument = Seq(D(2), Plus, absx);
        var indexOne = Seq(j, Plus, D(1));
        var indexTwo = Seq(j, Plus, D(2));
        var weight = Seq(w, Underscore, Grp(j));
        var profile = Apply(f, x);
        var scaleDenominator = Seq(Root(Seq(c, Plus, D(2))), Sp,
            Open, D(2), Plus, Fraction(Log(Seq(c, Plus, D(2))), Log(D(2))), Close);
        var discrepancy = Apply(Seq(e, Underscore, Grp(j)), omega);
        var tailSet = Seq(OpenBrace, omega, InMacro, Sp, s, Mid, Sp,
            c, Sp, Square(indexOne), Lt, Sp, Abs(discrepancy), CloseBrace);
        var marginal = Seq(Forall, Sp, error, InMacro, Sp, Reals, Comma, Sp,
            error, Gt, Sp, D(0), Sp, Rightarrow, Sp,
            Exists, Sp, c, InMacro, Sp, Reals, Comma, Sp,
            All(j, Naturals, Seq(Mu, Open, tailSet, Close, Leq, Sp, Call("ofReal", error))));
        var measurable = All(j, Naturals, Call("Measurable", Seq(e, Underscore, Grp(j))));
        var weightSum = Seq(Sum, Underscore, Grp(Seq(j, InMacro, Sp, Naturals)), Sp,
            Call("ofReal", weight));
        var profileSum = Seq(Sum, Underscore, Grp(Seq(j, InMacro, Sp, Naturals)), Sp,
            Call("ofReal", Apply(f, discrepancy)));
        var finiteSet = Seq(OpenBrace, omega, InMacro, Sp, s, Mid, Sp,
            profileSum, Neq, Sp, Infty, CloseBrace);
        var application = AllTyped(s, F.Id("Type"), Seq(
            OpenBracket, Call("MeasurableSpace", s), CloseBracket, Comma, Sp,
            AllTyped(Mu, Call("Measure", s), AllTyped(e, Seq(Naturals, Sp, To, Sp, s, Sp, To, Sp, Integers),
                Seq(Call("FiniteMeasure", Mu), Sp, Land, Sp, Open, measurable, Close,
                    Sp, Land, Sp, Open, marginal, Close, Sp, Rightarrow, Sp,
                    Mu, Open, finiteSet, Close, Eq, Sp, D(0))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Uniform quadratic marginal tails force the reciprocal square-root logarithmic profile of integer discrepancies to have an infinite sum almost everywhere.",
            H("Absolute Discrepancy Series"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("reciprocal-square-root-logarithmic-profile"),
                    DeclarationHandle.Create("D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.discrepancyProfile"),
                    H("Discrepancy profile"),
                    StatementSource.FromAuthor(Disp(All(x, Integers, Seq(profile, Eq, Sp,
                        Fraction(D(1), Seq(Root(argument), Sp, Log(argument))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Integer absolute values are cast to the real numbers. The square-root and logarithm arguments are at least two, so every profile value is strictly positive and finite."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("exact-shifted-logarithmic-weight"),
                    DeclarationHandle.Create("D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.shiftedLogWeight"),
                    H("Shifted logarithmic weight"),
                    StatementSource.FromAuthor(Disp(All(j, Naturals, Seq(weight, Eq, Sp,
                        Fraction(D(1), Seq(Open, indexOne, Close, Sp, Log(indexTwo))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The index starts at zero. All arithmetic in the denominator is real arithmetic after casting the index."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("shifted-logarithmic-weight-divergence"),
                    DeclarationHandle.Create("D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.tsum_shiftedLogWeight_eq_top"),
                    H("Divergence of the exact shifted weights"),
                    StatementSource.FromAuthor(Disp(Seq(weightSum, Eq, Sp, Infty))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("Each weight dominates the reciprocal of (j+2) log(j+2). Removing the first two terms of the inverse-logarithmic series preserves its divergence. Nonnegative extended-real summation records that divergence as infinity.")),
                        Paragraph(Text("The inverse-logarithmic premise uses the Cauchy-condensation proof by Rémy Degenne in Wang2026Almost, distributed under Apache 2.0. The shifted comparison and its conversion to extended nonnegative summation give the weight used here."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("exact-quadratic-tail-envelope"),
                    DeclarationHandle.Create("D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.discrepancyProfile_lower_bound"),
                    H("Exact lower envelope on the quadratic good event"),
                    StatementSource.FromAuthor(Disp(All(x, Integers, All(j, Naturals, All(c, Reals,
                        Seq(D(0), Leq, Sp, c, Sp, Land, Sp, absx, Leq, Sp, c, Sp, Square(indexOne),
                            Sp, Rightarrow, Sp, Fraction(weight, scaleDenominator), Leq, Sp, profile)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("Bound the profile argument by (C+2)(j+1) squared. Its square root is at most the product of the square root of C+2 and j+1. Its logarithm is at most log(C+2) plus twice log(j+1). Comparing log(j+1) and log(2) with log(j+2) gives the displayed denominator, with no discarded initial indices."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("almost-everywhere-discrepancy-accumulation"),
                    DeclarationHandle.Create("D5/S0/Asymptotics/WeightedProbability/AbsoluteDiscrepancySeries.ae_tsum_discrepancyProfile_eq_top"),
                    H("Accumulation under uniform quadratic marginal tails"),
                    StatementSource.FromAuthor(Disp(application)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("All discrepancies are measurable integer-valued functions on one common finite measure space. For every positive real error a single finite real tail constant works for every index. The tail constant need not be nonnegative: replacing it by its maximum with zero enlarges the good event and permits the envelope estimate.")),
                        Paragraph(Text("Use the reciprocal of the envelope denominator as a positive finite scale. The lower-quantile failure event is contained in the original quadratic-tail event. Apply the uniform lower-quantile series theorem to the exact shifted weights. Independence is never assumed.")),
                        Paragraph(Text("The sum takes values in the nonnegative extended real numbers; ofReal embeds each positive real profile value. This conclusion expresses divergence of the ordinary nonnegative partial sums.")),
                        Paragraph(Text("For an endpoint model, the common execution, its discrepancy variables, their marginal tail estimates and the occupied-shape lower bound must be established separately. This analytic implication alone identifies neither the endpoint law nor a conditional cycle hazard."))),
                    DescribeRole.Theorem)),
            []));
    }
}
