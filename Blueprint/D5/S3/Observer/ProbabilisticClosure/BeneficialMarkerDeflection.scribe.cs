using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class BeneficialMarkerDeflectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/BeneficialMarkerDeflection.";

    public DocumentDefinition Create()
    {
        Formula mu = F.Id("mu");
        Formula seedType = F.Id("U");
        Formula otherSeedType = F.Id("V");
        Formula policy = F.Id("p");
        Formula otherPolicy = F.Id("h");
        Formula law = F.Id("nu");
        Formula otherLaw = F.Id("rho");
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula interval = Seq(OpenBracket, D(0), Comma, D(1), CloseBracket);
        Formula oneMinusAlpha = Seq(Open, D(1), Minus, Alpha, Close);
        Formula moment = Call("reciprocalMoment", mu);
        Formula finiteMoment = Seq(moment, Neq, Infty);
        Formula endpoint = Call("essSup", F.Id("Q"), mu);
        Formula threshold = Seq(Frac, Grp(Alpha), Grp(oneMinusAlpha));
        Formula supportCondition = Seq(threshold, Lt, endpoint);
        Formula first = Call("firstNegative", Alpha, mu);
        Formula v = Call("coefficient", Alpha, mu, Seq(n, Plus, D(1)));
        Formula baseline = Seq(D(2), Call("toReal", moment), Minus, oneMinusAlpha);
        Formula sumAbs = Seq(Sum, Underscore, Grp(n, Eq, D(0)), Caret, Grp(Infty),
            Call("abs", v));

        Formula Expected(Formula p, Formula measure) => Call("expectedCost", p, measure, Alpha, mu);
        Formula RealCost(Formula p, Formula measure) => Call("toReal", Expected(p, measure));
        Formula Left(Formula type) => Call("alwaysLeft", type);
        Formula OriginalLambda(Formula p, Formula measure) => Call("lambda", p, measure, Seq(n, Plus, D(1)));
        Formula Correction(Formula p, Formula measure) => Seq(
            Sum, Underscore, Grp(n, Eq, D(0)), Caret, Grp(Infty),
            Open, OriginalLambda(p, measure), v, Close);

        Formula SeedLaw(Formula type, Formula measure, Formula body) => Seq(
            Forall, Sp, type, Colon, F.Id("Type"), Comma, Sp,
            Open, Call("MeasurableSpace", type), Rightarrow, Open,
            Forall, Sp, measure, Colon, Call("Measure", type), Comma, Sp,
            Open, Call("IsProbabilityMeasure", measure), Rightarrow,
            Open, body, Close, Close, Close, Close);

        Formula Policies(Formula type, Formula p, Formula measure, Formula body) =>
            SeedLaw(type, measure, Seq(
                Forall, Sp, p, Colon, Call("Policy", type), Comma, Sp, Open, body, Close));

        Formula support = Seq(Open, first, Lt, Infty, Leftrightarrow, supportCondition, Close);
        Formula corrections = Seq(Open,
            Call("Summable", Seq(Open, n, Mapsto, Call("abs", v), Close)), Land,
            Open, sumAbs, Lt, D(1), Close, Land,
            Open, Policies(seedType, policy, law,
                Call("Summable", Seq(Open, n, Mapsto, OriginalLambda(policy, law), v, Close))), Close,
            Close);
        Formula trueCosts = Policies(seedType, policy, law, Seq(
            Open, Call("ofReal", Alpha), moment, Leq, Expected(policy, law), Close, Land,
            Open, Expected(policy, law), Leq, D(1), Plus, D(2), moment, Close, Land,
            Open, Expected(policy, law), Neq, Infty, Leftrightarrow, finiteMoment, Close, Land,
            Open, finiteMoment, Rightarrow, Open,
                RealCost(policy, law), Eq, baseline, Plus, Correction(policy, law), Close, Close));
        Formula leftMean = SeedLaw(seedType, law, Seq(
            finiteMoment, Rightarrow, Open, RealCost(Left(seedType), law), Eq, baseline, Close));
        Formula improvement = SeedLaw(seedType, law, Seq(
            finiteMoment, Rightarrow, Open,
            Open, Exists, Sp, policy, Colon, Call("Policy", seedType), Comma, Sp,
                Expected(policy, law), Lt, Expected(Left(seedType), law), Close,
            Leftrightarrow, supportCondition, Close));
        Formula positivity = Seq(
            Forall, Sp, m, InMacro, naturals, Comma, Sp,
            Open, D(1), Leq, Sp, m, Rightarrow, Open,
                D(0), Lt, Call("coefficient", Alpha, mu, m), Close, Close);
        Formula minimum = Policies(seedType, policy, law, Seq(
            finiteMoment, Rightarrow, Open,
                Expected(Left(seedType), law), Leq, Expected(policy, law), Close));
        Formula halfBranch = Seq(Open, Seq(Frac, Grp(D(1)), Grp(D(2))), Leq, Alpha,
            Rightarrow, Open,
            Open, positivity, Close, Land,
            Open, first, Eq, Infty, Close, Land,
            Open, minimum, Close, Close, Close);
        Formula comparison = Policies(seedType, policy, law,
            Policies(otherSeedType, otherPolicy, otherLaw, Seq(
                Expected(policy, law), Neq, Infty, Rightarrow, Open,
                Expected(otherPolicy, otherLaw), Neq, Infty, Rightarrow, Open,
                Call("abs", Seq(RealCost(policy, law), Minus, RealCost(otherPolicy, otherLaw))),
                Lt, D(1), Close, Close)));
        Formula infiniteBranch = Seq(Open, moment, Eq, Infty, Rightarrow, Open,
            Policies(seedType, policy, law, Seq(
                Open, Expected(policy, law), Eq, Infty, Close, Land,
                Open, Neg, Open, Expected(policy, law), Lt, Expected(Left(seedType), law), Close, Close)),
            Close, Close);

        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Alpha, InMacro, interval, Comma, Sp,
            Open, Open, D(0), Lt, Alpha, Land, Alpha, Lt, D(1), Close, Rightarrow, Open,
            RowBreak, Grp(),
            Forall, Sp, mu, Colon, Call("Measure", interval), Comma, Sp,
            Open, Call("IsProbabilityMeasure", mu), Rightarrow, Open,
            Call("AE", mu, Seq(Open, D(0), Lt, F.Id("Q"), Land, Sp, F.Id("Q"), Lt, D(1), Close)),
            Rightarrow, Open,
            RowBreak, Grp(), support, Land,
            RowBreak, Grp(), corrections, Land,
            RowBreak, Grp(), Open, trueCosts, Close, Land,
            RowBreak, Grp(), Open, leftMean, Close, Land,
            RowBreak, Grp(), Open, improvement, Close, Land,
            RowBreak, Grp(), halfBranch, Land,
            RowBreak, Grp(), Open, comparison, Close, Land,
            RowBreak, Grp(), infiniteBranch,
            Close, Close, Close, Close, Close, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Beneficial marker deflection under an arbitrary shared-parameter prior.",
            H("Support, actual improving policies, and true expectation boundaries"),
            Blocks(Describe.Lean(
                DescribeId.Create("beneficial-marker-deflection"),
                DeclarationHandle.Create(Prefix + "beneficial_marker_deflection"),
                H("Complete support criterion with all finite and infinite mean consequences"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Q is the coordinate on the closed unit interval; the prior is any probability measure "
                        + "with Q strictly between zero and one almost everywhere. Alpha is strictly interior. "
                        + "The essential supremum may equal one without being attained. Atomic and nonatomic "
                        + "priors are both included, and the support criterion assumes no finite reciprocal moment.")),
                    Paragraph(Text(
                        "priorLaw is the prior bind of the existing jointLaw: one Q is shared by both outward "
                        + "Markov arms, the root is mixed once with true mass alpha, and the original measurable "
                        + "seed has its independent probability law. The proof establishes measurability of the "
                        + "existing trajectory law from finite prefix masses and measurable cylinders. A Policy "
                        + "chooses a fresh arm from its seed and acquired action and reply lists, and the existing "
                        + "actual execution stops at the first marker.")),
                    Paragraph(Text(
                        "expectedCost is the nonnegative integral of the actual stoppingTime, embedded from "
                        + "WithTop natural numbers into extended nonnegative reals with infinity preserved. "
                        + "reciprocalMoment integrates the reciprocal of one minus Q. coefficient at m integrates "
                        + "(1-Q)(alpha-(1-alpha)Q)Q to power m-1. firstNegative is the infimum of positive indices "
                        + "with a negative coefficient, with infinity for the empty set. Lambda always uses the "
                        + "original seed law of the all-zero replay, without survival conditioning.")),
                    Paragraph(Text(
                        "The improving witness ignores seed and replies and queries right only at acquired-history "
                        + "lengths 2N-1 and 2N, otherwise left. An induction at every replay depth proves its even "
                        + "odd-odd probability is one exactly at N. A marker before the second planned right query "
                        + "still stops the actual execution immediately. History length is acquired internal information; "
                        + "the policy has no hidden-Q input or external clock.")),
                    Paragraph(Text(
                        "Finite costs use their toReal values in the correction formula and comparison. The "
                        + "comparison permits different arbitrary measurable seed spaces and probability laws. "
                        + "When the reciprocal moment is infinite, every actual expectation is infinite, so the "
                        + "absolutely summable signed coefficients do not represent a difference of infinite "
                        + "expectations or a strict improvement of that objective."))),
                DescribeRole.Theorem))));
    }
}
