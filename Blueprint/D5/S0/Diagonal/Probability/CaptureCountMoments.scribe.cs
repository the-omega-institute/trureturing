using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Probability;

internal sealed class CaptureCountMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The capture-count second moment and variance are exact one- and two-address sums.",
        H("Capture Count Moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("capture-count-second-moment-and-variance"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Probability/CaptureCountMoments."
                    + "capture_count_second_moment_and_variance"),
                H("Exact capture-count second moment and variance"),
                StatementSource.FromAuthor(MomentsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let N count addresses satisfying the frozen Captured predicate. Its "
                            + "second moment is the sum of the existing one-address capture "
                            + "probabilities plus twice the existing unordered two-address "
                            + "probability sum. Subtracting the square of the frozen mean gives "
                            + "the centered variance.")),
                    Paragraph(Text(
                        "CaptureSecondMoment already proves the expectation identity and the "
                            + "Paley-Zygmund lower bound, so neither is redeclared. This theorem "
                            + "evaluates that bound's abstract second-moment denominator exactly; "
                            + "the resulting probability inequality is an exact re-expression, "
                            + "not a stronger inequality.")),
                    Paragraph(Text(
                        "Repository search found no prior one-plus-two-address moment expansion. "
                            + "Pinned Mathlib supplies finite sum-product rearrangements, which "
                            + "the Lean proof applies to the existing capture indicators."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Diagonal/Probability/CaptureSecondMoment")),
            DocumentEdge.Dependency.Create(
                GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni")),
        ]));

    private static Formula MomentsFormula()
    {
        Formula address = F.Id("a");
        Formula count = F.Id("N");
        Formula q = F.Id("q");
        Formula f = F.Id("f");
        Formula oneAddress = Seq(
            Sum, Underscore, Grp(address),
            Call("captureProbability", q, f, address));
        Formula twoAddress = Call("pairProbabilitySum", q, f);
        Formula secondMoment = Seq(
            Operatorname, Grp(F.Id("E")), Open,
            count, Caret, Grp(D(2)), Close);
        Formula variance = Seq(Operatorname, Grp(F.Id("Var")), Open, count, Close);
        Formula expandedSecondMoment = Seq(
            oneAddress, Plus, D(2), Star, twoAddress);

        return Disp(Seq(
            secondMoment, Eq, expandedSecondMoment,
            Sp, Land, Sp,
            variance, Eq, expandedSecondMoment,
            Minus, Grp(oneAddress), Caret, Grp(D(2)), Dot));
    }
}
