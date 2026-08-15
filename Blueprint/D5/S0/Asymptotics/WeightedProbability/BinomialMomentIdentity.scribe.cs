using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class BinomialMomentIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var address = F.Id("A");
        var captureSet = F.Id("C");
        var f = F.Id("f");
        var j = F.Id("j");
        var q = F.Id("q");
        var r = F.Id("r");
        var set = F.Id("T");
        var choose = Seq(Operatorname, Grp(F.Id("choose")), Open, j, Comma, r, Close);
        var countRange = Grp(D(0), Leq, Sp, j, Leq, Sp,
            Lvert, Sp, address, Sp, Rvert);
        var captureCount = Seq(Lvert, Sp, captureSet, Open, f, Close, Sp, Rvert);
        var exactCountMass = Call("eventProbability", q,
            Seq(captureCount, Sp, Eq, Sp, j));
        var binomialMoment = Seq(
            Sum, Underscore, countRange, Sp, choose, Sp, exactCountMass);
        var setRange = Grp(set, Subseteq, Sp, address, Comma, Sp,
            Lvert, Sp, set, Sp, Rvert, Eq, Sp, r);
        var prescribedSetMass = Seq(
            Sum, Underscore, setRange, Sp,
            Call("setCaptureProbability", q, f, set));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Every binomial moment of the finite capture count equals the total probability of all prescribed captured subsets of that size.",
            H("Binomial Moment Identity"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("exact-capture-count-binomial-moment"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/BinomialMomentIdentity."
                        + "exact_capture_count_binomial_moment"),
                    H("Binomial moments enumerate prescribed captured sets"),
                    StatementSource.FromAuthor(Disp(Seq(
                        binomialMoment, Sp, Eq, Sp, prescribedSetMass, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The identity needs no normalisation hypothesis: it is pure double counting over the finite sample weight. For each sample, the capture-count sum selects its unique realized cardinality. The resulting binomial coefficient counts the r-element subsets of the captured-address finset by Finset.card_powersetCard.")),
                        Paragraph(Text(
                            "Exchanging the finite sample and subset sums identifies membership in that powerset with simultaneous capture of every address in the prescribed set, yielding setCaptureProbability term by term."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/ExactCaptureCount")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture")),
            ]));
    }
}
