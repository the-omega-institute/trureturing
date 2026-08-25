using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionCertificates;

internal sealed class ClockTimeVersusRefinementDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Clock time alone does not determine predictive refinement depth.",
        H("Clock Time Versus Refinement Depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("clock-time-does-not-determine-refinement-depth"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionCertificates/"
                        + "ClockTimeVersusRefinementDepth."
                        + "clock_time_does_not_determine_refinement_depth"),
                H("Clock duration and refinement depth separate"),
                StatementSource.FromAuthor(SeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first witness is the one-state system. Its update and readout are "
                            + "both identities, so every finite number of clock updates returns "
                            + "the unique state while its predictive completion depth is zero.")),
                    Paragraph(Text(
                        "The second witness is a four-state cycle whose readout is false at zero, "
                            + "one, and two, and true only at reveal. One update carries zero to "
                            + "one, but those two starting states cannot be distinguished at "
                            + "depth zero or one and are distinguished at depth two. Their least "
                            + "distinguishing time, and hence the system's completion depth, is "
                            + "therefore at least two.")),
                    Paragraph(Text(
                        "Together the witnesses separate elapsed clock time from predictive "
                            + "refinement depth in these two concrete regimes. The result does "
                            + "not assert witnesses for every possible refinement depth."))),
                DescribeRole.Theorem))));

    private static Formula SeparationFormula()
    {
        Formula longUpdate = F.Id("tauL");
        Formula longReadout = F.Id("qL");
        Formula delayedUpdate = F.Id("tauD");
        Formula delayedReadout = F.Id("qD");
        Formula unit = F.Id("Unit");
        Formula delayedState = F.Id("DelayedState");
        Formula boolean = F.Id("Bool");
        Formula steps = F.Id("n");
        Formula longDepth = Call("completionDepth", longUpdate, longReadout);
        Formula delayedDepth = Call("completionDepth", delayedUpdate, delayedReadout);

        return Disp(Seq(
            Open,
            Exists, Sp, longUpdate, Colon, Sp, unit, Sp, To, Sp, unit,
            Comma, Sp, longReadout, Colon, Sp, unit, Sp, To, Sp, unit,
            Comma, Esc,
            Open,
            Forall, Sp, steps, InMacro, Sp, Mathbb, Grp(F.Id("N")),
            Comma, Sp,
            Call("iterate", longUpdate, steps, Star), Sp, Eq, Sp, Star,
            Close, Sp, Land, Sp,
            longDepth, Sp, Eq, Sp, D(0),
            Close, Sp, Land, Sp, Nl,
            Open,
            Exists, Sp, delayedUpdate, Colon, Sp,
            delayedState, Sp, To, Sp, delayedState,
            Comma, Sp, delayedReadout, Colon, Sp,
            delayedState, Sp, To, Sp, boolean,
            Comma, Esc,
            Call("tauD", F.Id("zero")), Sp, Eq, Sp, F.Id("one"),
            Sp, Land, Sp,
            D(2), Sp, Leq, Sp, delayedDepth,
            Close, Dot));
    }
}
