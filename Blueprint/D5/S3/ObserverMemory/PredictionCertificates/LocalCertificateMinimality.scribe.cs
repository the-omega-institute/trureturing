using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionCertificates;

internal sealed class LocalCertificateMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local pair-distance checks certify the canonical minimal predictive quotient.",
        H("Local Prediction Certificate Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-certificate-implies-global-predictive-minimality"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality."
                        + "local_certificate_global_minimality"),
                H("A locally checked distance table certifies global minimality"),
                StatementSource.FromAuthor(LocalCertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite deterministic state space with transition tau and "
                            + "readout q. A candidate label map is surjective, its equal-label "
                            + "pairs are exactly the entries marked infinite by delta, and delta "
                            + "passes the local zero-or-successor recurrence at every state pair.")),
                    Paragraph(Text(
                        "The recurrence is first proved to determine the unique shortest "
                            + "distinguishing-time table. Consequently, infinite entries are "
                            + "exactly equal complete itineraries, the label fibers are the "
                            + "canonical future-equivalence classes, and the transition on "
                            + "labels is well-defined.")),
                    Paragraph(Text(
                        "Mathlib's quotientKerEquivOfSurjective identifies the labelled carrier "
                            + "with the complete-itinerary quotient. The existing repository "
                            + "theorem controlled_behavior_universal_property is applied at a "
                            + "singleton input type to show that this carrier has no more states "
                            + "than any finite surjective deterministic realization preserving "
                            + "the transition and readout.")),
                    Paragraph(Text(
                        "The maximum finite certificate entry equals the canonical stability "
                            + "depth, with zero used when every entry is infinite. A verifier "
                            + "scans one entry for each ordered state pair, so its declared work "
                            + "function is the square of the state count and is therefore "
                            + "quadratic."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula LocalCertificateFormula()
    {
        Formula tau = F.Id("tau");
        Formula readout = F.Id("q");
        Formula label = F.Id("c");
        Formula distance = F.Id("delta");
        Formula state = F.Id("y");
        Formula checks = Call("CertificateChecks", tau, readout, label, distance);
        Formula completion = Call("PredictiveCompletion", tau, readout);
        Formula fibers = Call("Fibers", label);
        Formula futureClasses = Call("FutureClasses", tau, readout);
        Formula updateLaw = Seq(
            Exists, Sp, F.Id("barTau"), Comma, Sp, Forall, Sp, state, Comma, Esc,
            F.Id("barTau"), Open, label, Open, state, Close, Close,
            Sp, Eq, Sp, label, Open, tau, Open, state, Close, Close);
        Formula depthLaw = Seq(
            Call("certificateDepth", distance), Sp, Eq, Sp,
            Call("stabilityDepth", tau, readout));
        Formula minimality = Call("MinimalStateCount", tau, readout, F.Id("C"));
        Formula work = Seq(
            Call("certificateCheckWork", F.Id("n")), Sp, InMacro, Sp,
            Call("BigO", Seq(F.Id("n"), Caret, Grp(D(2)))));

        return Disp(Seq(
            Forall, Sp, tau, Comma, Sp, readout, Comma, Sp, label, Comma, Sp,
            distance, Comma, Esc, checks, Sp, Rightarrow, Sp, Nl,
            Open,
            fibers, Sp, Eq, Sp, futureClasses, Sp, Land, Sp, Nl,
            updateLaw, Sp, Land, Sp, Nl,
            Operatorname, Grp(F.Id("Nonempty")), Open,
            Operatorname, Grp(F.Id("Equiv")), Open,
            F.Id("C"), Comma, Sp, completion, Close, Close,
            Sp, Land, Sp, Nl,
            depthLaw, Sp, Land, Sp, Nl,
            minimality, Sp, Land, Sp, Nl,
            work,
            Close, Dot));
    }
}
