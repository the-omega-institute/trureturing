using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionCertificates;

internal sealed class LocalCertificateCanonicalMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local distance checks expose the canonical predictive equivalence and unique quotient update.",
        H("Canonical Local Prediction Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-certificate-canonical-minimality"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateCanonicalMinimality."
                        + "local_certificate_canonical_minimality"),
                H("A local certificate determines the canonical minimal completion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite types Y and C, a deterministic transition tau, readout q, "
                            + "surjective label c, and distance table delta, assume that equal "
                            + "labels are exactly the entries marked infinite and that delta "
                            + "satisfies the local zero-or-successor recurrence.")),
                    Paragraph(Text(
                        "The public conclusion states the complete-itinerary fibre identity, "
                            + "the unique quotient update, and the explicit equivalence from C "
                            + "to the canonical predictive completion. It also retains exact "
                            + "certificate depth, finite-realization state-count minimality, "
                            + "and quadratic table-scan work."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula typeY = F.Id("Y"), typeO = F.Id("O"), typeC = F.Id("C");
        Formula tau = F.Id("tau"), readout = F.Id("q"), label = F.Id("c");
        Formula distance = F.Id("delta"), state = F.Id("y");
        Formula finiteY = Call("Fintype", typeY), finiteC = Call("Fintype", typeC);
        Formula checks = Call("LocalDistanceChecks", tau, readout, distance);
        Formula fibres = Seq(
            Forall, Sp, state, Comma, Sp, F.Id("yPrime"), Comma, Sp,
            label, Open, state, Close, Sp, Eq, Sp,
            label, Open, F.Id("yPrime"), Close, Sp, Iff, Sp,
            Call("completeItinerary", tau, readout, state), Sp, Eq, Sp,
            Call("completeItinerary", tau, readout, F.Id("yPrime")));
        Formula update = Seq(
            Exists, Bang, Sp, F.Id("barTau"), Comma, Sp, Forall, Sp, state, Comma, Sp,
            F.Id("barTau"), Open, label, Open, state, Close, Close, Sp, Eq, Sp,
            label, Open, tau, Open, state, Close, Close);
        Formula equivalence = Seq(
            Exists, Sp, F.Id("equiv"), Colon, Sp,
            F.Id("C"), Sp, Equiv, Sp, Call("PredictiveCompletion", tau, readout), Comma, Sp,
            Forall, Sp, state, Comma, Sp, F.Id("yPrime"), Comma, Sp,
            F.Id("equiv"), Open, label, Open, state, Close, Close, Sp, Eq, Sp,
            F.Id("equiv"), Open, label, Open, F.Id("yPrime"), Close, Close, Sp, Iff, Sp,
            Call("completeItinerary", tau, readout, state), Sp, Eq, Sp,
            Call("completeItinerary", tau, readout, F.Id("yPrime")));
        Formula depth = Seq(Call("certificateDepth", distance), Sp, Eq, Sp,
            Call("stabilityDepth", tau, readout));
        Formula work = Seq(Call("certificateCheckWork", F.Id("n")), Sp, InMacro, Sp,
            Call("BigO", Seq(F.Id("n"), Caret, Grp(D(2)))));

        return Disp(Seq(
            Forall, Sp, typeY, Comma, Sp, typeO, Comma, Sp, typeC, Comma, Esc,
            finiteY, Sp, Land, Sp, finiteC, Sp, Land, Sp,
            F.Id("Surjective"), Open, label, Close, Sp, Land, Sp,
            Call("FiberCheck", label, distance), Sp, Land, Sp, checks,
            Rightarrow, Sp, Nl,
            fibres, Sp, Land, Sp, Nl,
            update, Sp, Land, Sp, Nl,
            equivalence, Sp, Land, Sp, Nl,
            depth, Sp, Land, Sp, Nl,
            Call("MinimalStateCount", tau, readout, typeC), Sp, Land, Sp, Nl,
            work, Dot));
    }
}
