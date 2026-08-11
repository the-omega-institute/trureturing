using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class FiniteCounterexampleCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Computability/FiniteCounterexampleCertificate",
            "A false universal finite readout has exactly a bounded counterexample certificate."),
        H("Finite Counterexample Certificates"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("finite-readout-counterexample-certificate"),
                H("A false universal finite readout has a bounded certificate"),
                LeanTheorem(
                    "D5/S0/Computability/FiniteCounterexampleCertificate."
                    + "finite_readout_counterexample_certificate"),
                Disp(Seq(
                    Neg, Open, Forall, Sp, F.Id("h"), Comma, Sp,
                    F.Id("D"), Open, F.Id("h"), Close, Sp, Eq, Sp,
                    F.Id("true"), Close, Sp, Iff, Sp,
                    Exists, Sp, F.Id("n"), Comma, Sp, F.Id("h"), Comma, Sp,
                    Operatorname, Grp(F.Id("findCounterexample")),
                    Open, F.Id("D"), Comma, Sp, F.Id("n"), Close,
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("some")),
                    Open, F.Id("h"), Close, Sp, Land, Sp,
                    F.Id("D"), Open, F.Id("h"), Close, Sp, Eq, Sp,
                    F.Id("false"), Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "A finite readout is an executable function from finite marker "
                        + "histories to `Bool`, with `true` as acceptance and `false` as "
                        + "rejection. Failure of universal acceptance is equivalent to "
                        + "an explicit natural bound and a history returned by bounded "
                        + "search with a certified false readout. The rejected history is "
                        + "therefore a checkable counterexample certificate.")),
                    Paragraph(Text(
                        "The proof first extracts a rejected history from the failed "
                        + "universal statement. That history's length supplies a finite "
                        + "search bound. Completeness of the existing bounded search then "
                        + "returns a counterexample, and soundness certifies its rejection. "
                        + "Conversely, any certified rejected history directly contradicts "
                        + "universal acceptance.")),
                    Paragraph(Text(
                        "The library was searched before proving. Pinned Mathlib provides "
                        + "`not_forall` and `Bool.eq_false_of_not_eq_true`, but it has no "
                        + "declaration about this marker-history search. The repository's "
                        + "`findCounterexample_complete` and `findCounterexample_sound` "
                        + "supply the executable core, so the new result is an honest "
                        + "composition rather than a reproof of either dependency.")))
            )),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/History/MarkerHistorySearch"))]));
}
