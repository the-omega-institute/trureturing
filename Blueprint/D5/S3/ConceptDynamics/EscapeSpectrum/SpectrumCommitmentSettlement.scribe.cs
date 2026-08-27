using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.EscapeSpectrum;

internal sealed class SpectrumCommitmentSettlementDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentSettlement."
            + "spectrum_commitment_local_settlement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A five-atom spectrum commitment settles by its fixed decisive-vote threshold.",
        H("Spectrum Commitment Settlement"),
        Blocks(Describe.Lean(
            DescribeId.Create("spectrum-commitment-local-settlement"),
            DeclarationHandle.Create(Declaration),
            H("The fixed cutoff gives a total five-atom commitment verdict"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "SpectrumCommitment is a typed seven-field record: atom family, scope, "
                        + "baseline, weight specification, comparator, test plan, and "
                        + "falsifiable prediction. The DESC-local instance fixes the last "
                        + "decision fields while leaving the descriptive fields explicit.")),
                Paragraph(Text(
                    "At the cutoff, an open research state terminalizes to invalid. The "
                        + "comparator counts only proved and refuted states among the five "
                        + "frozen parent atoms; statement-revised and invalid states do not "
                        + "contribute a decisive vote.")),
                Paragraph(Text(
                    "The prediction is a total pure function. It returns success exactly "
                        + "when the decisive count is at least three, and failure exactly "
                        + "when the count is below three, so no open verdict path remains.")),
                Paragraph(Text(
                    "Concrete five-state fixtures compile both branches: three proved "
                        + "states settle to success, while two refuted states and three "
                        + "statement-revised states settle to failure."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("s");
        Formula atom = F.Id("i");
        Formula commitment = F.Id("K");
        Formula stateType = F.Id("Q");
        Formula atomType = Call("Fin", D(5));
        Formula count = Call("decisiveCount", Call("comparator", commitment), state);
        Formula settlement = Call("localSettlement", commitment, state);
        Formula terminalState = Call("terminalize", Call("s", atom));

        return Disp(new Formula.Aligned([
            Seq(
                commitment, Sp, Eq, Sp, Call(
                    "localSpectrumCommitment", F.Id("atomFamily"), F.Id("scope"),
                    F.Id("baseline"), F.Id("weightSpec"), F.Id("testPlan")), Comma),
            Seq(
                Forall, Sp, state, Colon, Sp,
                atomType, Sp, To, Sp, stateType, Comma),
            Seq(
                Open, Forall, Sp, atom, Colon, Sp, atomType, Comma, Sp,
                terminalState, Sp, Neq, Sp, F.Id("open"), Close, Sp, Land),
            Seq(
                Open, settlement, Sp, Eq, Sp, F.Id("success"), Sp,
                Iff, Sp, D(3), Sp, Leq, Sp, count, Close, Sp, Land),
            Seq(
                Open, settlement, Sp, Eq, Sp, F.Id("failure"), Sp,
                Iff, Sp, count, Sp, Lt, Sp, D(3), Close, Dot),
        ]));
    }
}
