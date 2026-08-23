using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class BellPureStateMixedMarginalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pure Bell density has the maximally mixed one-qubit marginal.",
        H("A Pure Bell State with a Mixed Marginal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bell-pure-state-has-maximally-mixed-marginal"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Entanglement/BellPureStateMixedMarginal."
                        + "bell_pure_state_has_maximally_mixed_marginal"),
                H("The Bell pure state reduces to one half of the identity"),
                StatementSource.FromAuthor(BellFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The amplitude is the canonical normalized Bell vector obtained from the "
                            + "standard coefficients for the two computational-basis terms. Its "
                            + "outer product is the canonical Bell density matrix.")),
                    Paragraph(Text(
                        "Normalization, positivity, trace one, rank one, and idempotence are all "
                            + "public clauses. Together they certify that the joint two-qubit "
                            + "density is pure rather than merely naming it as a pure state.")),
                    Paragraph(Text(
                        "The partial trace is constructed by summing the equal environment "
                            + "indices. It is exactly one half of the qubit identity, and its "
                            + "failure of idempotence is public evidence that the marginal is "
                            + "mixed.")),
                    Paragraph(Text(
                        "The proof applies the existing rank-one handshake and Bell-state "
                            + "certificate, then evaluates the four finite matrix entries. No "
                            + "repository theorem already packaged the Bell partial trace."))),
                DescribeRole.Theorem))));

    private static Formula BellFormula()
    {
        Formula vector = Seq(Operatorname, Grp(F.Id("bellVector")));
        Formula density = Seq(Operatorname, Grp(F.Id("bellDensity")));
        Formula marginal = Seq(
            Operatorname, Grp(F.Id("traceEnvironment")), Open, density, Close);
        Formula trace = Seq(Operatorname, Grp(F.Id("Tr")), Open, density, Close);
        Formula rank = Seq(Operatorname, Grp(F.Id("rank")), Open, density, Close);
        Formula inner = Seq(
            Langle, vector, Mid, vector, Rangle);
        Formula halfIdentity = Seq(Frac, Grp(D(1)), Grp(D(2)), Sp, F.Id("I"));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            inner, Sp, Eq, Sp, D(1), Sp, Land, RowBreak, Grp(),
            density, Sp, Geq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            trace, Sp, Eq, Sp, D(1), Sp, Land, RowBreak, Grp(),
            rank, Sp, Eq, Sp, D(1), Sp, Land, RowBreak, Grp(),
            density, Caret, Grp(D(2)), Sp, Eq, Sp, density,
            Sp, Land, RowBreak, Grp(),
            marginal, Sp, Eq, Sp, halfIdentity, Sp, Land, RowBreak, Grp(),
            marginal, Caret, Grp(D(2)), Sp, Neq, Sp, marginal, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
