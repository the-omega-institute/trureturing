using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TimeProjection;

internal sealed class PredictionExpansionEscapeDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/TimeProjection/PredictionExpansionEscape."
            + "prediction_escape_iff_expansion_escape";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-horizon prediction escape is exactly escape from a current readout to its finite-time projection.",
        H("Prediction Escape as Expansion Escape"),
        Blocks(Describe.Lean(
            DescribeId.Create("prediction-escape-iff-expansion-escape"),
            DeclarationHandle.Create(Declaration),
            H("Bounded prediction escape is finite-time readout expansion escape"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "PredictionEscape is defined independently by equality of the current "
                        + "readout and a natural-number witness k no later than N where the "
                        + "iterated readouts differ.")),
                Paragraph(Text(
                    "ExpansionEscape instead compares equality under the old readout with "
                        + "inequality of the two functions on Fin(N+1). Decidable equality on "
                        + "the output supports a finite scan from function inequality back to "
                        + "a bounded witness."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula transition = F.Id("tau");
        Formula horizon = F.Id("N");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula projection = Call(
            "timeProjection", readout, transition, horizon);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            OpenBracket, Call("DecidableEq", output), CloseBracket, Comma,
            RowBreak, Grp(),
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma, Sp,
            transition, Colon, Sp, state, Sp, To, Sp, state, Comma,
            RowBreak, Grp(),
            horizon, Colon, Sp, naturals, Comma, Sp,
            left, Comma, Sp, right, Colon, Sp, state, Comma,
            RowBreak, Grp(),
            Call("PredictionEscape", readout, transition, horizon, left, right),
            Sp, Iff, RowBreak, Grp(),
            Call("ExpansionEscape", readout, projection, left, right), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
