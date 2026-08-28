using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TimeProjection;

internal sealed class TimeExpansionEscapeDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/TimeProjection/TimeExpansionEscape."
            + "time_expansion_escape_iff_expansion_escape";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Escape between nested finite horizons is exactly readout expansion escape.",
        H("Time-Horizon Escape as Expansion Escape"),
        Blocks(Describe.Lean(
            DescribeId.Create("time-expansion-escape-iff-expansion-escape"),
            DeclarationHandle.Create(Declaration),
            H("Extending a finite horizon realizes expansion escape"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "TimeExpansionEscape is defined independently: the two states agree at "
                        + "every natural-number coordinate through N, and differ at a witness "
                        + "strictly after N but no later than M.")),
                Paragraph(Text(
                    "The forward implication evaluates longer-projection equality at the "
                        + "witness. In reverse, decidable equality on O supports a finite scan "
                        + "of Fin(M+1); shorter-projection equality excludes every returned "
                        + "coordinate at or before N."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula transition = F.Id("tau");
        Formula oldHorizon = F.Id("N");
        Formula newHorizon = F.Id("M");
        Formula horizonProof = F.Id("h");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula oldProjection = Call(
            "timeProjection", readout, transition, oldHorizon);
        Formula newProjection = Call(
            "timeProjection", readout, transition, newHorizon);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            OpenBracket, Call("DecidableEq", output), CloseBracket, Comma,
            RowBreak, Grp(),
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma, Sp,
            transition, Colon, Sp, state, Sp, To, Sp, state, Comma,
            RowBreak, Grp(),
            oldHorizon, Comma, Sp, newHorizon, Colon, Sp, naturals, Comma, Sp,
            horizonProof, Colon, Sp, oldHorizon, Sp, Leq, Sp, newHorizon, Comma,
            RowBreak, Grp(),
            left, Comma, Sp, right, Colon, Sp, state, Comma,
            RowBreak, Grp(),
            Call("TimeExpansionEscape", readout, transition, oldHorizon,
                newHorizon, horizonProof, left, right),
            Sp, Iff, RowBreak, Grp(),
            Call("ExpansionEscape", oldProjection, newProjection, left, right), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
