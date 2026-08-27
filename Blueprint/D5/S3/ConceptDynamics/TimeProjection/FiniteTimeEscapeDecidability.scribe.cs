using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TimeProjection;

internal sealed class FiniteTimeEscapeDecidabilityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/TimeProjection/FiniteTimeEscapeDecidability."
            + "finite_time_escape_decidability";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite range scans decide all three finite-time relations.",
        H("Finite-Time Escape Decidability"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-time-escape-decidability"),
            DeclarationHandle.Create(Declaration),
            H("Finite scans construct all three decision procedures"),
            StatementSource.FromAuthor(DefinitionFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "TimeExpansionEscape is independently defined by agreement through the old "
                        + "horizon and a separating coordinate in the added interval. It is not "
                        + "defined through ExpansionEscape.")),
                Paragraph(Text(
                    "The construction uses Finset.range (N + 1) and Finset.range (N' + 1) "
                        + "to decide the old-horizon universal clause, the bounded witnesses, "
                        + "and pointwise equality of the projected functions.")),
                Paragraph(Text(
                    "Only decidable equality on the output carrier is assumed; the state and "
                        + "output carriers need neither finiteness nor global inhabitants."))),
            DescribeRole.Definition))));

    private static Formula DefinitionFormula()
    {
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("O");
        Formula readout = F.Id("q");
        Formula transition = Tau;
        Formula oldHorizon = F.Id("N");
        Formula newHorizon = Seq(F.Id("N"), Apos);
        Formula horizonProof = F.Id("h");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula timeEscape = Call(
            "TimeExpansionEscape", readout, transition, oldHorizon,
            newHorizon, horizonProof, left, right);
        Formula predictionEscape = Call(
            "PredictionEscape", readout, transition, oldHorizon, left, right);
        Formula leftProjection = Call(
            "timeProjection", readout, transition, oldHorizon, left);
        Formula rightProjection = Call(
            "timeProjection", readout, transition, oldHorizon, right);
        Formula projectionEquality = Seq(
            leftProjection, Sp, Eq, Sp, rightProjection);

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, outputType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Call("DecidableEq", outputType), CloseBracket, Comma, RowBreak, Grp(),
            readout, Colon, Sp, stateType, Sp, To, Sp, outputType, Comma, Sp,
            transition, Colon, Sp, stateType, Sp, To, Sp, stateType, Comma, RowBreak, Grp(),
            oldHorizon, Comma, Sp, newHorizon, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, Sp,
            horizonProof, Colon, Sp, oldHorizon, Sp, Leq, Sp, newHorizon,
            Comma, Sp, left, Comma, Sp, right, InMacro, Sp, stateType, Comma, RowBreak, Grp(),
            Call("Decidable", timeEscape), Sp, Times, RowBreak, Grp(),
            Call("Decidable", predictionEscape), Sp, Times, RowBreak, Grp(),
            Call("Decidable", projectionEquality), Dot));
    }
}
