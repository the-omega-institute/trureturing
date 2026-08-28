using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementAlgebra;

internal sealed class EventSeparationCharacterizationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementAlgebra/EventSeparationCharacterization."
            + "event_separation_characterization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Readout-equivalent states are exactly those agreeing on every observable event.",
        H("Event Separation Characterization"),
        Blocks(Describe.Lean(
            DescribeId.Create("event-separation-characterization"),
            DeclarationHandle.Create(Declaration),
            H("Observable events separate distinct readout fibers"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fiber-constant membership gives the forward implication. For the reverse "
                        + "implication, the observable fiber through the first state separates "
                        + "any state with a different readout."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula states = F.Id("X");
        Formula outputs = F.Id("O");
        Formula readout = F.Id("q");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula eventFormula = F.Id("A");
        Formula types = F.Id("Type");
        Formula conceptType = Seq(states, Sp, Rightarrow, Sp, outputs);
        Formula stateSet = Seq(Mathcal, Grp(F.Id("P")), Open, states, Close);
        Formula kernel = Seq(
            Operatorname, Grp(F.Id("ker")), Open,
            readout, Comma, Sp, first, Comma, Sp, second, Close);
        Formula algebra = Seq(
            Operatorname, Grp(F.Id("observableEventAlgebra")), Open, readout, Close);

        return Disp(Seq(
            Forall, Sp, states, Comma, Sp, outputs, Colon, Sp, types, Comma, Sp,
            readout, Colon, Sp, conceptType, Comma, Sp,
            first, Comma, Sp, second, Colon, Sp, states, Comma,
            RowBreak, Grp(),
            kernel, Sp, Iff, Sp,
            Forall, Sp, eventFormula, InMacro, Sp, stateSet, Comma, Sp,
            eventFormula, InMacro, Sp, algebra, Sp, Rightarrow, Sp,
            Open, first, InMacro, Sp, eventFormula, Sp, Iff, Sp,
            second, InMacro, Sp, eventFormula, Close, Dot));
    }
}
