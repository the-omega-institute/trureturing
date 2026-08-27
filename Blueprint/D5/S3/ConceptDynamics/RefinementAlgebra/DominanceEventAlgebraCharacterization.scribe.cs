using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementAlgebra;

internal sealed class DominanceEventAlgebraCharacterizationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementAlgebra/DominanceEventAlgebraCharacterization."
            + "complete_dominance_event_algebra_characterization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete dominance is exactly agreement on all observable events plus one separating event.",
        H("Dominance Event-Algebra Characterization"),
        Blocks(Describe.Lean(
            DescribeId.Create("complete-dominance-event-algebra-characterization"),
            DeclarationHandle.Create(Declaration),
            H("Complete dominance has an event-algebra characterization"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Complete dominance is the source kernel condition: the AA and AB states "
                        + "share one readout fiber, while AB and BB do not.")),
                Paragraph(Text(
                    "Every observable event therefore gives equal indicator values on AA and "
                        + "AB. Conversely, the readout fiber of AB supplies the observable event "
                        + "that distinguishes AB from BB."))),
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
        Formula states = F.Id("X");
        Formula outputs = F.Id("O");
        Formula readout = F.Id("q");
        Formula xAA = F.Id("xAA");
        Formula xAB = F.Id("xAB");
        Formula xBB = F.Id("xBB");
        Formula eventFormula = F.Id("A");
        Formula witness = F.Id("B");
        Formula types = F.Id("Type");
        Formula stateSet = Seq(Mathcal, Grp(F.Id("P")), Open, states, Close);
        Formula conceptType = Seq(states, Sp, Rightarrow, Sp, outputs);
        Formula algebra = Call("observableEventAlgebra", readout);
        Formula sameAAAB = Call("ker", readout, xAA, xAB);
        Formula sameABBB = Call("ker", readout, xAB, xBB);
        Formula indicatorAAA = Call("indicator", eventFormula, xAA);
        Formula indicatorAAB = Call("indicator", eventFormula, xAB);
        Formula indicatorBAB = Call("indicator", witness, xAB);
        Formula indicatorBBB = Call("indicator", witness, xBB);

        return Disp(Seq(
            Forall, Sp, states, Comma, Sp, outputs, Colon, Sp, types, Comma, Sp,
            readout, Colon, Sp, conceptType, Comma,
            RowBreak, Grp(),
            xAA, Comma, Sp, xAB, Comma, Sp, xBB, Colon, Sp, states, Comma, Sp,
            Open, sameAAAB, Sp, Land, Sp, Neg, Sp, sameABBB, Close, Sp, Iff,
            RowBreak, Grp(), Open,
            Open, Forall, Sp, eventFormula, InMacro, Sp, stateSet, Comma, Sp,
            eventFormula, InMacro, Sp, algebra, Sp, Rightarrow, Sp,
            indicatorAAA, Sp, Eq, Sp, indicatorAAB, Close, Sp, Land,
            RowBreak, Grp(),
            Exists, Sp, witness, InMacro, Sp, stateSet, Comma, Sp,
            witness, InMacro, Sp, algebra, Sp, Land, Sp,
            indicatorBAB, Sp, Neq, Sp, indicatorBBB,
            Close, Dot));
    }
}
