using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementAlgebra;

internal sealed class ObservableEventComplementPersistenceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventComplementPersistence."
            + "observable_event_complement_persistence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complementing an observable event preserves residual indistinguishability.",
        H("Observable-Event Complement Persistence"),
        Blocks(Describe.Lean(
            DescribeId.Create("observable-event-complement-persistence"),
            DeclarationHandle.Create(Declaration),
            H("Boolean negation cannot split a readout fiber"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "An observable event has constant membership on every fiber of the "
                        + "readout. Negating that membership preserves the same equivalence.")),
                Paragraph(Text(
                    "The displayed conclusion records complement closure together with the "
                        + "membership equivalences for the event and its complement."))),
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
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula eventFormula = F.Id("A");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula powerset = Call("Powerset", state);
        Formula observable = Call("observableEventAlgebra", readout);
        Formula complement = new Formula.Power(eventFormula, Grp(F.Id("c")));
        Formula sameResidual = Call("ker", readout, first, second);
        Formula sameEvent = Seq(
            Open, first, InMacro, Sp, eventFormula, Sp, Iff, Sp,
            second, InMacro, Sp, eventFormula, Close);
        Formula sameComplement = Seq(
            Open, first, InMacro, Sp, complement, Sp, Iff, Sp,
            second, InMacro, Sp, complement, Close);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, type, Comma,
            RowBreak, Grp(), readout, Colon, Sp, state, Sp, To, Sp, output,
            Comma, Sp, eventFormula, Colon, Sp, powerset, Comma,
            RowBreak, Grp(), first, Comma, Sp, second, Colon, Sp, state, Comma,
            RowBreak, Grp(),
            eventFormula, InMacro, Sp, observable, Sp, Land, Sp,
            sameResidual, Sp, Rightarrow,
            RowBreak, Grp(),
            complement, InMacro, Sp, observable, Sp, Land,
            RowBreak, Grp(), sameEvent, Sp, Land,
            RowBreak, Grp(), sameComplement, Dot));
    }
}
