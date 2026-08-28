using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementAlgebra;

internal sealed class ObservableEventAlgebraRepresentationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraRepresentation."
            + "observable_event_algebra_representation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fiber-constant events are canonically the powerset of the effective output.",
        H("Observable-Event Algebra Representation"),
        Blocks(Describe.Lean(
            DescribeId.Create("observable-event-algebra-representation"),
            DeclarationHandle.Create(Declaration),
            H("Observable events form the powerset of the realized range"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The observable-event carrier is the existing predicate of subsets whose "
                        + "membership is constant on every readout fiber. It is bundled with "
                        + "the inherited union, intersection, complement, and empty event.")),
                Paragraph(Text(
                    "The canonical forward map sends an observable event to the realized "
                        + "readout values met by that event. The inverse pulls a set of realized "
                        + "values back along the range factorization.")),
                Paragraph(Text(
                    "Fiber constancy makes pullback after image recover the original event, "
                        + "while surjectivity onto the realized range makes image after pullback "
                        + "recover the original set of effective outputs.")),
                Paragraph(Text(
                    "The displayed computation rule uniquely determines the order isomorphism, "
                        + "and an order isomorphism between these Boolean algebras preserves all "
                        + "Boolean operations."))),
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
        Formula representation = F.Id("Phi");
        Formula eventFormula = F.Id("A");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula observableAlgebra = Call("observableEventBooleanAlgebra", readout);
        Formula effectiveOutput = Call("range", readout);
        Formula powerset = Call("Powerset", effectiveOutput);
        Formula representationType = Call("OrderIso", observableAlgebra, powerset);
        Formula computation = Seq(
            representation, Open, eventFormula, Close, Sp, Eq, Sp,
            Call("image", Call("rangeFactorization", readout), eventFormula));

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, type, Comma,
            RowBreak, Grp(), readout, Colon, Sp, state, Sp, To, Sp, output, Comma,
            RowBreak, Grp(), Exists, Bang, Sp, representation, Colon, Sp,
            representationType, Comma,
            RowBreak, Grp(), Forall, Sp, eventFormula, InMacro, Sp,
            observableAlgebra, Comma, Sp, computation, Dot));
    }
}
