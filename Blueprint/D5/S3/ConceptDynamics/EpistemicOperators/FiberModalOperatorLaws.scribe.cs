using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.EpistemicOperators;

internal sealed class FiberModalOperatorLawsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/EpistemicOperators/FiberModalOperatorLaws."
            + "fiber_knowledge_and_possibility_operator_laws";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fiber knowledge is an interior operator and fiber possibility its dual closure.",
        H("Fiber Modal Operator Laws"),
        Blocks(Describe.Lean(
            DescribeId.Create("fiber-knowledge-and-possibility-operator-laws"),
            DeclarationHandle.Create(Declaration),
            H("Knowledge and possibility on concept fibers"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The readout C constructs both operators on the exact source carrier. "
                        + "Knowledge requires universal truth on the current readout fiber, "
                        + "while possibility requires an existential witness on that fiber.")),
                Paragraph(Text(
                    "The first four public clauses state factivity, monotonicity, "
                        + "idempotence, and conjunction preservation for knowledge. The next "
                        + "three state extensivity, monotonicity, and idempotence for "
                        + "possibility.")),
                Paragraph(Text(
                    "The final public clause is the classical complement duality. Its proof "
                        + "uses classical negation only in the direction from absence of a "
                        + "counterexample to universal fiber truth.")),
                Paragraph(Text(
                    "The proof imports the canonical fiber-knowledge primitive, its frozen "
                        + "partition-interior characterization, and the frozen topological "
                        + "knowledge laws rather than declaring another family primitive."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
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
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stateType = F.Id("X");
        Formula coordinateType = F.Id("B");
        Formula readout = F.Id("C");
        Formula predicate = F.Id("P");
        Formula otherPredicate = F.Id("Q");
        Formula state = F.Id("a");
        Formula witness = F.Id("x");
        Formula setType = Apply(F.Id("Set"), stateType);
        Formula knowledge(Formula value) => Apply(F.Id("Knowledge"), readout, value);
        Formula possibility(Formula value) => Apply(F.Id("Possibility"), readout, value);
        Formula intersection(Formula left, Formula right) =>
            Apply(F.Id("intersection"), left, right);
        Formula complement(Formula value) => Apply(F.Id("complement"), value);
        Formula readoutAt(Formula value) => Apply(readout, value);

        Formula knowledgeDefinition = Seq(
            Forall, Sp, predicate, Colon, Sp, setType, Comma, Sp,
            state, Colon, Sp, stateType, Comma, Sp,
            state, Sp, InMacro, Sp, knowledge(predicate), Sp, Iff, Sp,
            Forall, Sp, witness, Colon, Sp, stateType, Comma, Sp,
            readoutAt(witness), Sp, Eq, Sp, readoutAt(state), Sp,
            Rightarrow, Sp, witness, Sp, InMacro, Sp, predicate);
        Formula possibilityDefinition = Seq(
            Forall, Sp, predicate, Colon, Sp, setType, Comma, Sp,
            state, Colon, Sp, stateType, Comma, Sp,
            state, Sp, InMacro, Sp, possibility(predicate), Sp, Iff, Sp,
            Exists, Sp, witness, Colon, Sp, stateType, Comma, Sp,
            readoutAt(witness), Sp, Eq, Sp, readoutAt(state), Sp, Land, Sp,
            witness, Sp, InMacro, Sp, predicate);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, coordinateType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            readout, Colon, Sp, Apply(F.Id("Concept"), stateType, coordinateType), Comma,
            RowBreak, Grp(),
            knowledgeDefinition, Comma,
            RowBreak, Grp(),
            possibilityDefinition, Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, predicate, Colon, Sp, setType, Comma, Sp,
            knowledge(predicate), Sp, Subseteq, Sp, predicate, Close, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, predicate, Comma, Sp, otherPredicate, Colon, Sp, setType,
            Comma, Sp, predicate, Sp, Subseteq, Sp, otherPredicate, Sp,
            Rightarrow, Sp, knowledge(predicate), Sp, Subseteq, Sp,
            knowledge(otherPredicate), Close, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, predicate, Colon, Sp, setType, Comma, Sp,
            knowledge(knowledge(predicate)), Sp, Eq, Sp, knowledge(predicate), Close,
            Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, predicate, Comma, Sp, otherPredicate, Colon, Sp, setType,
            Comma, Sp, knowledge(intersection(predicate, otherPredicate)), Sp, Eq, Sp,
            intersection(knowledge(predicate), knowledge(otherPredicate)), Close, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, predicate, Colon, Sp, setType, Comma, Sp,
            predicate, Sp, Subseteq, Sp, possibility(predicate), Close, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, predicate, Comma, Sp, otherPredicate, Colon, Sp, setType,
            Comma, Sp, predicate, Sp, Subseteq, Sp, otherPredicate, Sp,
            Rightarrow, Sp, possibility(predicate), Sp, Subseteq, Sp,
            possibility(otherPredicate), Close, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, predicate, Colon, Sp, setType, Comma, Sp,
            possibility(possibility(predicate)), Sp, Eq, Sp, possibility(predicate), Close,
            Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, predicate, Colon, Sp, setType, Comma, Sp,
            knowledge(predicate), Sp, Eq, Sp,
            complement(possibility(complement(predicate))), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
