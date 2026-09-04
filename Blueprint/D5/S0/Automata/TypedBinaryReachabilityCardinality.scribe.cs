using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class TypedBinaryReachabilityCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In a reachable binary Zeckendorf-typed partial DFAO, every "
            + "previous-one state has a distinct previous-zero predecessor "
            + "under input one, hence the previous-one fiber has no more "
            + "states than the previous-zero fiber.",
        H("Reachability Cardinality in Binary Typed DFAOs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reachable-one-state-has-zero-predecessor"),
                DeclarationHandle.Create(
                    "D5/S0/Automata/TypedBinaryReachabilityCardinality.reachable_previousOne_has_one_predecessor"),
                H("Every reachable previous-one state has a previous-zero predecessor"),
                StatementSource.FromAuthor(PredecessorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A run ending in a previous-one state cannot be empty. Decomposing its input at the final symbol and using the typed transition law shows that the final symbol is one and that the predecessor state has previous-zero type."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("previous-one-fiber-cardinality-bound"),
                DeclarationHandle.Create(
                    "D5/S0/Automata/TypedBinaryReachabilityCardinality.previousOne_card_le_previousZero_card_of_allStatesReachable"),
                H("The previous-one fiber has no more states than the previous-zero fiber"),
                StatementSource.FromAuthor(CardinalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Choose one previous-zero predecessor for every previous-one state. Determinism makes this choice injective, because one source state on the same input symbol cannot reach two distinct targets.")),
                    Paragraph(Text(
                        "The result removes every exact reachable type split with more previous-one than previous-zero states before SAT search. It does not by itself exclude balanced or previous-zero-heavy splits."))),
                DescribeRole.Theorem)),
        []));

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

    private static Formula PredecessorFormula() => Disp(Seq(
        Exists, Sp, F.Id("s"), Comma, Sp,
        Call("stateType", F.Id("s")), Sp, Eq, Sp,
        Call("previousZero"), Sp, Land, Sp,
        Call("step", F.Id("s"), D(1)), Sp, Eq, Sp,
        Call("some", F.Id("t"))));

    private static Formula CardinalityFormula() => Disp(Seq(
        Call("card", Call("PreviousOneState", F.Id("M"))),
        Sp, Leq, Sp,
        Call("card", Call("PreviousZeroState", F.Id("M")))));
}
