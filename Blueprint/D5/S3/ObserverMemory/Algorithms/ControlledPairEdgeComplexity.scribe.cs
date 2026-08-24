using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class ControlledPairEdgeComplexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit controlled pair-edge construction has input-linear quadratic resource bounds.",
        H("Controlled Pair-Edge Complexity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("controlled-pair-edge-complexity"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/ControlledPairEdgeComplexity."
                        + "controlled_pair_edge_complexity"),
                H("Explicit controlled pair edges have quadratic state complexity"),
                StatementSource.FromAuthor(ComplexityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the input and state carriers be finite, and let each input select "
                            + "a deterministic state-update channel. For one channel, the "
                            + "canonical explicit reverse table contains the reversed edge of "
                            + "every ordered state pair.")),
                    Paragraph(Text(
                        "Controlled time and storage are constructed by summing the repository's "
                            + "per-channel reverse-search budgets over all inputs. Thus time is "
                            + "at most twice, and storage at most three times, the input count "
                            + "times the square of the state count.")),
                    Paragraph(Text(
                        "The proof directly applies reverse_bfs_correct_and_quadratic to each "
                            + "controlled channel and sums its two resource inequalities. "
                            + "Repository and pinned-library searches found no theorem already "
                            + "packaging both controlled full-table bounds.")),
                    Paragraph(Text(
                        "This formalizes the two boxed resource clauses of theorem 25.6. The "
                            + "subsequent online-enumeration sentence is qualitative and depends "
                            + "on implementation-specific structure, so it is not asserted as a "
                            + "universal mathematical clause."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ComplexityFormula()
    {
        Formula inputs = F.Id("U");
        Formula states = F.Id("Y");
        Formula update = F.Id("F");
        Formula inputCount = Call("card", inputs);
        Formula stateCount = Call("card", states);
        Formula stateCountSquared = new Formula.Power(stateCount, Seq(D(2)));
        Formula timeBound = Seq(
            Call("controlledTimeBudget", update), Sp, Leq, Sp,
            D(2), Sp, Times, Sp, inputCount, Sp, Times, Sp, stateCountSquared);
        Formula spaceBound = Seq(
            Call("controlledSpaceBudget", update), Sp, Leq, Sp,
            D(3), Sp, Times, Sp, inputCount, Sp, Times, Sp, stateCountSquared);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, inputs, Comma, Sp, states, Comma, RowBreak, Grp(),
            Call("Finite", inputs), Comma, Sp, Call("Finite", states), Comma,
            RowBreak, Grp(),
            update, Colon, Sp, inputs, Sp, To, Sp, states, Sp, To, Sp, states,
            Comma, RowBreak, Grp(),
            Open, timeBound, Close, Sp, Land, RowBreak, Grp(),
            Open, spaceBound, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
