using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class RankedCostDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A termination rank and a separate potential construct a goal word with state-dependent charges.",
        H("Goal Words with an Independent Rank and Cost Budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ranked-word-cost"),
                DeclarationHandle.Create("D5/S1/Words/RankedCostDescent.wordCost"),
                H("Charges are evaluated at the states actually reached"),
                StatementSource.FromAuthor(CostDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let X and A be state and letter types in independent universes, and let t be the transition and c its natural-valued charge. The notation run(t,w,s) means the native left fold w.foldl t s. The empty word is nil, and cons(a,w) places a before w. The function cost(t,c,s,w) is wordCost t c s w: after paying c(s,a), the remaining charges are evaluated starting at t(s,a), rather than at the original state. Costs may be zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ranked-cost-goal-word"),
                DeclarationHandle.Create(
                    "D5/S1/Words/RankedCostDescent.exists_goal_word_cost_add_potential_le"),
                H("Rank ensures termination while potential pays the charges"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an arbitrary goal predicate G, let R be a natural-valued termination rank and V a separate natural-valued budget potential. At every state s outside G, assume a finite word a reaches a strictly lower rank and that its actual accumulated charge plus the endpoint potential is at most V(s). Then every starting state x admits a word reaching G with total charge plus final potential at most V(x). No finiteness, nonemptiness or decidable equality is required of either type. The endpoint potential may be positive, and zero-cost progress is allowed even when V is constant.")),
                    Paragraph(Text(
                        "Strong induction on R(s) constructs the word. At a goal, use nil. Otherwise choose the local word a, recursively construct a goal suffix b at its lower-rank endpoint, and concatenate a followed by b. Cost concatenation uses the state reached after a as the suffix's starting state. The two budget inequalities cancel the intermediate potential. Only local endpoints must decrease in rank; no rank, potential or goal condition is imposed on their intermediate states.")),
                    Paragraph(Text(
                        "A preparation-and-execution system has states (n,ready), goal n=0, potential n+5 and rank 2n plus one when ready is false. Preparation changes (n,false) to (n,true) at zero charge. Execution changes (n,true) to (n-1,false) at charge one. For n>0 both operations decrease rank and preserve the paid budget. Thus every start reaches the goal with total charge plus the residual five bounded by its initial potential. From (3,false), a preparation followed by execution has charge one and reaches (2,false); preparation alone leaves the potential unchanged.")),
                    Paragraph(Text(
                        "For countdown on natural numbers, take R(n)=n, V(n)=2n+5 and charge one at even states and two at odd states. Every nonterminal predecessor step is affordable, so the theorem bounds the actual state-dependent total charge and retains a final potential of five. For example, the two steps from three through two to one cost three. A separate zero-charge countdown with constant potential seven shows that progress does not need to consume budget.")),
                    Paragraph(Text(
                        "When every charge is one, cost equals word length. Setting R=V recovers the potential-drop word bound, including its independently polymorphic parameters and empty alphabet. This also gives the finite-uncertainty application on natural numbers: predecessor image decreases the maximum together with zero until cardinality is at most one. Cardinality itself may plateau, as in {0,2} to {0,1}. This application uses an infinite ambient state space.")),
                    Paragraph(Text(
                        "Strict rank progress is essential: an identity transition with zero charges and an always-false goal satisfies local affordability but never reaches the goal. The theorem asserts existence, without a bound on finding local words, total word length when zero charges are allowed, shortest-word optimality or polynomial runtime. Native controller realization, legal operations, initialization and correct output need their own conditions; the polynomial native-controller claim of Section 21.5 in the capacity-coherence volume is not covered. The accounting is the standard potential method discussed in Library/Computability/tarjan1985amortized.md; no literature novelty is claimed."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Run(string word, string state) =>
        Call("run", F.Id("t"), F.Id(word), F.Id(state));

    private static Formula Cost(Formula word, Formula state) =>
        Call("cost", F.Id("t"), F.Id("c"), state, word);

    private static Formula CostDefinition() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("X"), Colon, Sp, Call("Type", F.Id("u")), Comma, Sp,
        F.Id("A"), Colon, Sp, Call("Type", F.Id("v")), Comma,
        RowBreak, Grp(),
        Forall, Sp, F.Id("t"), Colon, Sp, F.Id("X"), Sp, To, Sp,
        F.Id("A"), Sp, To, Sp, F.Id("X"), Comma, Sp,
        F.Id("c"), Colon, Sp, F.Id("X"), Sp, To, Sp,
        F.Id("A"), Sp, To, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        F.Id("s"), Colon, Sp, F.Id("X"), Comma,
        RowBreak, Grp(),
        Cost(Call("nil"), F.Id("s")), Sp, Eq, Sp, F.D(0), Sp, Land, Sp,
        Forall, Sp, F.Id("a"), Colon, Sp, F.Id("A"), Comma, Sp,
        F.Id("w"), Colon, Sp, Call("List", F.Id("A")), Comma,
        RowBreak, Grp(),
        Cost(Call("cons", F.Id("a"), F.Id("w")), F.Id("s")), Sp, Eq, Sp,
        Call("c", F.Id("s"), F.Id("a")), Sp, Plus, Sp,
        Cost(F.Id("w"), Call("t", F.Id("s"), F.Id("a"))), Dot,
        End, Grp(F.Id("gathered"))));

    private static Formula Statement() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("X"), Colon, Sp, Call("Type", F.Id("u")), Comma, Sp,
        F.Id("A"), Colon, Sp, Call("Type", F.Id("v")), Comma,
        RowBreak, Grp(),
        Forall, Sp, F.Id("t"), Colon, Sp, F.Id("X"), Sp, To, Sp,
        F.Id("A"), Sp, To, Sp, F.Id("X"), Comma, Sp,
        F.Id("G"), Colon, Sp, F.Id("X"), Sp, To, Sp, F.Id("Prop"), Comma,
        RowBreak, Grp(),
        F.Id("R"), Comma, Sp, F.Id("V"), Colon, Sp,
        F.Id("X"), Sp, To, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        F.Id("c"), Colon, Sp, F.Id("X"), Sp, To, Sp,
        F.Id("A"), Sp, To, Sp, Mathbb, Grp(F.Id("N")), Comma,
        RowBreak, Grp(),
        F.Id("x"), Colon, Sp, F.Id("X"), Comma,
        RowBreak, Grp(),
        Open, Forall, Sp, F.Id("s"), Colon, Sp, F.Id("X"), Comma, Sp,
        Call("not", Call("G", F.Id("s"))), Sp, Rightarrow, Sp,
        Exists, Sp, F.Id("a"), Colon, Sp, Call("List", F.Id("A")), Comma,
        RowBreak, Grp(),
        Call("R", Run("a", "s")), Sp, Lt, Sp, Call("R", F.Id("s")),
        Sp, Land, Sp, Cost(F.Id("a"), F.Id("s")), Sp, Plus, Sp,
        Call("V", Run("a", "s")), Sp, Leq, Sp, Call("V", F.Id("s")), Close,
        RowBreak, Grp(), Rightarrow, Sp,
        Exists, Sp, F.Id("w"), Colon, Sp, Call("List", F.Id("A")), Comma,
        RowBreak, Grp(),
        Call("G", Run("w", "x")), Sp, Land, Sp,
        Cost(F.Id("w"), F.Id("x")), Sp, Plus, Sp, Call("V", Run("w", "x")),
        Sp, Leq, Sp, Call("V", F.Id("x")), Dot,
        End, Grp(F.Id("gathered"))));
}
