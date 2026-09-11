using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class SelfInterestConventionDeviationGainDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/SelfInterestConventionDeviationGain.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both players can gain by changing friendly to antagonistic tie-breaking.",
        H("Profitable Deviations towards Antagonistic Tie-Breaking"),
        Blocks(
            Paragraph(Text(
                "Bhagat, Kulkarni, Larsson and Murali, \"Tie-breaking in self interest "
                    + "cumulative subtraction games\", arXiv:2510.24280v2 (20 January 2026), "
                    + "Section 6, Problem 6 asks: \"Is it true that no player can have a "
                    + "positive discrepancy by going from AvF or FvA to AvA?\" The answer "
                    + "is no. The authors' own sentence immediately before the problem reads "
                    + "\"Experimental results point towards that this cannot happen if "
                    + "deviating towards AvA\"; their experiments pointed the other way.")),
            Paragraph(Text(
                "For subtraction set {7,12,13,38,50}, at heap 122 the AvF and AvA outcomes "
                    + "are (64,57) and (64,58), so Bob, the second player, gains by switching "
                    + "his own convention from friendly to antagonistic. At heap 172 the "
                    + "FvA and AvA outcomes are (107,64) and (108,64), so Alice, the opening "
                    + "player, gains by the same change. Problem 6 is a disjunction over "
                    + "AvF and FvA, and both disjuncts are refuted.")),
            Paragraph(Text(
                "Nothing about Conjecture 4, the FvF-to-AvA statement, is established. "
                    + "There is no classification of such subtraction sets and no claim "
                    + "that these are the only or the smallest witnesses. The paper supplies "
                    + "the question and Definition 2; the declarations are repository "
                    + "constructions. Nat denotes the natural numbers, List(Nat) a finite "
                    + "list, and .1 and .2 are pair projections.")),
            Definition("Convention", "convention", "Mover-relative conventions",
                Disp(Seq(F.Id("Convention"), Sp, Eq, Sp,
                    F.Id("Bool"), Sp, Times, Sp, F.Id("Bool"))),
                "A Boolean records whether a player is antagonistic. Component 1 belongs "
                    + "to the mover, and component 2 belongs to the opponent."),
            Definition("FvF", "fvf", "Friendly versus friendly",
                Disp(Seq(F.Id("FvF"), Sp, Eq, Sp, Pair(F.Id("false"), F.Id("false")))),
                "Both players use friendly tie-breaking."),
            Definition("AvF", "avf", "Antagonistic versus friendly",
                Disp(Seq(F.Id("AvF"), Sp, Eq, Sp, Pair(F.Id("true"), F.Id("false")))),
                "The mover is antagonistic and the opponent is friendly."),
            Definition("FvA", "fva", "Friendly versus antagonistic",
                Disp(Seq(F.Id("FvA"), Sp, Eq, Sp, Pair(F.Id("false"), F.Id("true")))),
                "The mover is friendly and the opponent is antagonistic."),
            Definition("AvA", "ava", "Antagonistic versus antagonistic",
                Disp(Seq(F.Id("AvA"), Sp, Eq, Sp, Pair(F.Id("true"), F.Id("true")))),
                "Both players use antagonistic tie-breaking."),
            Definition("dual", "dual", "Role reversal at every move",
                Disp(Seq(Forall, Sp, F.Id("convention"), Colon, Sp, F.Id("Convention"), Comma, Sp,
                    Call("dual", F.Id("convention")), Sp, Eq, Sp,
                    Pair(Project(F.Id("convention"), 2), Project(F.Id("convention"), 1)))),
                "Swap the two components at every move, including moves in mixed conventions."),
            Describe.Lean(DescribeId.Create("dual-involutive"),
                DeclarationHandle.Create(Prefix + "dual_involutive"),
                H("Two role reversals restore the convention"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("convention"), Colon, Sp, F.Id("Convention"), Comma, Sp,
                    Call("dual", Call("dual", F.Id("convention"))), Sp, Eq, Sp, F.Id("convention")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This holds for every convention without further hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dual-fixed-iff"),
                DeclarationHandle.Create(Prefix + "dual_fixed_iff"),
                H("Exactly the homogeneous conventions are fixed"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("convention"), Colon, Sp, F.Id("Convention"), Comma, Sp,
                    Call("dual", F.Id("convention")), Sp, Eq, Sp, F.Id("convention"), Sp, Iff, Sp,
                    Open, F.Id("convention"), Sp, Eq, Sp, F.Id("FvF"), Sp, Lor, Sp,
                    F.Id("convention"), Sp, Eq, Sp, F.Id("AvA"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equivalence covers all four Boolean pairs."))),
                DescribeRole.Theorem),
            Definition("Preferred", "preferred", "Own total with a convention-dependent tie-break",
                PreferredFormula(),
                "Own total is primary. On equality, an antagonistic mover minimizes the "
                    + "opponent's total and a friendly mover maximizes it. The Boolean "
                    + "conditional tests component 1 of the mover-relative convention."),
            Definition("outcome", "outcome", "Tabulated mover and opponent totals",
                Disp(new Formula.Aligned([
                    Parameters(),
                    Seq(CurrentOutcome(), Sp, Eq, Sp,
                        Call("readTable", Call("tabulate", F.Id("subtractions"),
                            Seq(F.Id("heap"), Plus, D(1))), F.Id("heap"), F.Id("convention"))),
                ])),
                "The result has type Nat times Nat: mover total followed by opponent total. "
                    + "readTable and tabulate are the module's private implementation functions. "
                    + "Structural tabulation stores all four conventions at each heap; a "
                    + "terminal position returns (0,0). The recurrence theorem proves the "
                    + "Definition 2 semantics, rather than assuming faithfulness of the table."),
            Describe.Lean(DescribeId.Create("outcome-recurrence"),
                DeclarationHandle.Create(Prefix + "outcome_recurrence"),
                H("Definition 2 holds for the tabulated outcome"),
                StatementSource.FromAuthor(RecurrenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both implications hold for every finite subtraction list, convention "
                        + "and natural heap. With no positive legal step the payoff is zero. "
                        + "Otherwise a positive legal step realizes the payoff, after role "
                        + "reversal, and that payoff is Preferred over every positive legal "
                        + "alternative. Heap subtraction is natural-number subtraction. "
                        + "The existential membership, both step bounds, the realization "
                        + "equality and the universally quantified optimality clause are "
                        + "all part of the proved statement."))),
                DescribeRole.Theorem),
            Definition("witnessSubtractions", "witness-subtractions", "The subtraction list",
                Disp(Seq(F.Id("witnessSubtractions"), Colon, Sp, Call("List", F.Id("Nat")),
                    Sp, Eq, Sp, OpenBracket, D(7), Comma, D(1, 2), Comma, D(1, 3),
                    Comma, D(3, 8), Comma, D(5, 0), CloseBracket)),
                "Both witnesses use this list, representing the subtraction set "
                    + "{7,12,13,38,50}. Only positive entries not exceeding the heap are legal. "
                    + "The general recurrence imposes no sorting or distinctness hypothesis."),
            Describe.Lean(DescribeId.Create("witness-values"),
                DeclarationHandle.Create(Prefix + "witness_values"),
                H("Four exact outcome pairs"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(WitnessOutcome("AvF", D(1, 2, 2)), Sp, Eq, Sp,
                        Pair(D(6, 4), D(5, 7)), Sp, Land),
                    Seq(WitnessOutcome("AvA", D(1, 2, 2)), Sp, Eq, Sp,
                        Pair(D(6, 4), D(5, 8)), Sp, Land),
                    Seq(WitnessOutcome("FvA", D(1, 7, 2)), Sp, Eq, Sp,
                        Pair(D(1, 0, 7), D(6, 4)), Sp, Land),
                    Seq(WitnessOutcome("AvA", D(1, 7, 2)), Sp, Eq, Sp,
                        Pair(D(1, 0, 8), D(6, 4))),
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Lean verifies all four equalities together using decide +kernel. "
                        + "These are evaluations of the tabulation whose recurrence is proved, "
                        + "not assumed values or outputs trusted from an external search."))),
                DescribeRole.Theorem),
            Definition("noPositiveDiscrepancyToAvA", "no-positive-discrepancy-to-ava",
                "Problem 6 as a proposition", NoPositiveDiscrepancyFormula(),
                "For every subtraction list and heap, Bob's second component after AvF-to-AvA "
                    + "and Alice's first component after FvA-to-AvA do not exceed their values "
                    + "before the respective changes. Both inequalities are required."),
            Describe.Lean(DescribeId.Create("both-deviations-refute-no-positive-discrepancy"),
                DeclarationHandle.Create(Prefix + "both_deviations_refute_no_positive_discrepancy"),
                H("Typed refutation of Problem 6"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, F.Id("noPositiveDiscrepancyToAvA")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This closed theorem negates the proposition without hypotheses. "
                        + "It uses both audited strict gains, for Bob at heap 122 and Alice "
                        + "at heap 172, to contradict the sum of the claimed upper bounds."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("both-deviations-profitable"),
                DeclarationHandle.Create(Prefix + "both_deviations_profitable"),
                H("Both changes towards AvA are profitable"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Project(WitnessOutcome("AvF", D(1, 2, 2)), 2), Sp, Lt, Sp,
                        Project(WitnessOutcome("AvA", D(1, 2, 2)), 2), Sp, Land),
                    Seq(Project(WitnessOutcome("FvA", D(1, 7, 2)), 1), Sp, Lt, Sp,
                        Project(WitnessOutcome("AvA", D(1, 7, 2)), 1)),
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There are no hypotheses. Both strict inequalities are conclusions: "
                        + "Bob gains from 57 to 58 at heap 122, and Alice gains from 107 to "
                        + "108 at heap 172. Each changes only their own friendly convention "
                        + "to antagonistic while the other player remains antagonistic."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string declaration, string id, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula Project(Formula pair, byte component) =>
        Seq(Open, pair, Close, Dot, D(component));

    private static Formula Parameters() => Seq(
        Forall, Sp, F.Id("subtractions"), Colon, Sp, Call("List", F.Id("Nat")), Comma, Sp,
        Forall, Sp, F.Id("convention"), Colon, Sp, F.Id("Convention"), Comma, Sp,
        Forall, Sp, F.Id("heap"), Colon, Sp, F.Id("Nat"), Comma);

    private static Formula CurrentOutcome() =>
        Call("outcome", F.Id("subtractions"), F.Id("convention"), F.Id("heap"));

    private static Formula WitnessOutcome(string convention, Formula heap) =>
        Call("outcome", F.Id("witnessSubtractions"), F.Id(convention), heap);

    private static Formula AvailableStep() => Seq(
        Exists, Sp, F.Id("step"), Sp, InMacro, Sp, F.Id("subtractions"), Comma, Sp,
        D(0), Sp, Lt, Sp, F.Id("step"), Sp, Land, Sp,
        F.Id("step"), Sp, Leq, Sp, F.Id("heap"));

    private static Formula MovePayoff(string step)
    {
        var continuation = Call("outcome", F.Id("subtractions"),
            Call("dual", F.Id("convention")), Seq(F.Id("heap"), Minus, F.Id(step)));
        return Pair(Seq(Project(continuation, 2), Plus, F.Id(step)), Project(continuation, 1));
    }

    private static Formula RecurrenceFormula() => Disp(new Formula.Aligned([
        Parameters(),
        Seq(Open, Open, Neg, Sp, Open, AvailableStep(), Close, Close, Sp, Rightarrow, Sp,
            CurrentOutcome(), Sp, Eq, Sp, Pair(D(0), D(0)), Close, Sp, Land),
        Seq(Open, Open, AvailableStep(), Close, Sp, Rightarrow),
        Seq(Exists, Sp, F.Id("step"), Sp, InMacro, Sp, F.Id("subtractions"), Comma, Sp,
            D(0), Sp, Lt, Sp, F.Id("step"), Sp, Land, Sp,
            F.Id("step"), Sp, Leq, Sp, F.Id("heap"), Sp, Land),
        Seq(CurrentOutcome(), Sp, Eq, Sp, MovePayoff("step"), Sp, Land),
        Seq(Forall, Sp, F.Id("alternative"), Sp, InMacro, Sp, F.Id("subtractions"), Comma, Sp,
            D(0), Sp, Lt, Sp, F.Id("alternative"), Sp, Rightarrow, Sp,
            F.Id("alternative"), Sp, Leq, Sp, F.Id("heap"), Sp, Rightarrow),
        Seq(Call("Preferred", F.Id("convention"), CurrentOutcome(), MovePayoff("alternative")), Close),
    ]));

    private static Formula NoPositiveDiscrepancyFormula() => Disp(new Formula.Aligned([
        Seq(F.Id("noPositiveDiscrepancyToAvA"), Sp, Iff),
        Seq(Forall, Sp, F.Id("subtractions"), Colon, Sp, Call("List", F.Id("Nat")), Comma, Sp,
            Forall, Sp, F.Id("heap"), Colon, Sp, F.Id("Nat"), Comma),
        Seq(Project(Call("outcome", F.Id("subtractions"), F.Id("AvA"), F.Id("heap")), 2),
            Sp, Leq, Sp,
            Project(Call("outcome", F.Id("subtractions"), F.Id("AvF"), F.Id("heap")), 2),
            Sp, Land),
        Seq(Project(Call("outcome", F.Id("subtractions"), F.Id("AvA"), F.Id("heap")), 1),
            Sp, Leq, Sp,
            Project(Call("outcome", F.Id("subtractions"), F.Id("FvA"), F.Id("heap")), 1)),
    ]));

    private static Formula PreferredFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, F.Id("convention"), Colon, Sp, F.Id("Convention"), Comma, Sp,
            Forall, Sp, F.Id("chosen"), Comma, Sp, F.Id("alternative"), Colon, Sp,
            F.Id("Nat"), Sp, Times, Sp, F.Id("Nat"), Comma),
        Seq(Call("Preferred", F.Id("convention"), F.Id("chosen"), F.Id("alternative")), Sp, Iff, Sp,
            Project(F.Id("alternative"), 1), Sp, Leq, Sp, Project(F.Id("chosen"), 1), Sp, Land),
        Seq(Open, Project(F.Id("alternative"), 1), Sp, Eq, Sp, Project(F.Id("chosen"), 1),
            Sp, Rightarrow, Sp, F.Id("if"), Sp, Project(F.Id("convention"), 1), Sp,
            F.Id("then"), Sp, Project(F.Id("chosen"), 2), Sp, Leq, Sp, Project(F.Id("alternative"), 2),
            Sp, F.Id("else"), Sp, Project(F.Id("alternative"), 2), Sp, Leq, Sp,
            Project(F.Id("chosen"), 2), Close),
    ]));

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
}
