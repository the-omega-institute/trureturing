using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class GreedyBrickCapacityTotalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/GreedyBrickCapacityTotality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural gap transfers realize the literal row scan and supported contiguous brick placement.",
        H("Greedy brick rows and capacities"),
        Blocks(
            Paragraph(Text("Capacities and occupied row widths are stored from top to bottom. "
                + "The function widths forms cumulative sums of the natural capacities. "
                + "Zero gaps are allowed. The published A395531 Python generator stores rows "
                + "in the opposite order. sourceRowStep reverses that convention: it first "
                + "tests a new top row, then scans existing rows downwards, extending the "
                + "first row whose width plus the new brick width is supported below. "
                + "The floor is always available. This model uses unbounded natural numbers.")),
            Describe.Lean(DescribeId.Create("step-invariants"),
                DeclarationHandle.Create(Prefix + "step_invariants"),
                H("Capacity transfer bounds and exact area increment"),
                StatementSource.FromAuthor(StepInvariants()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every capacity is at most 2n-1. A placement preserves "
                    + "height or creates exactly one row, preserves the capacity bound, and "
                    + "increases weighted area by n. The donor-transfer induction proves "
                    + "all four conclusions on arbitrary bounded natural capacity lists."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reachable-invariants"),
                DeclarationHandle.Create(Prefix + "reachable_invariants"),
                H("All finite literal trajectories have the exact placed area"),
                StatementSource.FromAuthor(ReachableInvariants()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction from the empty wall gives the capacity cap "
                    + "2N-1 and area equal to the sum of labels 0 through N. Height is "
                    + "monotone and increases by at most one at each placement."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reachable-rows"),
                DeclarationHandle.Create(Prefix + "reachable_rows"),
                H("Positive monotone reconstructed rows and exact inverse gaps"),
                StatementSource.FromAuthor(ReachableRows()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each positive endpoint N, cumulative gap sums "
                    + "give positive widths increasing downwards, preserve height and "
                    + "area, and recover the original capacities under the inverse map."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("birth-totality"),
                DeclarationHandle.Create(Prefix + "birth_totality"),
                H("Every positive row has an actual least birth"),
                StatementSource.FromAuthor(BirthTotality()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact area and uniform capacity bound force "
                    + "every positive height to be reached. Its least reaching endpoint "
                    + "has exactly that height. The first birth is at most 1; for m>=2 "
                    + "the endpoint is at most 2m(m-1)-1. No missing-row default is used."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("row-transition-correspondence"),
                DeclarationHandle.Create(Prefix + "row_transition_correspondence"),
                H("The two recursive algorithms are conjugate"),
                StatementSource.FromAuthor(Transition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural capacity list and positive brick width, "
                    + "reconstructing widths after transfer agrees with applying the source row scan. "
                    + "The recursive proof tracks a common offset through the donor scan. "
                    + "No reachability premise, capacity bound or conjectured identity is used."))),
                DescribeRole.Theorem),
            Paragraph(Text("occupied(ws,u,y) means that unit cell (u,y) belongs to the wall. "
                + "Row zero is the floor; each row is the half-open interval [0,w). "
                + "AppendSite enumerates supported existing-row frontiers without making a "
                + "greedy choice. PlacementSite also permits a supported new top row. "
                + "LegalBrick requires disjointness over the entire new interval, support "
                + "over its entire bottom unless on the floor, and left contact with the "
                + "axis or the occupied wall. BrickAddition requires the exact union of "
                + "old occupied cells with the new interval, together with those three constraints.")),
            Describe.Lean(DescribeId.Create("source-row-geometry"),
                DeclarationHandle.Create(Prefix + "source_row_geometry"),
                H("The source scan realizes the leftmost highest legal placement"),
                StatementSource.FromAuthor(Geometry()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For widths increasing downwards, the source scan gives "
                    + "one legal brick addition. Its left endpoint is no larger, and its row "
                    + "is no lower, than those of every LegalBrick position. The proof also "
                    + "shows internally that every physical position satisfying the stated "
                    + "cell constraints is among the enumerated frontiers. Positive row "
                    + "widths are supplied for actual nonempty trajectories by the existing "
                    + "reachable_rows theorem; positive least births use birth_totality."))),
                DescribeRole.Theorem),
            Paragraph(Text("birthBound(m) is 1 when m=1 and 2m(m-1)-1 otherwise. "
                + "sumRangeId(k) denotes the sum of the natural labels in range(k). "
                + "These results establish the row algorithm and the contiguous "
                + "integer-cell placement model. The labelled-history and continuous-plane theorems "
                + "are supplied by the separate GreedyBrickLabelledHistory source. The original OEIS self-composition identity is not proved. "
                + "Source statements are attributed to OEIS A395531 and A233380; the "
                + "algorithm-correspondence and geometric proofs are derivations of the stated rule.")))));

    private static Formula StepInvariants()
    {
        Formula n = F.Id("n"), cs = F.Id("cs"), next = Call("step", n, cs);
        Formula cap = MinusOf(TimesOf(D(2), n), D(1));
        Formula bounds = And(Leq(Call("length", cs), Call("length", next)),
            And(Leq(Call("length", next), PlusOf(Call("length", cs), D(1))),
                And(Capped(next, cap), Equal(Call("area", next), PlusOf(Call("area", cs), n)))));
        return Disp(All("n", Naturals, All("cs", Lists,
            Implies(And(Less(D(0), n), Capped(cs, cap)), bounds))));
    }

    private static Formula ReachableInvariants()
    {
        Formula n = F.Id("N"), cs = Call("trajectory", n);
        Formula next = Call("trajectory", PlusOf(n, D(1)));
        return Disp(All("N", Naturals, And(Capped(cs, MinusOf(TimesOf(D(2), n), D(1))),
            And(Equal(Call("area", cs), Call("sumRangeId", PlusOf(n, D(1)))),
                And(Leq(Call("length", cs), Call("length", next)),
                    Leq(Call("length", next), PlusOf(Call("length", cs), D(1))))))));
    }

    private static Formula ReachableRows()
    {
        Formula n = F.Id("N"), cs = Call("trajectory", n), ws = Call("widths", cs);
        Formula positive = All("w", Naturals,
            Implies(Call("member", F.Id("w"), ws), Less(D(0), F.Id("w"))));
        return Disp(All("N", Naturals, Implies(Less(D(0), n),
            And(Equal(Call("length", ws), Call("length", cs)),
                And(Call("PairwiseLe", ws), And(Equal(Call("sum", ws), Call("area", cs)),
                    And(Equal(Call("capacities", ws), cs), positive)))))));
    }

    private static Formula BirthTotality()
    {
        Formula m = F.Id("m"), b = F.Id("B"), k = F.Id("K");
        Formula minimal = All("K", Naturals,
            Implies(Less(k, b), Less(Call("length", Call("trajectory", k)), m)));
        Formula bound = Call("birthBound", m);
        return Disp(All("m", Naturals, Implies(Leq(D(1), m), Exists("B", Naturals,
            And(Less(D(0), b), And(Equal(Call("length", Call("trajectory", b)), m),
                And(minimal, Leq(b, bound))))))));
    }

    private static Formula Capped(Formula list, Formula bound) => All("c", Naturals,
        Implies(Call("member", F.Id("c"), list), Leq(F.Id("c"), bound)));
    private static Formula PlusOf(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula MinusOf(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula TimesOf(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);

    private static Formula Transition() => Disp(All("n", Naturals,
        All("cs", Lists, Implies(Less(D(0), F.Id("n")), Equal(
            Call("widths", Call("step", F.Id("n"), F.Id("cs"))),
            Call("sourceRowStep", F.Id("n"), Call("widths", F.Id("cs"))))))));

    private static Formula Geometry()
    {
        Formula n = F.Id("n"), ws = F.Id("ws"), x = F.Id("x"), y = F.Id("y");
        Formula xp = F.Id("xp"), yp = F.Id("yp");
        Formula optimal = All("xp", Naturals, All("yp", Naturals,
            Implies(Call("LegalBrick", n, ws, xp, yp), And(Leq(x, xp), Leq(yp, y)))));
        Formula addition = Call("BrickAddition", ws, Call("sourceRowStep", n, ws), n, x, y);
        Formula result = Exists("x", Naturals, Exists("y", Naturals,
            And(Call("PlacementSite", n, ws, x, y), And(optimal, addition))));
        return Disp(All("n", Naturals, All("ws", Lists,
            Implies(And(Less(D(0), n), Call("PairwiseLe", ws)), result))));
    }

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Lists => Call("List", Naturals);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
