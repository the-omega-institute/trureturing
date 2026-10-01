using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class GreedyBrickLabelledHistoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/GreedyBrickLabelledHistory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A labelled real-plane brick history realizes the literal capacity trajectory.",
        H("Labelled supported brick geometry"),
        Blocks(
            Paragraph(Text("OEIS A395531 places bricks of widths 1,2,3,... in the first "
                + "quadrant, as close to x=0 as possible and on the highest supported row "
                + "without overhang. The results below use the existing exact row scan "
                + "and capacity conjugacy. rowEnd(ws,y) is the right endpoint of row y, "
                + "with an empty slice outside the stored wall. A brick rectangle is "
                + "[x,x+n) times [y,y+1); half-open ownership permits shared boundaries "
                + "and implies disjoint ordinary interiors.")),
            Paragraph(Text("wall(ws,t,z) holds when t is nonnegative and lies below the "
                + "right endpoint of the unique unit-height row containing z. legal "
                + "requires first-quadrant coordinates, nonoverlap and full bottom "
                + "support on the floor or the upper face of an occupied row. It "
                + "allows arbitrary real horizontal endpoints and imposes no left "
                + "contact. sourceOptimal requires legality and proves that x is "
                + "minimal and y is maximal among all those physical competitors.")),
            Describe.Lean(DescribeId.Create("continuous-row-geometry"),
                DeclarationHandle.Create(Prefix + "continuous_row_geometry"),
                H("The discrete scan has the physical real-plane optimum"),
                StatementSource.FromAuthor(Continuous()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive n and monotone natural width "
                    + "list, the scan supplies natural x,y. A real competitor is "
                    + "reduced to the same row's occupied frontier: nonoverlap bounds "
                    + "its x below by that frontier and support makes the frontier "
                    + "eligible. The existing discrete theorem supplies the ordering. "
                    + "Floor-slice equivalences transport the exact cell addition to "
                    + "the real half-open rectangle union."))),
                DescribeRole.Theorem),
            Paragraph(Text("labelledWall(pos,N) is the union of rectangles labelled "
                + "1 through N, each with width equal to its label and position pos(i). "
                + "NatToNatPair denotes functions from natural labels to natural "
                + "coordinate pairs; x(pos,i) and y(pos,i) are their two coordinates. "
                + "historyLegal uses only these previously placed labelled rectangles: "
                + "the bottom is on the floor or every point under it lies on an old "
                + "brick's upper face. historyOptimal compares against all such real "
                + "competitors. These definitions contain no scan or assumed optimum.")),
            Describe.Lean(DescribeId.Create("actual-labelled-history"),
                DeclarationHandle.Create(Prefix + "actual_labelled_history"),
                H("One labelled history realizes every finite prefix"),
                StatementSource.FromAuthor(History()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One position function is chosen for every "
                    + "positive brick label. Induction proves that every finite union "
                    + "equals the wall reconstructed from the actual trajectory. "
                    + "The union then transports full support in both directions "
                    + "between row geometry and the actual labelled brick faces. "
                    + "Every step is physically optimal in that preceding history, "
                    + "and distinct labels have disjoint half-open rectangles. "
                    + "Closed bottom support includes the right endpoint: an old "
                    + "brick covering the point half a unit before it has an integer "
                    + "right endpoint at least as far to the right."))),
                DescribeRole.Theorem),
            Paragraph(Text("These are derivations of the published "
                + "placement rule, attributed to OEIS A395531 and A233380. They do "
                + "not prove the OEIS self-composition identity. "
                + "The geometric statements use unbounded mathematical naturals "
                + "and real coordinates, not machine-integer simulations.")))));

    private static Formula Continuous()
    {
        Formula n = F.Id("n"), ws = F.Id("ws"), x = F.Id("x"), y = F.Id("y");
        Formula t = F.Id("t"), z = F.Id("z");
        Formula union = All("t", Reals, All("z", Reals,
            Equivalent(Call("wall", Call("sourceRowStep", n, ws), t, z),
                Or(Call("wall", ws, t, z), Call("rectangle", n, x, y, t, z)))));
        Formula result = Exists("x", Naturals, Exists("y", Naturals,
            And(Call("PlacementSite", n, ws, x, y),
                And(Call("sourceOptimal", n, ws, x, y), union))));
        return Disp(All("n", Naturals, All("ws", Lists,
            Implies(And(Less(D(0), n), Call("PairwiseLe", ws)), result))));
    }

    private static Formula History()
    {
        Formula pos = F.Id("pos"), n = F.Id("n"), endpoint = F.Id("N");
        Formula t = F.Id("t"), z = F.Id("z"), i = F.Id("i"), j = F.Id("j");
        Formula union = All("N", Naturals, All("t", Reals, All("z", Reals,
            Equivalent(Call("wall", Call("widths", Call("trajectory", endpoint)), t, z),
                Call("labelledWall", pos, endpoint, t, z)))));
        Formula optimal = All("n", Naturals, Implies(Less(D(0), n),
            Call("historyOptimal", pos, Seq(n, Sp, Minus, Sp, D(1)), n,
                Call("x", pos, n), Call("y", pos, n))));
        Formula disjoint = All("i", Naturals, All("j", Naturals,
            Implies(And(Less(D(0), i), Less(i, j)), All("t", Reals, All("z", Reals,
                Implies(Call("rectangle", i, Call("x", pos, i), Call("y", pos, i), t, z),
                    Not(Call("rectangle", j, Call("x", pos, j), Call("y", pos, j), t, z))))))));
        Formula support = All("n", Naturals, Implies(Less(D(0), n),
            Call("closedSupport", pos, Seq(n, Sp, Minus, Sp, D(1)), n,
                Call("x", pos, n), Call("y", pos, n))));
        return Disp(Exists("pos", Call("NatToNatPair"),
            And(union, And(optimal, And(support, disjoint)))));
    }

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Lists => Call("List", Naturals);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
}
