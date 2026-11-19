using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Games;

internal sealed class OddCycleTERDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Games/OddCycleTER.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/beneshernstmeyersalmonsieben2026geodeticremoving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original graph game TERMINATE has initial Grundy value zero on every odd cycle of length at least five.",
        H("Odd-cycle TERMINATE has initial Grundy value zero"),
        Blocks(
            Definition("Vertex", "Vertices of the odd cycle", Vertices(),
                "The vertices are the residues modulo 2m+1. The underlying graph is Mathlib's simple cycle graph."),
            Definition("GeoConvex", "Geodetic convexity", Convexity(),
                "A set contains the support of every shortest walk whose endpoints belong to the set. "
                + "Every walk with length equal to graph distance is a path."),
            Definition("geoHull", "Geodetic hull of the survivors", Hull(),
                "Intersect all geodetically convex sets containing the survivors. "
                + "Shortest paths are measured in the original cycle."),
            Definition("moves", "All legal TERMINATE moves", Options(),
                "If the current survivor hull is the entire vertex set, deleting any one survivor is legal. "
                + "The resulting hull may be proper. A proper hull at the current position gives no options."),
            Definition("grundy", "Grundy recursion on survivors", Grundy(),
                "Take the least natural number missing from the option values. "
                + "Every option removes exactly one survivor, so survivor cardinality gives well-founded recursion."),
            Definition("terNim", "Grundy value in selected-vertex coordinates", SelectedGrundy(),
                "Evaluate the survivor recurrence on the complement of the selected set. "
                + "Deletion of an unselected vertex from the survivors adds that same vertex to the selected set."),
            Describe.Lean(DescribeId.Create("odd-cycle-ter-conjecture-5-5"),
                DeclarationHandle.Create(Prefix + "conjecture_5_5"),
                H("Benesh et al. Conjecture 5.5"),
                StatementSource.FromAuthor(F.Disp(Claim())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Section 5.1 defines cycle graphs for n ≥ 4, so the odd cases are exactly n = 2m+1 with m ≥ 2. "
                        + "Play starts with the empty selected set.")),
                    Paragraph(Text("The survivor hull is full exactly when every block of m consecutive vertices contains a survivor. "
                        + "At the start of a two-move round with 2k+1 survivors, maintain at least k survivors in every block. "
                        + "For k > 2, delete the kth clockwise survivor after the first deletion's vertex in the pre-move order. "
                        + "The two strict arcs have k−1 and k survivors, so any block containing both deleted vertices had more than k. "
                        + "The reply restores the invariant with k−1.")),
                    Paragraph(Text("At k = 2 the first deletion leaves four survivors and every block remains occupied. "
                        + "Two disjoint m-vertex blocks partition the complement of any one survivor. "
                        + "One block contains exactly one survivor, whose deletion ends the game. "
                        + "Thus each first option has a zero-valued reply by strong induction or termination. "
                        + "Mex then gives zero at every position satisfying the invariant, including the start."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("benesh-et-al-2026-odd-cycle-terminate-conjecture-5-5"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("odd-cycle-ter-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(F.Disp(formula)),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Nat() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Positions(Formula m) => Call("Finset", Call("Vertex", m));

    private static Formula Vertices()
    {
        var m = F.Id("m");
        return All("m", Nat(), Equal(Call("Vertex", m), Fin(Add(Multiply(Num(2), m), Num(1)))));
    }

    private static Formula Convexity()
    {
        var n = F.Id("n");
        var k = F.Id("K");
        var x = F.Id("x");
        var y = F.Id("y");
        var p = F.Id("p");
        var z = F.Id("z");
        var cycle = Call("cycleGraph", n);
        var shortest = Equal(Call("length", p), Call("dist", cycle, x, y));
        var contain = All("z", Fin(n), new Formula.Logic(
            Member(z, Call("support", p)), FormulaLogicOperator.Implies, Member(z, k)));
        return All("n", Nat(), All("K", Call("Set", Fin(n)), new Formula.Logic(
            Call("GeoConvex", n, k), FormulaLogicOperator.Iff,
            All("x", Fin(n), All("y", Fin(n), All("p", Call("Walk", cycle, x, y),
                new Formula.Logic(
                    new Formula.Logic(Member(x, k), FormulaLogicOperator.And,
                        new Formula.Logic(Member(y, k), FormulaLogicOperator.And, shortest)),
                    FormulaLogicOperator.Implies, contain)))))));
    }

    private static Formula Hull()
    {
        var n = F.Id("n");
        var r = F.Id("R");
        var k = F.Id("K");
        var z = F.Id("z");
        var convexSuperset = F.Seq(r, F.Sp, F.Subseteq, F.Sp, k, F.Sp, F.Land, F.Sp,
            Call("GeoConvex", n, k));
        return All("n", Nat(), All("R", Call("Finset", Fin(n)), All("z", Fin(n),
            new Formula.Logic(Member(z, Call("geoHull", n, r)), FormulaLogicOperator.Iff,
                All("K", Call("Set", Fin(n)),
                    new Formula.Logic(convexSuperset, FormulaLogicOperator.Implies, Member(z, k)))))));
    }

    private static Formula Options()
    {
        var m = F.Id("m");
        var r = F.Id("R");
        var q = F.Id("Q");
        var x = F.Id("x");
        var full = Equal(Call("geoHull", Add(Multiply(Num(2), m), Num(1)), r), F.Id("V"));
        var erase = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("x"),
            Call("Vertex", m), new Formula.Logic(Member(x, r), FormulaLogicOperator.And,
                Equal(Call("erase", r, x), q)));
        return All("m", Nat(), All("R", Positions(m), All("Q", Positions(m),
            new Formula.Logic(Member(q, Call("moves", m, r)), FormulaLogicOperator.Iff,
                new Formula.Logic(full, FormulaLogicOperator.And, erase)))));
    }

    private static Formula Grundy()
    {
        var m = F.Id("m");
        var r = F.Id("R");
        var value = F.Id("g");
        var q = F.Id("Q");
        var optionValue = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("Q"),
            Positions(m), new Formula.Logic(Member(q, Call("moves", m, r)), FormulaLogicOperator.And,
                Equal(Call("grundy", m, q), value)));
        return All("m", Nat(), All("R", Positions(m), Equal(Call("grundy", m, r),
            Call("mex", F.Seq(F.OpenBrace, value, F.Sp, F.Bar, F.Sp, optionValue, F.CloseBrace)))));
    }

    private static Formula SelectedGrundy()
    {
        var m = F.Id("m");
        var selected = F.Id("S");
        return All("m", Nat(), All("S", Positions(m),
            Equal(Call("terNim", m, selected), Call("grundy", m, Call("complement", selected)))));
    }

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula Claim() =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("m"),
            F.Seq(F.Mathbb, F.Grp(F.Id("N"))),
            new Formula.Logic(
                new Formula.Relation(Num(2), FormulaRelationOperator.LessThanOrEqual, F.Id("m")),
                FormulaLogicOperator.Implies,
                Equal(Call("terNim", F.Id("m"), F.Emptyset), Num(0))));
}
