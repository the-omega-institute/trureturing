using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class TreeBottomPinnacleNonuniqueDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/TreeBottomPinnacleNonunique.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A six-vertex tree has no minimum among its size-three pinnacle sets.",
        H("A Tree with Nonunique Bottom Pinnacle Sets"),
        Blocks(
            Paragraph(Text(
                "Section 6 of Bozeman, Cheng, Harris, Lasinis and Walker, "
                    + "The Pinnacle Sets of a Graph, arXiv:2406.19562v1, asks one to consider "
                    + "the bottom pinnacle set(s) of trees and determine whether there is "
                    + "a unique bottom element. This module exhibits a six-vertex tree "
                    + "whose size-three pinnacle sets have no minimum.")),
            Paragraph(Text(
                "Figure 10 of that same paper already exhibits a graph with the two bottom "
                    + "size-three pinnacle sets {2,5,6} and {3,4,6}, but that graph contains "
                    + "cycles. The poset is not claimed to be new; what is established here "
                    + "is its realization by a tree. The paper supplies the question and "
                    + "comparison; the declarations below are repository constructions.")),
            Paragraph(Text(
                "No classification for other cardinalities is formalized, and no claim "
                    + "is made about which trees on more vertices behave this way. "
                    + "Fin(6) contains the vertices 0, 1, 2, 3, 4, 5; pinnacle labels "
                    + "are one-based natural numbers.")),
            Definition("tree", "tree", "The six-vertex graph", TreeFormula(),
                "The displayed edge set consists of unordered pairs. There are no other "
                    + "edges. IsTree(tree) below is Lean's tree.IsTree."),
            Definition("pinnacleSet", "pinnacle-set", "Pinnacle labels", PinnacleFormula(),
                "For any function label, retain exactly the vertices whose every neighbor "
                    + "has strictly smaller label, then take the finite image under "
                    + "vertex maps to val(label(vertex)) + 1. This definition itself does "
                    + "not require bijectivity; repeated image values are counted only once."),
            Definition("Attainable", "attainable", "Attainability by a bijective labeling",
                AttainableFormula(),
                "Bijective is Function.Bijective. The existential quantifier ranges over "
                    + "every bijective labeling, not only the two witnesses exhibited below."),
            Definition("CoordinateLE", "coordinate-le", "Coordinatewise comparison",
                CoordinateFormula(),
                "sort uses the natural-number less-than-or-equal relation and lists the "
                    + "elements increasingly. ForallTwo denotes Lean's List.Forall₂: "
                    + "the lists have equal lengths and each corresponding pair satisfies "
                    + "the displayed relation."),
            Describe.Lean(DescribeId.Create("tree-is-tree"),
                DeclarationHandle.Create(Prefix + "tree_isTree"),
                H("The graph is a tree"),
                StatementSource.FromAuthor(Disp(Call("IsTree", F.Id("tree")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Lean proves connectivity by paths from vertex 1, and verifies "
                        + "the edge count required by the finite-tree characterization."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("attainable-three-cases"),
                DeclarationHandle.Create(Prefix + "attainable_three_cases"),
                H("Every attainable size-three set is one of four cases"),
                StatementSource.FromAuthor(ThreeCasesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both hypotheses are essential: pinnacles is attainable and its "
                        + "cardinality is three. Kernel reduction checks all 720 permutations; "
                        + "the proof shows that every bijective labeling appears in that "
                        + "enumeration. This theorem gives a necessary case list, not "
                        + "a classification for any other cardinality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("attainable-256"),
                DeclarationHandle.Create(Prefix + "attainable_256"),
                H("The set {2,5,6} is attainable"),
                StatementSource.FromAuthor(Disp(Call("Attainable", Pinnacles(2, 5, 6)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero-based label vector in vertex order is [2,3,0,4,5,1]. "
                        + "Lean checks its bijectivity and exact one-based pinnacle set."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("attainable-346"),
                DeclarationHandle.Create(Prefix + "attainable_346"),
                H("The set {3,4,6} is attainable"),
                StatementSource.FromAuthor(Disp(Call("Attainable", Pinnacles(3, 4, 6)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero-based label vector in vertex order is [0,1,4,2,3,5]. "
                        + "Lean checks its bijectivity and exact one-based pinnacle set."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tree-no-minimum"),
                DeclarationHandle.Create(Prefix + "tree_no_minimum"),
                H("A tree without a minimum size-three pinnacle set"),
                StatementSource.FromAuthor(NoMinimumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The conclusion includes tree.IsTree and denies a least set that "
                        + "has cardinality three, is attainable, and lies coordinatewise "
                        + "below every other attainable cardinality-three set. Such a least "
                        + "set would lie below both exhibited witnesses, but each of the "
                        + "four exhaustive cases contradicts one of these comparisons. "
                        + "The restriction on other is part of the theorem, not an "
                        + "implicit convention."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string declaration, string id, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

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

    private static Formula Vertex() => Call("Fin", D(6));
    private static Formula Finsets() => Call("Finset", F.Id("Nat"));
    private static Formula LabelType() => Seq(Vertex(), Sp, To, Sp, Vertex());
    private static Formula Pinnacles(byte first, byte second, byte third) =>
        Seq(OpenBrace, D(first), Comma, D(second), Comma, D(third), CloseBrace);
    private static Formula Edge(byte left, byte right) =>
        Seq(OpenBrace, D(left), Comma, D(right), CloseBrace);

    private static Formula TreeFormula() => Disp(new Formula.Aligned([
        Seq(F.Id("tree"), Colon, Sp, Call("SimpleGraph", Vertex()), Comma),
        Seq(Call("E", F.Id("tree")), Sp, Eq, Sp, OpenBrace,
            Edge(0, 1), Comma, Edge(1, 2), Comma, Edge(1, 3), Comma,
            Edge(1, 4), Comma, Edge(2, 5), CloseBrace),
    ]));

    private static Formula PinnacleFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, F.Id("label"), Colon, Sp, LabelType(), Comma),
        Seq(Call("pinnacleSet", F.Id("label")), Sp, Eq, Sp, OpenBrace,
            Call("val", Call("label", F.Id("vertex"))), Plus, D(1), Sp, Mid, Sp,
            F.Id("vertex"), Colon, Sp, Vertex(), Comma),
        Seq(Forall, Sp, F.Id("neighbor"), Colon, Sp, Vertex(), Comma, Sp,
            Call("Adj", F.Id("tree"), F.Id("vertex"), F.Id("neighbor")), Sp, Rightarrow, Sp,
            Call("label", F.Id("neighbor")), Sp, Lt, Sp,
            Call("label", F.Id("vertex")), CloseBrace),
    ]));

    private static Formula AttainableFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, F.Id("pinnacles"), Colon, Sp, Finsets(), Comma),
        Seq(Call("Attainable", F.Id("pinnacles")), Sp, Iff, Sp,
            Open, Exists, Sp, F.Id("label"), Colon, Sp, LabelType(), Comma, Sp,
            Call("Bijective", F.Id("label")), Sp, Land, Sp,
            Call("pinnacleSet", F.Id("label")), Sp, Eq, Sp, F.Id("pinnacles"), Close),
    ]));

    private static Formula CoordinateFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, F.Id("left"), Comma, Sp, F.Id("right"), Colon, Sp, Finsets(), Comma),
        Seq(Call("CoordinateLE", F.Id("left"), F.Id("right")), Sp, Iff, Sp,
            Call("ForallTwo", Leq, Call("sort", Leq, F.Id("left")),
                Call("sort", Leq, F.Id("right")))),
    ]));

    private static Formula ThreeCasesFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, F.Id("pinnacles"), Colon, Sp, Finsets(), Comma, Sp,
            Call("Attainable", F.Id("pinnacles")), Sp, Rightarrow, Sp,
            Call("card", F.Id("pinnacles")), Sp, Eq, Sp, D(3), Sp, Rightarrow),
        Seq(Open, F.Id("pinnacles"), Sp, Eq, Sp, Pinnacles(2, 5, 6), Sp, Lor, Sp,
            F.Id("pinnacles"), Sp, Eq, Sp, Pinnacles(3, 4, 6), Sp, Lor),
        Seq(F.Id("pinnacles"), Sp, Eq, Sp, Pinnacles(3, 5, 6), Sp, Lor, Sp,
            F.Id("pinnacles"), Sp, Eq, Sp, Pinnacles(4, 5, 6), Close),
    ]));

    private static Formula NoMinimumFormula() => Disp(new Formula.Aligned([
        Seq(Call("IsTree", F.Id("tree")), Sp, Land, Sp, Neg, Sp,
            Open, Exists, Sp, F.Id("least"), Colon, Sp, Finsets(), Comma),
        Seq(Call("card", F.Id("least")), Sp, Eq, Sp, D(3), Sp, Land, Sp,
            Call("Attainable", F.Id("least")), Sp, Land),
        Seq(Forall, Sp, F.Id("other"), Colon, Sp, Finsets(), Comma, Sp,
            Call("card", F.Id("other")), Sp, Eq, Sp, D(3), Sp, Rightarrow, Sp,
            Call("Attainable", F.Id("other")), Sp, Rightarrow, Sp,
            Call("CoordinateLE", F.Id("least"), F.Id("other")), Close),
    ]));
}
