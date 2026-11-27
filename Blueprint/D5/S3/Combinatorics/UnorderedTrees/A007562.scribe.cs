using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class A007562Document : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/UnorderedTrees/A007562.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/wiseman2025a007562");

    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula V = F.Id("V");
    private static readonly Formula T = F.Id("T");
    private static readonly Formula U = F.Id("u");
    private static readonly Formula W = F.Id("w");
    private static readonly Formula Child = F.Id("v");
    private static readonly Formula N = F.Id("n");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reparenting the same vertices gives a bijection between the normalized even-depth planted classes "
        + "and the classes in which each internal vertex has an immediate leaf child.",
        H("Wiseman’s two rooted-tree counts"),
        Blocks(
            Paragraph(Text(
                "A rooted parent tree has a fixed root, and every vertex reaches it by iterating the parent map. "
                + "Its nonroot parent edges connect the graph to the root and change depth by one. "
                + "A deepest vertex on a cycle would have two shallower neighbors, but each nonroot vertex has just one parent. Conversely, "
                + "in a rooted tree graph the unique simple path to the root determines each nonroot parent. "
                + "A rooted graph isomorphism preserves those paths, and a root-preserving parent-map "
                + "isomorphism preserves the graph edges.")),
            Definition("parity", "ParityTree", "The parity condition", ForTree(
                IffOf(Call("ParityTree", T),
                    All(U, V, ImpliesOf(EvenDepth(U), All(Child, V, All(W, V,
                        ImpliesOf(And(ChildOf(Child, U), ChildOf(W, U)), Equal(Child, W)))))))),
                "Every vertex at even edge depth, including the root, has at most one actual child."),
            Definition("planted", "Planted", "The literal planted condition", ForTree(
                IffOf(Call("Planted", T),
                    And(UniqueChild(Call("root", T)),
                        All(U, V, ImpliesOf(
                            And(Seq(U, Sp, Neq, Sp, Call("root", T)),
                                And(EvenDepth(U), Internal(U))), UniqueChild(U)))))),
                "The root has exactly one child. A nonroot internal vertex at even edge depth also has "
                + "exactly one child, so it has degree two in the underlying graph.", Source),
            Definition("leaf-child", "LeafChildTree", "The leaf-child condition", ForTree(
                IffOf(Call("LeafChildTree", T), All(U, V, ImpliesOf(Internal(U),
                    Seq(Exists, Sp, Typed(Child, V), Comma, Sp,
                        And(ChildOf(Child, U), Seq(Neg, Sp, Internal(Child)))))))),
                "The leaf required at each internal vertex is an immediate child of that vertex.", Source),
            Definition("parity-class", "ParityClass", "Normalized parity classes",
                ClassFormula("ParityClass", "ParityTree"),
                "The predicate descends to actual root-preserving isomorphism classes on Fin n. "
                + "The bar denotes the predicate on classes obtained by applying it to a representative."),
            Definition("planted-class", "PlantedClass", "Literal planted classes",
                ClassFormula("PlantedClass", "Planted"),
                "The planted predicate descends to the same unordered rooted-tree quotient. "
                + "On any tree with at least two vertices a path to the root supplies an actual root child, "
                + "so the planted and parity predicates agree at these sizes."),
            Definition("leaf-child-class", "LeafChildClass", "Leaf-child classes",
                ClassFormula("LeafChildClass", "LeafChildTree"),
                "The leaf-child predicate descends because rooted isomorphisms preserve and reflect child "
                + "edges. Any finite tree on n vertices can be relabeled on Fin n. Quotienting by actual "
                + "root-preserving isomorphism removes the labels, and the finite parent maps and roots "
                + "give a finite quotient."),
            Definition("class-equivalence", "classEquiv", "Reparenting gives an equivalence",
                All(N, Nat, Typed(Call("classEquiv", N),
                    Call("Equiv", Call("ParityClass", N), Call("LeafChildClass", N)))),
                "The forward transform keeps the parent of an odd-depth vertex and uses the grandparent "
                + "for a nonroot even-depth vertex. The new depth of a vertex of depth d is ⌊(d+1)/2⌋, "
                + "as this rank falls by one at each nonroot step. Every new parent has even original "
                + "depth. Any internal vertex in the image still has an original odd child, which "
                + "becomes a leaf. The inverse selects one immediate leaf at each internal vertex "
                + "and attaches the remaining children to that selected leaf. Its depth at a vertex "
                + "of image depth D is 2D minus one for a selected leaf and 2D otherwise. Its even-depth "
                + "vertices are unselected and have at most one child. Applying the forward map after "
                + "any inverse restores all parents. The inverse after the forward map restores all "
                + "original parents when the original odd children are selected. Any two choices are "
                + "related by an involution swapping the two selected leaves within each parent’s child "
                + "set, with the root and all internal vertices fixed. Together with transport of a "
                + "choice along a rooted isomorphism, this gives injectivity on the quotient. The "
                + "inverse with any allowed choice supplies surjectivity. Each operation uses the "
                + "same vertices, including all occurrences of isomorphic sibling subtrees."),
            Definition("planted-count", "plantedCount", "The literal planted count",
                CountFormula("plantedCount", "PlantedClass"),
                "The singleton has no child and contributes zero to this count."),
            Definition("normalized-count", "normalizedCount", "The normalized count",
                CountFormula("normalizedCount", "ParityClass"),
                "The singleton satisfies the parity condition and contributes one. At larger sizes the "
                + "normalized count is the literal planted count."),
            Definition("leaf-child-count", "leafChildCount", "The leaf-child count",
                CountFormula("leafChildCount", "LeafChildClass"),
                "The singleton has no internal vertices and belongs to this class."),
            Describe.Lean(
                DescribeId.Create("oeis-a007562-result"),
                DeclarationHandle.Create(Owner + "result"),
                H("The exact equality and the singleton boundary"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Wiseman asks, “Let a(n) be the number of planted trees where non-root, "
                        + "non-leaf nodes an even distance from root are of degree 2. Let b(n) be the number "
                        + "of unlabeled rooted trees with n nodes in which every non-leaf node has at least "
                        + "one leaf. Is a(n) = b(n) for all n?”")),
                    Paragraph(Text(
                    "The equivalence gives equality of the two cardinalities at each positive size after "
                    + "normalization. From size two on, every tree has a root child and the parity "
                    + "condition is the literal planted condition. There is one rooted isomorphism class "
                    + "on one vertex. Its literal planted count is zero and the other two counts are one."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a007562-parity-leaf-child"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string name, string title, Formula formula, string prose,
        params LibraryNoteRef[] acknowledgements) =>
        Describe.Lean(DescribeId.Create("oeis-a007562-" + id), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(acknowledgements),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ResultFormula()
    {
        var literalEquality = All(N, Nat, ImpliesOf(Seq(D(2), Sp, Le, Sp, N),
            Equal(Call("plantedCount", N), Call("leafChildCount", N))));
        var singleton = And(Equal(Call("plantedCount", D(1)), D(0)),
            And(Equal(Call("normalizedCount", D(1)), D(1)),
                Equal(Call("leafChildCount", D(1)), D(1))));
        var normalizedEquality = All(N, Nat, ImpliesOf(Seq(D(0), Lt, N),
            Equal(Call("normalizedCount", N), Call("leafChildCount", N))));
        return new Formula.Aligned([
            Seq(Amp, Parenthesized(literalEquality)),
            Seq(Amp, Land, Sp, Parenthesized(singleton)),
            Seq(Amp, Land, Sp, Parenthesized(normalizedEquality))
        ]);
    }

    private static Formula ClassFormula(string name, string predicate)
    {
        var x = F.Id("x");
        var lifted = new Formula.Apply(Seq(Overline, Grp(Operator(predicate))), [x]);
        return All(N, Nat, Equal(Call(name, N),
            Seq(OpenBrace, Typed(x, Call("TreeClass", N)), Sp, Mid, Sp, lifted, CloseBrace)));
    }

    private static Formula CountFormula(string name, string domain) =>
        All(N, Nat, Equal(Call(name, N),
            new Formula.Apply(Seq(Operatorname, Grp(Seq(F.Id("Nat"), Dot, F.Id("card")))),
                [Call(domain, N)])));

    private static Formula ForTree(Formula body) =>
        All(V, Seq(Mathrm, Grp(F.Id("Type"))), All(T, Call("Tree", V), body));

    private static Formula EvenDepth(Formula v) => Call("Even", Call("depth", T, v));
    private static Formula Internal(Formula v) => Call("Internal", T, v);
    private static Formula ChildOf(Formula v, Formula u) => Call("Child", T, v, u);
    private static Formula UniqueChild(Formula u) =>
        Seq(Exists, Bang, Sp, Typed(Child, V), Comma, Sp, ChildOf(Child, u));

    private static Formula Operator(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Operator(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula term, Formula type) => Seq(term, Colon, Sp, type);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Typed(variable, type)), Comma, Sp, body);
    private static Formula And(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula ImpliesOf(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Implies, Sp, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => Seq(left, Sp, Iff, Sp, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => Seq(left, Eq, right);
}
