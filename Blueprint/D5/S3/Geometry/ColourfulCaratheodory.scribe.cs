using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class ColourfulCaratheodoryDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/barany1982colourful");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One representative per label preserves a common convex hull point.",
        H("Colourful Carathéodory theorem"),
        Blocks(
            Paragraph(Text("For a natural number d, E(d) denotes the native real Euclidean "
                + "space EuclideanSpace Real (Fin d), and I(d) denotes Fin (d+1). "
                + "Set(E(d)) is the set of all subsets of E(d). The operator convexHull "
                + "below is convexHull Real, and range is the image of a function on "
                + "its entire domain.")),
            Describe.Lean(
                DescribeId.Create("colourful-caratheodory"),
                DeclarationHandle.Create("D5/S3/Geometry/ColourfulCaratheodory.colourful_caratheodory"),
                H("Labelled convex hull selection in every dimension"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every natural d, every point p of E(d), and every "
                        + "family S indexed by I(d) of arbitrary subsets of E(d), assume "
                        + "p belongs to the real convex hull of S(i) for every label i. "
                        + "There exists a function f on all labels such that f(i) belongs "
                        + "to S(i) for every i and p belongs to the real convex hull of "
                        + "range(f). The sets may be infinite and may overlap. The "
                        + "representatives may coincide, and convex coefficients may "
                        + "vanish. There is no compactness, closedness, boundedness, "
                        + "affine independence or general position hypothesis. Dimension "
                        + "zero is included.")),
                    Paragraph(Text("Translate p to zero and extract a finite nonempty "
                        + "subset from each original hull membership. The union of the "
                        + "convex hulls of all choices from these finite labelled subsets "
                        + "is a nonempty finite union of compact sets. Minimize the "
                        + "Euclidean norm on that union, obtaining q in one selected hull.")),
                    Paragraph(Text("If q is nonzero, the projection inequality gives "
                        + "inner(q,z) at least inner(q,q) for every point z of this hull. "
                        + "Take a positive affinely independent representation of q. "
                        + "The weighted inequalities sum to equality, so every support "
                        + "point lies at the supporting level inner(q,q). That level is "
                        + "positive; applying the inner product to a linear relation "
                        + "shows its coefficient sum is zero. Affine independence then "
                        + "makes the support linearly independent. It has at most d "
                        + "members and therefore omits a label among the d+1 colours.")),
                    Paragraph(Text("The omitted colour has zero in its convex hull, so "
                        + "some point x of that colour has inner(q,x) strictly less "
                        + "than inner(q,q). Change only that representative. All support "
                        + "points remain in the new selected hull, which still contains "
                        + "q and now contains x. The projection characterization implies "
                        + "that some point r in this same new hull has norm strictly "
                        + "less than the norm of q. This contradicts the chosen global "
                        + "minimum. Thus q is zero. Translate the selected representatives "
                        + "back to obtain the stated selection for p.")),
                    Paragraph(Text("Bárány's Theorem 2.1 on printed page 141 states the "
                        + "classical colourful selection theorem for arbitrary subsets "
                        + "of real Euclidean space. Ordinary Carathéodory, compactness "
                        + "of finite convex hulls, the finite-dimensional independence "
                        + "bound and the Hilbert projection characterization supply "
                        + "the standard ingredients."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var d = F.Id("d"); var p = F.Id("p"); var s = F.Id("S");
        var f = F.Id("f"); var i = F.Id("i");
        var e = Call("E", d); var labels = Call("I", d);
        var hypothesis = All("i", labels, Member(p, Call("convexHull", Apply(s, i))));
        var conclusion = Exists("f", new Formula.TypeArrow(labels, e),
            And(All("i", labels, Member(Apply(f, i), Apply(s, i))),
                Member(p, Call("convexHull", Call("range", f)))));
        return All("d", F.Id("Nat"), All("p", e,
            All("S", new Formula.TypeArrow(labels, Call("Set", e)),
                Implies(hypothesis, conclusion))));
    }

    private static Formula Apply(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Call(string n, params Formula[] a) => Apply(F.Id(n), a);
    private static Formula All(string n, Formula d, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula Exists(string n, Formula d, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), d, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
