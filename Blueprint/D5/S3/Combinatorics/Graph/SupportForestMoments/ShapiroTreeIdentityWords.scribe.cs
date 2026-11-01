using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SupportForestMoments;

internal sealed class ShapiroTreeIdentityWordsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroTreeIdentityWords.";
    private const string Quotation = "For a tree T, a word of length 2|E(T)| in the edges of T using every edge has product 1 if and only if every edge occurs exactly twice and, for every vertex x of T, the subword formed by the edges incident to x is a non-crossing double occurrence word.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/shapiro2026treewords");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Leaf intervals characterize identity words on every finite tree.",
        H("Identity edge words on finite trees"),
        Blocks(
            Node("NoncrossingDoubleOccurrence", "Noncrossing double occurrence words",
                DoubleOccurrenceFormula(), AssessedProvenance.FromLiterature(Source),
                "Page 14, Conjecture 1(iii): \"" + Quotation + "\" "
                + "For this term, every occurring letter has two copies. The existing "
                + "Crossing predicate compares the position pairs (i,j) and (k,l); it "
                + "forbids both alternating orders. Nested pairs and the empty word are allowed.",
                DescribeRole.Definition),
            Node("claim", "Shapiro's local tree criterion",
                IffFormula(F.Id("claim"), ClaimBody()),
                AssessedProvenance.FromLiterature(Source),
                "Page 14, Conjecture 1(iii): \"" + Quotation + "\" "
                + "Fin n relabels the source's vertex set [n]. Sym2 represents unordered "
                + "endpoint pairs. SimpleGraph.IsTree supplies connectedness and acyclicity; "
                + "the two membership hypotheses say that the word contains only tree edges "
                + "and uses every tree edge. List.prod multiplies the endpoint transpositions "
                + "in list order, with (sigma * rho)(v) = sigma(rho(v)). List.filter retains "
                + "the original order and tests decidable endpoint membership. The length is "
                + "twice the edge count, including the empty word on the one-vertex tree.",
                DescribeRole.Definition),
            Node("result", "The local tree criterion holds", ClaimBody(),
                AssessedProvenance.FromRepo(Source),
                "Deleting a tree edge separates its endpoints, so an identity word cannot "
                + "use that edge once. The prescribed total length forces multiplicity two. "
                + "For a leaf edge, the permutation between its two copies fixes its other "
                + "endpoint. Cancellation replaces that interval by its singleton letters. "
                + "A product of distinct forest-edge transpositions fixes exactly the vertices "
                + "outside those edges, which excludes a crossing with the leaf edge. "
                + "Induction proves necessity. For sufficiency, crossing edges have disjoint "
                + "endpoints, their transpositions commute, and repeated pairs cancel.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("shap2610"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("shapiro-tree-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula DoubleOccurrenceFormula()
    {
        var n = F.Id("n");
        var w = F.Id("w");
        return All("n", Nat(), All("w", Words(n),
            IffFormula(Call("NoncrossingDoubleOccurrence", w), DoubleOccurrenceBody(n, w))));
    }

    private static Formula DoubleOccurrenceBody(Formula n, Formula w)
    {
        var a = F.Id("a");
        var i = F.Id("i");
        var j = F.Id("j");
        var k = F.Id("k");
        var l = F.Id("l");
        var positions = Call("Fin", App(Q("List", "length"), w));
        var doubles = All("a", Edge(n),
            Imp(Member(a, w), Equal(App(Q("List", "count"), a, w), D(2))));
        var crossing = App(Q("NoncrossingNonnestingGraphRecurrence", "Crossing"),
            Pair(i, j), Pair(k, l));
        var noCrossing = All("i", positions, All("j", positions,
            All("k", positions, All("l", positions,
                Imp(Equal(At(w, i), At(w, j)),
                    Imp(Equal(At(w, k), At(w, l)),
                        Imp(NotEqual(At(w, i), At(w, k)), new Formula.Not(crossing))))))));
        return And(doubles, noCrossing);
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var t = F.Id("T");
        var w = F.Id("w");
        var a = F.Id("a");
        var x = F.Id("x");
        var edges = App(Q("SimpleGraph", "edgeFinset"), t);
        var letters = All("a", Edge(n), Imp(Member(a, w), Member(a, edges)));
        var length = Equal(App(Q("List", "length"), w),
            Multiply(D(2), App(Q("Finset", "card"), edges)));
        var used = All("a", Edge(n), Imp(Member(a, edges), Member(a, w)));
        var doubles = All("a", Edge(n),
            Imp(Member(a, edges), Equal(App(Q("List", "count"), a, w), D(2))));
        var membership = LambdaOf("a", Edge(n), Call("decide", Member(x, a)));
        var localWord = App(Q("List", "filter"), membership, w);
        var local = All("x", Call("Fin", n),
            Call("NoncrossingDoubleOccurrence", localWord));
        var product = App(Q("List", "prod"),
            App(Q("List", "map"), Q("SupportAndEdgeWordReflection", "edgeSwap"), w));
        return All("n", Nat(), All("T", Call("SimpleGraph", Call("Fin", n)),
            All("w", Words(n), Imp(App(Q("SimpleGraph", "IsTree"), t),
                Imp(letters, Imp(length, Imp(used,
                    IffFormula(Equal(product, D(1)), And(doubles, local)))))))));
    }

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Edge(Formula n) => Call("Sym2", Call("Fin", n));
    private static Formula Words(Formula n) => Call("List", Edge(n));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)),
            Sp, Mapsto, Sp, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula IffFormula(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name))));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula At(Formula w, Formula i) => Seq(w, OpenBracket, i, CloseBracket);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
}
