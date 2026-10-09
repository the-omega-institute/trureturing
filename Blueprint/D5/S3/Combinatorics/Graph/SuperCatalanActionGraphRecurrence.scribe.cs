using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class SuperCatalanActionGraphRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/caldwell2024actiongraphs");

    private const string GraphQuote = "Definition 5.2. We construct the sequence generalized action graphs, denoted {Gn}, for the super Catalan numbers as sequence of directed graphs defined inductively in the following way. The graph G0 is a single vertex labeled 0. To construct Gn+1 from Gn, consider each vertex v in Gn. For each 0 ≤ ℓ ≤ n, add p(v, ℓ) · 2/2^ℓ new vertices labeled n + 1 with edges from v, where p(v, ℓ) is the number of paths of length ℓ from v to vertices labeled n in Gn.";
    private const string TableQuote = "Definition 5.4. Let Kℓ,v,n be the number of paths of length ℓ in Gn that start at a vertex labeled v and end at a vertex labeled n. For a given n, the table of Kℓ,v,n for all values of ℓ and v is called the n-table.";
    private const string SuperQuote = "Definition 5.1 ([1], A17). The super Catalan numbers are defined by S(m, n) = (2m)!(2n)! / (m!n!(m + n)!).";
    private const string ClaimQuote = "Conjecture 5.6. The subsequent super Catalan number can be computed from the n-table of its previous action graph via S(0, n + 1) = Σ_{ℓ=0}^{n} (2/2^ℓ) Σ_{v=0}^{n} Kℓ,v,n.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every nonnegative n, the weighted sum of the path-table columns of the recursively constructed action graph equals S(0, n + 1).",
        H("Super Catalan numbers from action-graph path tables"),
        Blocks(
            Node("tree", "Labeled rooted trees", TreeFormula(), "Tree",
                "ArXiv v1, page 15: “" + GraphQuote + "” Each new vertex has exactly one parent. Tree.node records its label and its list of children; repeated list entries represent distinct vertices, with all edges directed from parent to child.", DescribeRole.Definition),
            Node("paths", "Paths from a root", PathsFormula(), "paths",
                "ArXiv v1, page 15: “" + GraphQuote + "” paths(t, r, k) is the source's p(v, ℓ), with r = ℓ and t the subtree rooted at v. The zero-length path starts and ends at the root. Paths of positive length first choose one child and then follow a shorter path.", DescribeRole.Definition),
            Node("grow", "Adding the next generation", GrowFormula(), "grow",
                "ArXiv v1, page 15: “" + GraphQuote + "” All path counts are taken in the old tree. Nat.div denotes natural-number quotient, including its total convention at zero; the denominators here are powers of two and are nonzero. The divisibility invariant proves that these quotients are exact for every subtree of G(n). The append operator ++ and List.replicate retain vertex multiplicities.", DescribeRole.Definition),
            Node("graphs", "The graph sequence", GraphFormula(), "G",
                "ArXiv v1, page 15: “" + GraphQuote + "” The initial tree is one vertex labeled zero, and the next graph is obtained by applying grow to the whole old graph.", DescribeRole.Definition),
            Node("pathsfrom", "Paths from every vertex of a label", PathsFromFormula(), "pathsFrom",
                "ArXiv v1, page 16: “" + TableQuote + "” pathsFrom(t, r, v, k) sums over every starting vertex labeled v in t. Its root contribution is included exactly when the root label equals v; recursive child contributions include every other vertex once.", DescribeRole.Definition),
            Node("table", "The n-table", TableFormula(), "K",
                "ArXiv v1, page 16: “" + TableQuote + "” r is the path length ℓ. The source's example K₁,₂,₃ counts all starting vertices labeled 2 and gives 2×2 + 2×2×2 = 12. K is a natural number; its occurrence in the conjectured weighted sum is explicitly cast to ℚ.", DescribeRole.Definition),
            Node("super", "Super Catalan numbers", SuperFormula(), "S",
                "ArXiv v1, page 15: “" + SuperQuote + "” Both arguments are natural numbers. Each factorial is cast to ℚ before rational multiplication and division.", DescribeRole.Definition),
            Node("claim", "Caldwell and coauthors' conjecture", ClaimFormula(), "claim",
                "ArXiv v1, page 17: “" + ClaimQuote + "” The quantifier includes n = 0. Both finite sums range from zero through n, and the weights and path counts are interpreted in ℚ.", DescribeRole.Definition),
            Node("result", "Proof of the weighted column identity", Disp(F.Id("claim")), "result",
                "At every subtree, 2^r divides the number of length-r paths to the current generation. This makes every growth count an exact quotient. Removing the last edge gives the weighted path recurrence. Summing over starting vertices and inducting on n yields the column formula 2^r times Nat.choose(2n − r, n) for 0 ≤ r ≤ n. The hockey-stick identity then gives twice Nat.choose(2n + 1, n + 1), equal to S(0, n + 1). The per-label path recurrence of Conjecture 5.5 has a posted proof at MathDB p/369567; the same last-edge mechanism supplies the recurrence used here.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("caldwell-2024-super-catalan-action-graph-ntable"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string declaration,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("caldwell-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula),
            role == DescribeRole.Theorem ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula TreeType() => Named("Tree");
    private static Formula ListTree() => Call("List", TreeType());
    private static Formula Nil() => Seq(OpenBracket, CloseBracket);
    private static Formula NodeTree(Formula a, Formula cs) => QCall("Tree", "node", a, cs);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Times(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula All(string v, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), type, body);
    private static Formula NaturalBinders(string[] names, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; i--) body = All(names[i], Naturals(), body);
        return body;
    }
    private static Formula RationalCast(Formula value) => Parenthesized(Seq(value, Colon, Rationals()));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, condition, Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);
    private static Formula LambdaTree(string v, Formula body) =>
        Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id(v), Colon, TreeType())), Sp, Mapsto, Sp, body);
    private static Formula ListSum(Formula function, Formula cs) =>
        QCall("List", "sum", QCall("List", "map", function, cs));
    private static Formula RangeSum(string v, Formula n, Formula body) =>
        Seq(new Formula.Subscript(Sum,
            Seq(F.Id(v), Sp, InMacro, Sp, QCall("Finset", "range", Add(n, D(1))))),
            Sp, Parenthesized(body));

    private static Formula TreeFormula() => Disp(new Formula.Aligned([
        Seq(TreeType(), Colon, Named("Type")),
        Seq(Qualified("Tree", "node"), Colon,
            new Formula.TypeArrow(Naturals(), new Formula.TypeArrow(ListTree(), TreeType())))]));

    private static Formula PathsFormula()
    {
        Formula a = F.Id("a"), cs = F.Id("cs"), r = F.Id("r"), k = F.Id("k");
        return Disp(new Formula.Aligned([
            NaturalBinders(["a", "k"], All("cs", ListTree(),
                Equal(Call("paths", NodeTree(a, cs), D(0), k), IfThenElse(Equal(a, k), D(1), D(0))))),
            NaturalBinders(["a", "r", "k"], All("cs", ListTree(),
                Equal(Call("paths", NodeTree(a, cs), Add(r, D(1)), k),
                    ListSum(LambdaTree("c", Call("paths", F.Id("c"), r, k)), cs))))]));
    }

    private static Formula GrowFormula()
    {
        Formula n = F.Id("n"), a = F.Id("a"), cs = F.Id("cs"), r = F.Id("r");
        var additions = RangeSum("r", n, QCall("Nat", "div",
            Times(Call("paths", NodeTree(a, cs), r, n), D(2)), new Formula.Power(D(2), r)));
        var children = Seq(QCall("List", "map", Call("grow", n), cs), Sp, Plus, Plus, Sp,
            QCall("List", "replicate", additions, NodeTree(Add(n, D(1)), Nil())));
        return Disp(NaturalBinders(["n", "a"], All("cs", ListTree(),
            Equal(Call("grow", n, NodeTree(a, cs)), NodeTree(a, children)))));
    }

    private static Formula GraphFormula()
    {
        Formula n = F.Id("n");
        return Disp(new Formula.Aligned([
            Equal(Call("G", D(0)), NodeTree(D(0), Nil())),
            All("n", Naturals(), Equal(Call("G", Add(n, D(1))), Call("grow", n, Call("G", n))))]));
    }

    private static Formula PathsFromFormula()
    {
        Formula a = F.Id("a"), cs = F.Id("cs"), r = F.Id("r"), v = F.Id("v"), k = F.Id("k");
        var root = Parenthesized(IfThenElse(Equal(a, v), Call("paths", NodeTree(a, cs), r, k), D(0)));
        return Disp(NaturalBinders(["a", "r", "v", "k"], All("cs", ListTree(),
            Equal(Call("pathsFrom", NodeTree(a, cs), r, v, k),
                Add(root, ListSum(LambdaTree("c", Call("pathsFrom", F.Id("c"), r, v, k)), cs))))));
    }

    private static Formula TableFormula() => Disp(NaturalBinders(["r", "v", "n"],
        Equal(Call("K", F.Id("r"), F.Id("v"), F.Id("n")),
            Call("pathsFrom", Call("G", F.Id("n")), F.Id("r"), F.Id("v"), F.Id("n")))));

    private static Formula SuperFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n");
        Formula Factorial(Formula x) => RationalCast(QCall("Nat", "factorial", x));
        return Disp(NaturalBinders(["m", "n"], Equal(Call("S", m, n),
            new Formula.Fraction(Times(Factorial(Times(D(2), m)), Factorial(Times(D(2), n))),
                Times(Times(Factorial(m), Factorial(n)), Factorial(Add(m, n)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), r = F.Id("r"), v = F.Id("v");
        var weight = new Formula.Fraction(RationalCast(D(2)), new Formula.Power(RationalCast(D(2)), r));
        var weighted = RangeSum("r", n, Times(weight,
            RangeSum("v", n, RationalCast(Call("K", r, v, n)))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            Parenthesized(All("n", Naturals(), Equal(Call("S", D(0), Add(n, D(1))), weighted)))));
    }
}
