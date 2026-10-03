using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Polyomino;

internal sealed class LPolyominoSkippedSequenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/condon2026polyominodensity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimum size of a polyomino containing N translated L n-ominoes is the Nth term of S(n, 1, 2).",
        H("L Polyominoes and Skipped Numbers"),
        Blocks(
            Node("Cell", "Integer cells", EqTo(Cell, Seq(Ints, Sp, Times, Sp, Ints)),
                "Section 2.1, p. 4: “We regard the cells of all polyominoes as orthogonal unit squares on the Cartesian plane, with their lower left corners having integer coordinates.” A cell is encoded by its lower left corner.", DescribeRole.Definition),
            Node("L", "The L n-omino", LFormula(),
                "Section 4.4, p. 15: “We define an L n-omino, for n ≥ 3, to be a left-aligned polyomino with two rows that has 1 cell in the top row and n − 1 cells in the bottom row.” The bottom row starts at (0,0); the top cell is (0,1). The image uses the natural-number range 0 ≤ i < n − 1 and casts i to an integer. Natural subtraction is truncated at zero.", DescribeRole.Definition),
            Node("instances", "Translation anchors", InstancesFormula(),
                "Section 2.1, p. 4: “In this paper, we deal with fixed polyominoes, meaning we consider two polyominoes to be the same shape if they differ by translation only; we call these two instances of that shape.” The displayed expression first lists differences u − c, then retains precisely the anchors v for which every c + v belongs to P. For a nonempty shape this captures every translation anchor. Rotations and reflections are not counted. The expression gives the empty set for an empty shape; every L n-omino in the theorem is nonempty.", DescribeRole.Definition),
            Node("Adj", "Edge adjacency", AdjFormula(),
                "Section 1, p. 3: “A polyomino is a connected shape made from unit squares, called cells, glued together edge-to-edge.” The two alternatives describe vertical and horizontal unit edges. All coordinate arithmetic is in the integers.", DescribeRole.Definition),
            Node("IsPolyomino", "Nonempty connected cell sets", PolyominoFormula(),
                "Section 1, p. 3: “A polyomino is a connected shape made from unit squares, called cells, glued together edge-to-edge.” ReflTransGen means a finite path, including the length-zero path. Every vertex of each edge is required to belong to P.", DescribeRole.Definition),
            Node("a", "The instance minimum", MinimumFormula(),
                "Section 1, p. 3: “For N any positive integer, if P is a polyomino of minimum size among those polyominoes containing at least N instances (translated copies) of some polyomino p, we say that P is (p, N)-dense” and “We let a_{p,N} denote the size of a (p, N)-dense polyomino, and we call (a_{p,N})_{N=1}^∞ the instance sequence for p.” The minimum is the natural-number infimum of the displayed set. The proof constructs an eligible polyomino for each n ≥ 3 and N ≥ 1, so the empty-set convention for sInf is never used in the conclusion.", DescribeRole.Definition),
            Node("skip", "The sequence's own recursion", SkipFormula(),
                "Section 6.3, p. 28: “In a recent preprint [Clo25], Benoit Cloitre defines an S(x, y, z) sequence to be an increasing sequence of integers a_k starting with a_1 = x, such that for k > 1, a_k − a_{k−1} = y if k occurs in the sequence before position k, and otherwise a_k − a_{k−1} = z.” Here y = 1 and z = 2. The function ite selects its second argument when its first argument holds and its third otherwise. Index zero is an auxiliary value equal to x; the source sequence starts at index one. Natural subtraction is truncated at zero.", DescribeRole.Definition),
            Node("claim", "The general suspicion", IffTo(F.Id("claim"), ClaimFormula()),
                "Section 6.3, p. 28: “We believe S(5, 1, 2) is the same as the instance sequence for [L pentomino], and we suspect that the instance sequence for the L n-omino is S(n, 1, 2) in general.” The bracketed label denotes the source's inline L pentomino diagram. The n ≥ 3 domain comes from Section 4.4 and the N ≥ 1 domain from Section 1. Both independent sides use exactly the definitions above.", DescribeRole.Definition),
            Node("result", "Identification for every n and N", ClaimFormula(),
                "Put d = n − 2 and weight a cell (x,y) by x + d y. The top and right-most cells of every instance share a level. Injecting anchors into earlier levels and excluding the maximum-x cell at the current level bounds the number I of instances by the sum of floor(i/d) for 0 ≤ i < |P| − I, for every finite cell set P. No connectivity assumption is needed for this lower bound. A trimmed down-set attains the bound and is edge-connected. If K is the least integer with N ≤ sum of floor(i/d) for 0 ≤ i ≤ K, the attained minimum is N + 1 + K. The prefix-sum identity H(K+d) = H(K) + K identifies the jump positions of this minimum with the values absent from its earlier range. Strong induction then identifies it with the independently defined skipped-number recursion. In particular, the believed L pentomino case n = 5 follows.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("condon-dugan-goldman-williams-2026-l-polyomino-skipped-sequence"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("l-polyomino-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(Disp(formula)),
            role == DescribeRole.Theorem ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Cell => F.Id("Cell");
    private static Formula Cells => Call("Finset", Cell);
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Comma, Sp, y));
    private static Formula Cast(Formula x) => Parenthesized(Seq(x, Sp, Colon, Sp, Ints));
    private static Formula Bind(Formula quantifier, string name, Formula type, Formula body) =>
        Seq(quantifier, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula All(string name, Formula type, Formula body) => Bind(Forall, name, type, body);
    private static Formula Some(string name, Formula type, Formula body) => Bind(Exists, name, type, body);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula EqTo(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula LeTo(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula LtTo(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Mem(Formula x, Formula s) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, s);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) =>
        new Formula.Logic(Parenthesized(x), op, Parenthesized(y));
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula Or(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Or, y);
    private static Formula Imp(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula IffTo(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Card(Formula x) => Call("card", x);

    private static Formula LFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i");
        Formula bottom = Call("image", LambdaOf("i", Nats, Pair(Cast(i), D(0))), Call("range", Sub(n, D(1))));
        return All("n", Nats, EqTo(Call("L", n), Seq(bottom, Sp, Cup, Sp, new Formula.SetLiteral([Pair(D(0), D(1))]))));
    }

    private static Formula InstancesFormula()
    {
        Formula p = F.Id("p"), P = F.Id("P"), u = F.Id("u"), c = F.Id("c"), v = F.Id("v");
        Formula candidates = Call("biUnion", P, LambdaOf("u", Cell, Call("image", LambdaOf("c", Cell, Sub(u, c)), p)));
        Formula predicate = LambdaOf("v", Cell, All("c", Cell, Imp(Mem(c, p), Mem(Add(c, v), P))));
        return All("P", Cells, All("p", Cells, EqTo(Call("instances", P, p), Call("filter", candidates, predicate))));
    }

    private static Formula AdjFormula()
    {
        Formula c = F.Id("c"), b = F.Id("b");
        Formula cx = Call("fst", c), cy = Call("snd", c), bx = Call("fst", b), by = Call("snd", b);
        return All("c", Cell, All("b", Cell, IffTo(Call("Adj", c, b),
            Or(And(EqTo(cx, bx), Or(EqTo(Add(cy, D(1)), by), EqTo(Add(by, D(1)), cy))),
               And(EqTo(cy, by), Or(EqTo(Add(cx, D(1)), bx), EqTo(Add(bx, D(1)), cx)))))));
    }

    private static Formula PolyominoFormula()
    {
        Formula P = F.Id("P"), c = F.Id("c"), b = F.Id("b"), u = F.Id("u"), v = F.Id("v");
        Formula edge = LambdaOf("u", Cell, LambdaOf("v", Cell, And(Mem(u, P), And(Mem(v, P), Call("Adj", u, v)))));
        Formula connected = All("c", Cell, Imp(Mem(c, P), All("b", Cell, Imp(Mem(b, P), Call("ReflTransGen", edge, c, b)))));
        return All("P", Cells, IffTo(Call("IsPolyomino", P), And(Call("Nonempty", P), connected)));
    }

    private static Formula MinimumFormula()
    {
        Formula p = F.Id("p"), N = F.Id("N"), S = F.Id("S"), P = F.Id("P");
        Formula eligible = Some("P", Cells, And(Call("IsPolyomino", P),
            And(LeTo(N, Card(Call("instances", P, p))), EqTo(Card(P), S))));
        Formula sizes = Seq(OpenBrace, S, Sp, Colon, Sp, Nats, Sp, Mid, Sp, eligible, CloseBrace);
        return All("p", Cells, All("N", Nats, EqTo(Call("a", p, N), Call("sInf", sizes))));
    }

    private static Formula SkipFormula()
    {
        Formula x = F.Id("x"), k = F.Id("k"), i = F.Id("i");
        Formula earlier = Some("i", Nats, And(LeTo(D(1), i), And(LtTo(i, k), EqTo(Call("skip", x, i), k))));
        Formula step = Add(Call("skip", x, Sub(k, D(1))), Call("ite", earlier, D(1), D(2)));
        return All("x", Nats, All("k", Nats, EqTo(Call("skip", x, k), Call("ite", LeTo(k, D(1)), x, step))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), N = F.Id("N");
        return All("n", Nats, All("N", Nats, Imp(LeTo(D(3), n), Imp(LeTo(D(1), N),
            EqTo(Call("a", Call("L", n), N), Call("skip", n, N))))));
    }
}
