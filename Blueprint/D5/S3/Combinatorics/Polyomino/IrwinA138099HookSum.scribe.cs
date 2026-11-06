using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Polyomino;

internal sealed class IrwinA138099HookSumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Polyomino/IrwinA138099HookSum.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/irwin2016a138099");
    private const string NameQuote = "Irregular triangle read by rows: T(n,k) = k + floor(n/2), 1 <= k <= ceiling(n/2).";
    private const string ConjectureQuote = "Conjecture: a(n) = HookSum(T(n))-HookSum(T(n-1)), where HookSum(A) is the sum of all hooks across a tableau A, and T(n) are the spiraling sequence of tableaux:";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The row-flattened triangle equals each hook-sum increment of the square spiral.",
        H("Irwin's hook-sum conjecture for OEIS A138099"),
        Blocks(
            Paragraph(Text("OEIS A138099, revision 26, NAME and Irwin FORMULA block (unpaginated). Coordinates are horizontal and vertical integers, with the vertical coordinate increasing downwards. The first cell is the origin; directions are west, south, east, north and leg lengths are 1, 1, 2, 2, 3, 3, and so on. The diagrams retain their actual occupied positions. All Nat.div and Nat.mod operations below are natural quotient and remainder; natural subtraction is truncated. Hook-sum subtraction is performed after casting both sums to the integers.")),
            Node("triangleEntry", "Triangle entries", TriangleEntry(), NameQuote + " Here k is the source's row n and j is its column k. The formula is used at 1 <= k and 1 <= j <= (k+1)/2.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("trianglePrefix", "Cumulative row lengths", TrianglePrefix(), NameQuote + " Row i+1 has (i+2)/2 entries, so trianglePrefix k counts the entries in rows 1 through k. The sum for k=0 is empty.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSourceSequence", "The sequence read by rows", SourceSequence(), NameQuote + " Indices start at one, as in the entry's offset 1,2. The value at index zero is unrestricted.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("legDirection", "The four leg directions", LegDirection(), "The four cases describe west, south, east and north respectively. They repeat with period four.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("WalkState", "Position and leg counters", WalkStateFormula(), "WalkState has exactly the three fields cell, leg and used, of the displayed types. The field used counts steps already taken on the current leg.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("advance", "One step and a possible turn", Advance(), "The direction d determines the next position p. A completed leg advances the leg counter and resets used; otherwise used increases by one. Every leg has positive length.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("walk", "The literal unit-step walk", Walk(), "Cell zero is (0,0). Applying advance repeatedly gives the cells of the displayed spiral in their insertion order.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("IsSourceSpiral", "Spiral diagrams", SourceSpiral(), ConjectureQuote + " The source's diagram, in its unpaginated FORMULA block, starts Empty, o, oo. Here T 0 is empty and T(n+1) inserts cell n of the walk. No reordering of rows or cells is performed.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("hookLength", "Ordinary hooks in occupied cells", HookLength(), ConjectureQuote + " The ordinary hook contains its own cell, the occupied cells strictly to its right in its row, and the occupied cells strictly below it in its column. The formula is used for c in D when summing hooks; holes are allowed.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("hookSum", "The sum of all hooks", HookSum(), ConjectureQuote + " This finite sum uses the occupied cells themselves, including the empty sum zero.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The source assertion with existence", IffTo(F.Id("claim"), ClaimBody()), ConjectureQuote + " This is the complete sentence in Irwin's unpaginated FORMULA block. The arithmetic and spiral sequences both exist, and the identity holds for every pair of such sequences and every positive index. The first two conjuncts assert existence rather than assume it.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The hook-sum identity at every positive index", ClaimBody(), "Inserting a fresh cell increases the total hook sum by one plus the old row and column sizes. After m squared cells the walk fills an m by m square. Its next m cells form one boundary strip and its next m+1 cells form the other. Their increments are m+j, exactly the entries of source rows 2m and 2m+1. The first singleton is handled separately. Row addresses also construct a source arithmetic sequence, and the insertion recursion constructs and uniquely determines the source spiral.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(ProblemSlugRef.Create("irwin-a138099"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("irwin-a138099-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(F.Id(name))), args);
    private static Formula App(Formula head, params Formula[] args) => new Formula.Apply(head, [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula DotCall(Formula value, string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Parenthesized(value), Dot, F.Id(name)) : App(Seq(Parenthesized(value), Dot, F.Id(name)), args);
    private static Formula Field(Formula value, string name) => Seq(value, Dot, F.Id(name));
    private static Formula Coordinate(Formula value, byte number) => Seq(value, Dot, D(number));
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Cells => Parenthesized(Seq(Ints, Sp, Times, Sp, Ints));
    private static Formula Diagrams => Call("Finset", Cells);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula State(Formula p, Formula l, Formula u) => Seq(Langle, Sp, p, Comma, Sp, l, Comma, Sp, u, Sp, Rangle);
    private static Formula Cast(Formula a) => Parenthesized(Seq(a, Sp, Colon, Sp, Ints));
    private static Formula All(string name, Formula type, Formula body) => Bind(Forall, name, type, body);
    private static Formula Some(string name, Formula type, Formula body) => Bind(Exists, name, type, body);
    private static Formula Bind(Formula token, string name, Formula type, Formula body) => Seq(token, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LtTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Div(Formula a, Formula b) => App(Qualified("Nat", "div"), a, b);
    private static Formula Mod(Formula a, Formula b) => App(Qualified("Nat", "mod"), a, b);
    private static Formula Ite(Formula p, Formula a, Formula b) => Call("ite", p, a, b);
    private static Formula FilterCard(Formula diagram, Formula predicate) => DotCall(DotCall(diagram, "filter", predicate), "card");

    private static Formula TriangleEntry()
    {
        Formula k = F.Id("k"), j = F.Id("j");
        return All("k", Nats, All("j", Nats, EqTo(Call("triangleEntry", k, j), Add(j, Div(k, D(2))))));
    }

    private static Formula TrianglePrefix()
    {
        Formula k = F.Id("k"), i = F.Id("i");
        return All("k", Nats, EqTo(Call("trianglePrefix", k),
            DotCall(App(Qualified("Finset", "range"), k), "sum", LambdaOf("i", Nats, Div(Add(i, D(2)), D(2))))));
    }

    private static Formula SourceSequence()
    {
        Formula a = F.Id("a"), k = F.Id("k"), j = F.Id("j");
        Formula value = EqTo(App(a, Add(Call("trianglePrefix", Sub(k, D(1))), j)), Call("triangleEntry", k, j));
        return All("a", Arrow(Nats, Nats), IffTo(Call("IsSourceSequence", a),
            All("k", Nats, Imp(LeTo(D(1), k), All("j", Nats, Imp(LeTo(D(1), j), Imp(LeTo(j, Div(Add(k, D(1)), D(2))), value)))))));
    }

    private static Formula LegDirection()
    {
        Formula leg = F.Id("leg");
        Formula cases = new Formula.Aligned([
            Seq(D(0), Sp, Mapsto, Sp, Pair(new Formula.Negate(D(1)), D(0))),
            Seq(D(1), Sp, Mapsto, Sp, Pair(D(0), D(1))),
            Seq(D(2), Sp, Mapsto, Sp, Pair(D(1), D(0))),
            Seq(Operatorname, Grp(F.Id("otherwise")), Sp, Mapsto, Sp, Pair(D(0), new Formula.Negate(D(1))))]);
        return All("leg", Nats, EqTo(Call("legDirection", leg),
            Seq(Operatorname, Grp(F.Id("match")), Sp, Mod(leg, D(4)), Sp, Operatorname, Grp(F.Id("with")), Sp, cases)));
    }

    private static Formula WalkStateFormula() => Seq(
        F.Id("WalkState"), Sp, Colon, Sp, F.Id("Type"), Semi, Sp,
        F.Id("cell"), Sp, Colon, Sp, Cells, Semi, Sp,
        F.Id("leg"), Sp, Colon, Sp, Nats, Semi, Sp,
        F.Id("used"), Sp, Colon, Sp, Nats);

    private static Formula Advance()
    {
        Formula s = F.Id("s"), d = F.Id("d"), p = F.Id("p");
        Formula used = Field(s, "used"), leg = Field(s, "leg"), cell = Field(s, "cell");
        Formula next = Pair(Add(Coordinate(cell, 1), Coordinate(d, 1)), Add(Coordinate(cell, 2), Coordinate(d, 2)));
        Formula step = Ite(EqTo(Add(used, D(1)), Add(Div(leg, D(2)), D(1))), State(p, Add(leg, D(1)), D(0)), State(p, leg, Add(used, D(1))));
        return All("s", F.Id("WalkState"), EqTo(Call("advance", s), Seq(
            Operatorname, Grp(F.Id("let")), Sp, d, Sp, Colon, Sp, Cells, Sp, Seq(Colon, Eq), Sp, Call("legDirection", leg), Semi, Sp,
            Operatorname, Grp(F.Id("let")), Sp, p, Sp, Colon, Sp, Cells, Sp, Seq(Colon, Eq), Sp, next, Semi, Sp, step)));
    }

    private static Formula Walk()
    {
        Formula n = F.Id("n");
        return And(EqTo(Call("walk", D(0)), State(Pair(D(0), D(0)), D(0), D(0))),
            All("n", Nats, EqTo(Call("walk", Add(n, D(1))), Call("advance", Call("walk", n)))));
    }

    private static Formula SourceSpiral()
    {
        Formula T = F.Id("T"), n = F.Id("n");
        return All("T", Arrow(Nats, Diagrams), IffTo(Call("IsSourceSpiral", T),
            And(EqTo(App(T, D(0)), Emptyset), All("n", Nats,
                EqTo(App(T, Add(n, D(1))), Call("insert", Field(Call("walk", n), "cell"), App(T, n)))))));
    }

    private static Formula HookLength()
    {
        Formula diagram = F.Id("D"), c = F.Id("c"), d = F.Id("d");
        Formula arm = LambdaOf("d", Cells, And(EqTo(Coordinate(d, 2), Coordinate(c, 2)), LtTo(Coordinate(c, 1), Coordinate(d, 1))));
        Formula leg = LambdaOf("d", Cells, And(EqTo(Coordinate(d, 1), Coordinate(c, 1)), LtTo(Coordinate(c, 2), Coordinate(d, 2))));
        return All("D", Diagrams, All("c", Cells, EqTo(Call("hookLength", diagram, c), Add(Add(D(1), FilterCard(diagram, arm)), FilterCard(diagram, leg)))));
    }

    private static Formula HookSum()
    {
        Formula diagram = F.Id("D"), c = F.Id("c");
        return All("D", Diagrams, EqTo(Call("hookSum", diagram), DotCall(diagram, "sum", LambdaOf("c", Cells, Call("hookLength", diagram, c)))));
    }

    private static Formula ClaimBody()
    {
        Formula a = F.Id("a"), T = F.Id("T"), n = F.Id("n");
        Formula arithmeticExists = Some("a", Arrow(Nats, Nats), Call("IsSourceSequence", a));
        Formula spiralExists = Some("T", Arrow(Nats, Diagrams), Call("IsSourceSpiral", T));
        Formula equality = EqTo(Cast(App(a, n)), Sub(Cast(Call("hookSum", App(T, n))), Cast(Call("hookSum", App(T, Sub(n, D(1)))))));
        Formula universal = All("a", Arrow(Nats, Nats), All("T", Arrow(Nats, Diagrams),
            Imp(Call("IsSourceSequence", a), Imp(Call("IsSourceSpiral", T), All("n", Nats, Imp(LeTo(D(1), n), equality))))));
        return And(arithmeticExists, And(spiralExists, universal));
    }
}
