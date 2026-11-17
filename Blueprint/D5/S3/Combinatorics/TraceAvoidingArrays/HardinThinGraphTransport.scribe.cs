using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinThinGraphTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233170");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal six-colour counts of distinct thin square and diagonal strips.",
        H("Actual graph reconstruction and continuation induction"),
        Blocks(
            Paragraph(Text("The height is n+1 and the width is k+1. True selects horizontal edges and both diagonals between consecutive rows; false selects horizontal and vertical edges. There are no wraparound edges. The graphs are defined independently. Colours are the three actual elements of Fin 3.")),
            Def("row", "Row", "A pair-label row", "Row k is Fin (k+1) to Fin 3."),
            Def("proper", "proper", "Horizontal properness", "For every j in Fin k, the colours at j.castSucc and j.succ differ."),
            Def("compatible", "compatible", "The actual inter-row bonds", "In the diagonal case, p j.castSucc differs from q j.succ and p j.succ differs from q j.castSucc for every j in Fin k. In the square case, p j differs from q j at every column."),
            Def("decidable-proper", "instDecidableProper", "Finite row decision", "The decision procedure is the finite universal inequality test defining proper."),
            Def("decidable-compatible", "instDecidableCompatible", "Finite bond decision", "The decision procedure unfolds compatible and decides its finite conjunctions and universal inequalities."),
            Def("boundary-class", "boundaryClass", "Endpoint equality of a three-cell row", "For p : Row 2, boundaryClass p is true exactly when p 0 equals p 2. Among proper rows, true is the aba class and false is the abc class."),
            Def("transition-table", "K", "The common two-class transfer", "K : Bool to Bool to Nat counts target classes in the order true, false. Its entries are 3 at (true,true) and 2 at each other pair. The transition_counts theorem identifies this table with actual proper-row successor counts for either bond choice."),
            Describe.Lean(DescribeId.Create("transition-counts"), DeclarationHandle.Create(Prefix + "transition_counts"),
                H("Exact successor counts at widths two and three"), StatementSource.FromAuthor(Disp(TransitionFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For each d : Bool and each proper p : Row 1, exactly three proper rows q satisfy compatible d p q. For each d : Bool, proper p : Row 2 and b : Bool, the number of proper compatible q with boundaryClass q=b is K (boundaryClass p) b. Both clauses quantify over every actual row over Fin 3; d=true selects both diagonals and d=false selects vertical bonds. Finite enumeration proves the two clauses, which determine the continuation recursions."))), DescribeRole.Theorem),
            Def("graph", "stripGraph", "Separate square and diagonal graphs", "Vertices are Fin (n+1) times Fin (k+1). Adjacency is an oriented horizontal bond, or an oriented vertical or diagonal bond as selected by d, or the reversal of such a bond. Distinct coordinate values prove looplessness."),
            Def("colouring-equiv", "colouringEquiv", "Actual colourings as complete row sequences", "The forward map reads the actual colour of every cell. The inverse reconstructs the graph colouring from horizontal properness and every adjacent-row compatibility condition. Both inverse identities hold at all heights and widths."),
            Def("row-major", "rowMajor", "The actual row-major index", "The index of cell (i,j) is j+(k+1)i. The codomain has n(k+1)+k+1 vertices, exactly (n+1)(k+1). The index order is precisely the lexicographic row-then-column order."),
            Def("ordered-graph", "orderedGraph", "The graph on literal scanner indices", "This is stripGraph transported along rowMajor, with no change to its actual cells or bonds."),
            Def("literal-strip", "literalStrip", "The complete six-colour strip", "Each actual rectangular assignment satisfies the existing widthLegal scanner, first-cell zero, horizontal exclusions and the selected vertical or diagonal exclusions. The colour_bond_iff theorem translates each exclusion to unequal beta labels. All positive heights and widths remain in scope."),
            Def("literal-equiv", "literalEquiv", "Reversible graph and literal-strip normalization", "Flattening the actual array along rowMajor gives exactly GraphNormalization.Legal on orderedGraph. Earlier flat indices are exactly earlier rows or earlier columns in the same row. This proves every scanner predecessor condition in both directions. The inverse unflattens the actual six-colour word, and both compositions recover every cell."),
            Describe.Lean(DescribeId.Create("path-result"), DeclarationHandle.Create(Prefix + "path_result"),
                H("The actual one-row path count"), StatementSource.FromAuthor(Disp(PathFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Automata/britnellwildon2017bellnumbers")),
                Blocks(Paragraph(Text("For every k≥0 the one-row path has k+2 vertices and its literal normalized six-colour count L satisfies 2L=4^k+2^k. The proper Fin 3 path count is 3 times 2^(k+1): after the first of three colours, each next vertex has exactly two choices. Decomposing actual row words into their first colour and remaining proper word proves that statement for arbitrary length. The connected graph formula and literalEquiv then give the displayed equality. In source indices this is T(1,w)=(4^(w-2)+2^(w-2))/2 for w≥2. The singleton convention T(1,1)=1 is separate. The one-row paired-colouring identity is attributed to Britnell and Wildon, Bell numbers, partition moves and the eigenvalues of the random-to-top shuffle in Dynkin Types A, B and D, arXiv:1507.04803v1, equation (9) and Proposition 8.1, as recorded in the cited Library note. The two-dimensional strip transport is outside that prior-result attribution; no sequence is defined by this shift."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-result"), DeclarationHandle.Create(Prefix + "normalized_result"),
                H("Literal diagonal counts equal the existing square counts"), StatementSource.FromAuthor(Disp(NormalizedFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every positive height, the normalized six-colour diagonal strips at widths two and three have exactly the counts of the existing A233123 and A233124 square-strip owners. Horizontal paths connect each row; an actual diagonal and a horizontal path connect consecutive rows. Column parity gives the diagonal bipartition, while row-plus-column parity gives the square bipartition. A horizontal edge is present at these widths. The connected_count theorem gives P(1)=0 and P(2)=2, so equality of P(3) transfers through the exact graph identity. The literalEquiv maps recover the scanner assignments. Expanding the existing square owners verifies their literal widthLegal predicates. No generating-series proof is duplicated."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Equality at every positive height"), StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A graph colouring is equivalent to its row sequence: properness supplies horizontal bonds and compatible supplies every selected inter-row bond. Both inverse maps preserve the actual colour at every cell. Splitting a row sequence into its first row and tail identifies its cardinality with the finite continuation recursion. At width two every proper row has three next rows for either graph. At width three the aba and abc classes have common successor counts K=((3,2),(2,2)). These local certificates are checked for all actual Fin 3 row words. Induction on every continuation length proves the shared recursion and hence equality of the actual graph-colouring counts. This is an all-height theorem, not an inference from finite-height agreement. It asserts neither graph isomorphism nor equality for every palette. The normalized_result theorem consumes this equality through the reversible six-colour scanner bridge and the connected-bipartite reduction."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((part, k) => k == 0
        ? new[] { Seq(Operatorname, Grp(F.Id(part))) }
        : new[] { Dot, Seq(Operatorname, Grp(F.Id(part))) }).ToArray());
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Name(name) : new Formula.Apply(Name(name), [.. args]);
    private static Formula PathFormula()
    {
        var k = F.Id("k");
        var width = new Formula.Binary(k, FormulaBinaryOperator.Add, D(1));
        var lhs = new Formula.Binary(D(2), FormulaBinaryOperator.Multiply,
            Call("Nat.card", Call("literalStrip", Call("true"), D(0), width)));
        var rhs = new Formula.Binary(new Formula.Power(D(4), k), FormulaBinaryOperator.Add,
            new Formula.Power(D(2), k));
        return Seq(Forall, Sp, k, Colon, Sp, Call("Nat"), Comma, Sp, lhs, Sp, F.Eq, Sp, rhs);
    }
    private static Formula TransitionFormula()
    {
        var d = F.Id("d"); var p = F.Id("p"); var q = F.Id("q"); var b = F.Id("b");
        Formula All(Formula x, Formula t, Formula body) => Seq(Forall, Sp, x, Colon, Sp, t, Comma, Sp, Parenthesized(body));
        Formula Equal(Formula x, Formula y) => Seq(x, Sp, F.Eq, Sp, y);
        Formula And(Formula x, Formula y) => Seq(Parenthesized(x), Sp, Land, Sp, Parenthesized(y));
        Formula Guard(Formula x, Formula y) => Seq(Parenthesized(x), Sp, Implies, Sp, Parenthesized(y));
        Formula Count(byte k, Formula condition) => Seq(Sum, Underscore, Grp(q, Colon, Sp, Call("Row", D(k))), Sp,
            Call("if", condition, D(1), D(0)));
        Formula Bonds() => And(Call("proper", q), Call("compatible", d, p, q));
        var two = All(d, Call("Bool"), All(p, Call("Row", D(1)),
            Guard(Call("proper", p), Equal(Count(1, Bonds()), D(3)))));
        var three = All(d, Call("Bool"), All(p, Call("Row", D(2)), Guard(Call("proper", p),
            All(b, Call("Bool"), Equal(Count(2, And(Bonds(), Equal(Call("boundaryClass", q), b))),
                Call("K", Call("boundaryClass", p), b))))));
        return And(two, three);
    }
    private static Formula NormalizedFormula()
    {
        var n = F.Id("n");
        Formula Count(byte k) => Call("Nat.card", Call("literalStrip", Call("true"), n, D(k)));
        var h = new Formula.Binary(n, FormulaBinaryOperator.Add, D(1));
        return Seq(Forall, Sp, n, Colon, Sp, Call("Nat"), Comma, Sp,
            Count(1), Sp, F.Eq, Sp, Call("HardinA233123SquareStrip.a", h), Sp, Land, Sp,
            Count(2), Sp, F.Eq, Sp, Call("HardinA233124SquareStrip.a", h));
    }
    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        Formula Count(bool d, int k) => Call("Nat.card", Call("Coloring",
            Call("stripGraph", Call(d ? "true" : "false"), n, D((byte)k)), Call("Fin", D(3))));
        return Seq(Forall, Sp, n, Colon, Sp, Call("Nat"), Comma, Sp,
            Count(true, 1), Sp, F.Eq, Sp, Count(false, 1), Sp, Land, Sp,
            Count(true, 2), Sp, F.Eq, Sp, Count(false, 2));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

}
