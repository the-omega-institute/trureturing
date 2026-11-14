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
            Def("graph", "stripGraph", "Separate square and diagonal graphs", "Vertices are Fin (n+1) times Fin (k+1). Adjacency is an oriented horizontal bond, or an oriented vertical or diagonal bond as selected by d, or the reversal of such a bond. Distinct coordinate values prove looplessness."),
            Def("colouring-equiv", "colouringEquiv", "Actual colourings as complete row sequences", "The forward map reads the actual colour of every cell. The inverse reconstructs the graph colouring from horizontal properness and every adjacent-row compatibility condition. Both inverse identities hold at all heights and widths."),
            Def("row-major", "rowMajor", "The actual row-major index", "The index of cell (i,j) is j+(k+1)i. The codomain has n(k+1)+k+1 vertices, exactly (n+1)(k+1). The index order is precisely the lexicographic row-then-column order."),
            Def("ordered-graph", "orderedGraph", "The graph on literal scanner indices", "This is stripGraph transported along rowMajor, with no change to its actual cells or bonds."),
            Def("literal-strip", "literalStrip", "The complete six-colour strip", "Each actual rectangular assignment satisfies the existing widthLegal scanner, first-cell zero, horizontal exclusions and the selected vertical or diagonal exclusions. The colour_bond_iff theorem translates each exclusion to unequal beta labels. All positive heights and widths remain in scope."),
            Def("literal-equiv", "literalEquiv", "Reversible graph and literal-strip normalization", "Flattening the actual array along rowMajor gives exactly GraphNormalization.Legal on orderedGraph. Earlier flat indices are exactly earlier rows or earlier columns in the same row. This proves every scanner predecessor condition in both directions. The inverse unflattens the actual six-colour word, and both compositions recover every cell."),
            Describe.Lean(DescribeId.Create("path-result"), DeclarationHandle.Create(Prefix + "path_result"),
                H("The actual one-row path count"), StatementSource.FromAuthor(Disp(PathFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every k≥0 the one-row path has k+2 vertices and its literal normalized six-colour count L satisfies 2L=4^k+2^k. The proper Fin 3 path count is 3 times 2^(k+1): after the first of three colours, each next vertex has exactly two choices. Decomposing actual row words into their first colour and remaining proper word proves that statement for arbitrary length. The connected graph formula and literalEquiv then give the displayed equality. In source indices this is T(1,w)=(4^(w-2)+2^(w-2))/2 for w≥2. The singleton convention T(1,1)=1 is separate. The source credits the A007582(w-2) identification to Britnell and Wildon, equation (9) and Proposition 8.1; no sequence is defined by this shift."))), DescribeRole.Theorem),
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
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(name.Split('.').SelectMany((part, k) => k == 0
            ? new[] { Seq(Operatorname, Grp(F.Id(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(F.Id(part))) }).ToArray()), [.. args]);
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
}
