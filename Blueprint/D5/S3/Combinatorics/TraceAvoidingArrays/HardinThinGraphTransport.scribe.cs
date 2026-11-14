using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinThinGraphTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233170");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three-colouring counts of distinct thin square and diagonal graphs.",
        H("Actual graph reconstruction and continuation induction"),
        Blocks(
            Paragraph(Text("The height is n+1 and the width is k+1. True selects horizontal edges and both diagonals between consecutive rows; false selects horizontal and vertical edges. There are no wraparound edges. The graphs are defined independently. Colours are the three actual elements of Fin 3.")),
            Def("row", "Row", "A pair-label row", "Row k is Fin (k+1) to Fin 3."),
            Def("proper", "proper", "Horizontal properness", "For every j in Fin k, the colours at j.castSucc and j.succ differ."),
            Def("compatible", "compatible", "The actual inter-row bonds", "In the diagonal case, p j.castSucc differs from q j.succ and p j.succ differs from q j.castSucc for every j in Fin k. In the square case, p j differs from q j at every column."),
            Def("decidable-proper", "instDecidableProper", "Finite row decision", "The decision procedure is the finite universal inequality test defining proper."),
            Def("decidable-compatible", "instDecidableCompatible", "Finite bond decision", "The decision procedure unfolds compatible and decides its finite conjunctions and universal inequalities."),
            Def("graph", "stripGraph", "Separate square and diagonal graphs", "Vertices are Fin (n+1) times Fin (k+1). Adjacency is an oriented horizontal bond, or an oriented vertical or diagonal bond as selected by d, or the reversal of such a bond. Distinct coordinate values prove looplessness."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Equality at every positive height"), StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A graph colouring is equivalent to its row sequence: properness supplies horizontal bonds and compatible supplies every selected inter-row bond. Both inverse maps preserve the actual colour at every cell. Splitting a row sequence into its first row and tail identifies its cardinality with the finite continuation recursion. At width two every proper row has three next rows for either graph. At width three the aba and abc classes have common successor counts K=((3,2),(2,2)). These local certificates are checked for all actual Fin 3 row words. Induction on every continuation length proves the shared recursion and hence equality of the actual graph-colouring counts. This is an all-height theorem, not an inference from finite-height agreement. It asserts neither graph isomorphism nor equality for every palette. The row-major six-colour scanner bridge and connected-bipartite reduction remain separate obligations."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(name.Split('.').SelectMany((part, k) => k == 0
            ? new[] { Seq(Operatorname, Grp(F.Id(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(F.Id(part))) }).ToArray()), [.. args]);
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
