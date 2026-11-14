using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class LyudogovskiyTransfersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/lyudogovskiy2026simplex");

    public DocumentDefinition Create()
    {
        var n = V("n");
        var p = V("p");
        var q = V("q");
        var bridge = OnPartitions(Imp(Lt(D(0), n), Iff(C("UnitTransfer", p, q),
            Eq(C("card", C("inf", C("ofPartition", p), C("ofPartition", q))), Sub(n, D(1))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Native partition transfers are one-cell exchanges of finite Young ideals in the integer lattice.",
            H("Partition transfers and finite lattice ideals"), Blocks(
                Paragraph(Text("The vertices are native Nat.Partition values, with multiplicities retained. Their Young diagrams are finite lower ideals in the nonnegative integer lattice. An edge exchanges exactly one cell; the multiset description also permits a virtual zero recipient and omits zero remainders.")),
                Node("part", "A row with zero omitted", All("k", V("Nat"),
                    Eq(C("part", V("k")), C("positiveSingleton", V("k")))),
                    "positiveSingleton(k) is empty at zero and contains one occurrence of k otherwise."),
                Node("UnitTransfer", "Two distinct occurrences", TransferFormula(),
                    "The a+1 donor and b recipient are two slots in the multiset decomposition. Thus equal positive sizes require two occurrences; b=0 creates a new part, and a=0 deletes the donor remainder. The residual multiset s retains every unaffected occurrence."),
                Node("graph", "The literal partition graph", OnPartitions(
                    Iff(C("Adj", C("graph", n), p, q), C("UnitTransfer", p, q))),
                    "Reversing the two slots reverses a transfer. Self-results are excluded, so this is a simple graph."),
                Describe.Lean(DescribeId.Create("lyudogovskiy-part-sum"),
                    DeclarationHandle.Create(Prefix + "part_sum"), H("Sum of a row occurrence"),
                    StatementSource.FromAuthor(Disp(All("k", V("Nat"), Eq(C("sum", C("part", V("k"))), V("k"))))),
                    AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Omitting a zero row preserves its sum. The staircase-cardinality proof consumes this helper."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("lyudogovskiy-diagram-injective"),
                    DeclarationHandle.Create(Prefix + "diagram_injective"), H("Partitions determined by their diagrams"),
                    StatementSource.FromAuthor(Disp(All("n", V("Nat"), C("Injective", C("ofPartitionOn", V("n")))))),
                    AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("ofPartitionOn(n) maps each native partition of n to its Young diagram. This is the injectivity inherited from Mathlib's partition/diagram equivalence; the star, top and first-family proofs consume it."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("lyudogovskiy-row-parts"),
                    DeclarationHandle.Create(Prefix + "row_parts"), H("Rows reconstruct the partition multiset"),
                    StatementSource.FromAuthor(Disp(All("d", V("YoungDiagram"), All("H", V("Nat"),
                        Imp(Le(C("colLen", V("d"), D(0)), V("H")),
                            Eq(C("sumPositiveRows", V("d"), V("H")), C("rowLens", V("d")))))))),
                    AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("sumPositiveRows(d,H) is the multiset sum of part(rowLen(d,i)) for i in range(H). Rows beyond the diagram's height are zero and contribute no occurrence. Row decompositions in the converse transfer proof and the staircase-cardinality proof consume this identity."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("lyudogovskiy-transfer-intersection"),
                    DeclarationHandle.Create(Prefix + "transfer_iff_intersection"), H("Transfers and diagram intersections"),
                    StatementSource.FromAuthor(Disp(bridge)), AssessedProvenance.FromRepo(Source),
                    Blocks(Paragraph(Text("A transfer has a common size-(n-1) predecessor: shrink the donor before increasing the recipient. Column counts show inclusion after sorting, including repeated sizes. Conversely the two singleton cell differences lie in distinct rows. Decomposing the row multisets at those indices yields the donor and recipient slots, with zero rows omitted. This bridge does not itself establish either full-question proposition."))), DescribeRole.Theorem))));
    }

    private static Formula TransferFormula()
    {
        var a = V("a"); var b = V("b"); var s = V("s");
        var left = Eq(C("parts", V("p")), Add(Add(C("singleton", Add(a, D(1))), C("part", b)), s));
        var right = Eq(C("parts", V("q")), Add(Add(C("part", a), C("singleton", Add(b, D(1)))), s));
        var slots = Ex("s", C("Multiset", V("Nat")), Ex("a", V("Nat"), Ex("b", V("Nat"), And(left, right))));
        return OnPartitions(Iff(C("UnitTransfer", V("p"), V("q")), And(Ne(V("p"), V("q")), slots)));
    }
    private static Formula OnPartitions(Formula b) => All("n", V("Nat"),
        All("p", C("Partition", V("n")), All("q", C("Partition", V("n")), b)));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose = "") =>
        Describe.Lean(DescribeId.Create("lyudogovskiy-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose.Length == 0 ? title + "." : prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
}
