using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class LyudogovskiySimplexDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lyudogovskiy2026simplex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual integer-partition unit transfers determine finite clique maxima and exact local layers.",
        H("Unit transfers and local simplex layers"), Blocks(
            Paragraph(Text("Nat denotes the nonnegative integers. Partition(n) is the multiset of positive parts with sum n. Every occurrence is retained. A unit transfer removes one unit from one part occurrence and adds it to a distinct occurrence or to a virtual zero row; zero remainders disappear. The resulting partition must differ from the original. YoungDiagram.ofPartition sorts the parts and draws each row as an initial interval of cells. All cliques, maxima and layer cardinalities below use the actual finite partition carrier.")),
            Node("part", "A row with zero omitted", All("k", V("Nat"),
                Eq(C("part", V("k")), C("positiveSingleton", V("k")))),
            Node("UnitTransfer", "Two distinct occurrences", All("n", V("Nat"),
                All("p", C("Partition", V("n")), All("q", C("Partition", V("n")),
                    Iff(C("UnitTransfer", V("p"), V("q")), And(Ne(V("p"), V("q")),
                        Ex("s", C("Multiset", V("Nat")), Ex("a", V("Nat"), Ex("b", V("Nat"),
                            And(Eq(C("parts", V("p")), Add(Add(C("singleton", Add(V("a"), D(1))), C("part", V("b"))), V("s"))),
                                Eq(C("parts", V("q")), Add(Add(C("part", V("a")), C("singleton", Add(V("b"), D(1)))), V("s")))))))))))),
                "positiveSingleton(k) is empty at zero and contains one occurrence of k otherwise. The a+1 donor and b recipient are two slots in the multiset decomposition. Thus equal positive sizes require two occurrences; b=0 creates a new part, and a=0 deletes the donor remainder."),
            Node("graph", "The literal partition graph", All("n", V("Nat"),
                All("p", C("Partition", V("n")), All("q", C("Partition", V("n")),
                    Iff(C("Adj", C("graph", V("n")), V("p"), V("q")), C("UnitTransfer", V("p"), V("q"))))),
                "Reversing the two slots reverses a transfer. Self-results are excluded, so this is a simple graph."),
            Node("cliques", "All finite cliques", All("n", V("Nat"),
                All("s", C("Finset", C("Partition", V("n"))),
                    Iff(In(V("s"), C("cliques", V("n"))), C("IsClique", C("graph", V("n")), V("s"))))),
            Node("localDimension", "The largest clique through a vertex", All("n", V("Nat"),
                All("p", C("Partition", V("n")), Eq(C("localDimension", V("p")),
                    C("max", C("cliqueDimensionsContaining", V("n"), V("p")))))),
                "cliqueDimensionsContaining(n,p) contains card(s)-1 for every clique s containing p. The singleton clique ensures this collection is nonempty."),
            Node("layer", "An exact level", All("r", V("Nat"), All("n", V("Nat"),
                All("p", C("Partition", V("n")), Iff(In(V("p"), C("layer", V("r"), V("n"))),
                    Eq(C("localDimension", V("p")), V("r"))))))),
            Node("maxDimension", "Maximum local dimension", All("n", V("Nat"),
                Eq(C("maxDimension", V("n")), C("max", C("localDimensions", V("n")))))),
            Node("threshold", "Least positive occurrence", All("r", V("Nat"),
                Eq(C("threshold", V("r")), C("sInf", C("positiveNonemptyLevels", V("r")))))),
                "positiveNonemptyLevels(r) contains precisely the positive n with a nonempty exact layer(r,n). The natural-number infimum is zero when this set is empty; the full threshold claim explicitly requires existence and leastness."),
            Node("triangular", "Triangular sizes", All("r", V("Nat"),
                Eq(C("triangular", V("r")), C("natDiv", Mul(V("r"), Add(V("r"), D(1))), D(2)))))),
            Node("staircase", "The staircase ideal", All("r", V("Nat"), All("i", V("Nat"), All("j", V("Nat"),
                Iff(In(C("pair", V("i"), V("j")), C("staircase", V("r"))), Lt(Add(V("i"), V("j")), V("r"))))))),
            Node("firstFamily", "All addable one-cell extensions", All("r", V("Nat"), All("n", V("Nat"),
                All("p", C("Partition", V("n")), Iff(In(V("p"), C("firstFamily", V("r"), V("n"))),
                    And(C("subset", C("cells", C("staircase", V("r"))), C("cells", C("ofPartition", V("p")))),
                        Eq(C("card", C("sdiff", C("cells", C("ofPartition", V("p"))), C("cells", C("staircase", V("r"))))), D(1)))))))),
            Node("ThresholdClaim", "The full threshold question", Iff(C("ThresholdClaim"),
                And(All("r", V("Nat"), And(Eq(C("threshold", V("r")), Add(C("triangular", V("r")), D(1))),
                    C("IsLeast", C("positiveNonemptyLevels", V("r")), Add(C("triangular", V("r")), D(1))))),
                    All("n", V("Nat"), Imp(Lt(D(0), V("n")), Eq(C("maxDimension", V("n")), C("max", C("triangularRanksBelow", V("n"))))))))),
                "triangularRanksBelow(n) is the finite set of r<=n for which triangular(r)+1<=n. This is a proposition specifying the entire threshold and maximum problem; its definition supplies no proof of that proposition."),
            Node("FirstOccurrenceClaim", "The full first-family question", Iff(C("FirstOccurrenceClaim"),
                All("r", V("Nat"), Imp(Le(D(2), V("r")), And(
                    Eq(C("layer", V("r"), C("threshold", V("r"))), C("firstFamily", V("r"), C("threshold", V("r")))),
                    And(Eq(C("layer", V("r"), Add(C("triangular", V("r")), D(1))), C("firstFamily", V("r"), Add(C("triangular", V("r")), D(1)))),
                        Eq(C("card", C("firstFamily", V("r"), C("threshold", V("r")))), Add(V("r"), D(1))))))))),
                "Both equalities are equalities of full finite vertex sets. The cardinality requires r+1 distinct family members. This proposition includes r=2 and quantifies without an upper bound; its definition supplies no proof."),
            Describe.Lean(DescribeId.Create("lyudogovskiy-transfer-intersection"),
                DeclarationHandle.Create(Prefix + "transfer_iff_intersection"), H("Transfers and diagram intersections"),
                StatementSource.FromAuthor(Disp(All("n", V("Nat"), Imp(Lt(D(0), V("n")),
                    All("p", C("Partition", V("n")), All("q", C("Partition", V("n")),
                        Iff(C("UnitTransfer", V("p"), V("q")), Eq(C("card", C("inf", C("ofPartition", V("p")), C("ofPartition", V("q")))), Sub(V("n"), D(1)))))))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("A transfer has a common size-(n-1) predecessor: shrink the donor before increasing the recipient. Column counts show inclusion after sorting, including repeated sizes. Conversely the two singleton cell differences lie in distinct rows. Decomposing the row multisets at those two indices yields the donor and recipient slots, with zero rows omitted. This representation bridge does not itself establish either threshold or first-family proposition."))), DescribeRole.Theorem))));

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
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
