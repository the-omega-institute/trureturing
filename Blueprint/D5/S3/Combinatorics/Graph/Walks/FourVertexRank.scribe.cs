using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;
internal sealed class FourVertexRankDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/FourVertexRank.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual four-vertex perfect matchings are counted by three supported pairings. Applying matrix rank inequalities gives the weighted and binary rank tables and their signed difference.",
        H("Four-Vertex Matchings and Rank Applications"),
        Blocks(
            Paragraph(Text("Vertices are indexed by Fin 4, with indices 0, 1, 2, 3. The three partner maps exchange respectively the pairs 01 and 23, 02 and 13, and 03 and 12. A perfect matching is an actual SimpleGraph.Subgraph satisfying IsPerfectMatching; it includes every vertex and gives each vertex exactly one adjacent partner.")),
            Describe.Lean(DescribeId.Create("partner-maps"), DeclarationHandle.Create(Prefix + "mate"), H("Three Partner Maps"),
                StatementSource.FromAuthor(Disp(All("j", Call("Fin", D(3)), All("i", Call("Fin", D(4)),
                    Eq(Call("mate", F.Id("j"), F.Id("i")), Call("Entry", Call("PartnerTable"), F.Id("j"), F.Id("i"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("PartnerTable has rows (1,0,3,2), (2,3,0,1), and (3,2,1,0). Every row is an involution without a fixed vertex."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("perfect-matching-count"), DeclarationHandle.Create(Prefix + "pmCount"), H("Actual Perfect-Matching Count"),
                StatementSource.FromAuthor(Disp(All("H", Call("SimpleGraph", Call("Fin", D(4))),
                    Eq(Call("pmCount", F.Id("H")), Call("card", Call("PerfectMatchingSubgraphs", F.Id("H"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("PerfectMatchingSubgraphs(H) is the subtype of all subgraphs M of H with M.IsPerfectMatching. Its cardinality is Nat.card of this finite type."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-matching-count"), DeclarationHandle.Create(Prefix + "actual_matching_count"), H("Exact Matching Objects and Count"),
                StatementSource.FromAuthor(MatchingStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose the unique partner of vertex 0. It is 1, 2, or 3. Symmetry fixes its partner as 0. The two remaining vertices must be paired with each other, because the already paired vertices cannot acquire a second partner. Conversely, each of the three pairings gives a perfect-matching subgraph exactly when both of its edges occur in H. The public equivalence ranges over every actual subgraph M of H: M is a perfect matching if and only if its adjacency relation is one of the three supported partner maps. Support means that H contains every prescribed partner edge. Because every vertex has a partner, these subgraphs also have the full vertex set; no isolated-vertex choices remain. The constructions form a bijection, so their supported indicators sum to the actual cardinality. Each indicator is 1 when its two edges occur and 0 otherwise."))), DescribeRole.Theorem),
            ApplicationParameters(),
            PairingWeights(),
            RankDerivation(),
            RankTables(),
            GraphClassification(),
            SignedDifference())));
    private static DocumentBlock ApplicationParameters() => new DocumentBlock.Section(H("Parameters of the Rank Application"), Blocks(
        Paragraph(Text("The public theorem above identifies matching objects and counts them. The following rank and graph consequences are applications of actual_matching_count and the matrix results named below. They recover Proposition 4.2 of the stabilizer multientropy masked-rank correction theory under the correspondence sending its vertex labels 1, 2, 3, 4 to Fin 4 indices 0, 1, 2, 3; its matrix A is the matrix W here.")),
        Paragraph(Text("Let H be any simple graph on Fin 4. Let K be any field of characteristic two and let lambda be an injective function from Fin 4 to K. Injectivity says exactly that the four labels are pairwise distinct; one label may be zero. No nonzero-label or invertible diagonal-label assumption is needed. Define the natural number p and the matrices W over K and B over ZMod 2 by")),
        Display(Eq(F.Id("p"), Call("pmCount", F.Id("H")))),
        Display(All("i", Call("Fin", D(4)), All("j", Call("Fin", D(4)),
            Eq(Entry(F.Id("W"), F.Id("i"), F.Id("j")), Cases(
                Seq(Add(Label(F.Id("i")), Label(F.Id("j"))), Amp, Call("Adj", F.Id("H"), F.Id("i"), F.Id("j"))),
                Seq(D(0), Amp, Otherwise())))))),
        Display(Eq(F.Id("B"), Call("adjMatrix", Call("ZMod", D(2)), F.Id("H")))),
        Paragraph(Text("B is defined independently: an edge has entry 1 and a nonedge has entry 0. It does not require four distinct labels in ZMod 2, and is not obtained by specializing lambda to that field. Both matrices are symmetric with zero diagonal. Write E for the assertion that H has at least one edge:")),
        Display(Iff(F.Id("E"), Exists("i", Call("Fin", D(4)), Exists("j", Call("Fin", D(4)), Call("Adj", F.Id("H"), F.Id("i"), F.Id("j"))))))));
    private static DocumentBlock PairingWeights() => new DocumentBlock.Section(H("Pairing Weights and Support"), Blocks(
        Paragraph(Text("Index the three pairings by 0, 1, 2 in the order 01 with 23, 02 with 13, and 03 with 12. Let q at each index be 1 when both edges of that pairing occur in H, and 0 otherwise. The count component (actual_matching_count H).2 gives p as their sum; its first component ensures that this counts actual perfect-matching subgraphs, rather than a separately chosen pairing count.")),
        Display(Eq(F.Id("p"), Add(Add(Sub(F.Id("q"), D(0)), Sub(F.Id("q"), D(1))), Sub(F.Id("q"), D(2))))),
        Display(new Formula.Relation(F.Id("p"), FormulaRelationOperator.MemberOf, new Formula.SetLiteral([D(0), D(1), D(2), D(3)]))),
        Paragraph(Text("Define the three complete-pairing weights, whether or not their edges occur in H. These indices correspond to the original omega indices 1, 2, 3:")),
        Display(Eq(Sub(Omega, D(0)), Multiply(Add(Label(D(0)), Label(D(1))), Add(Label(D(2)), Label(D(3)))))),
        Display(Eq(Sub(Omega, D(1)), Multiply(Add(Label(D(0)), Label(D(2))), Add(Label(D(1)), Label(D(3)))))),
        Display(Eq(Sub(Omega, D(2)), Multiply(Add(Label(D(0)), Label(D(3))), Add(Label(D(1)), Label(D(2)))))),
        Display(And(All("j", Call("Fin", D(3)), NotEqual(Sub(Omega, F.Id("j")), D(0))),
            Eq(Add(Add(Sub(Omega, D(0)), Sub(Omega, D(1))), Sub(Omega, D(2))), D(0)))),
        Paragraph(Text("In characteristic two, the sum of two distinct labels cannot be zero, so each factor and each pairing weight is nonzero. Expanding the three products, each product of two different labels occurs twice. Those terms cancel, giving the zero-sum identity. This identity is independent of H; edge support determines which of the three weights contribute."))));
    private static DocumentBlock RankDerivation() => new DocumentBlock.Section(H("From Pairing Sums to Rank"), Blocks(
        Paragraph(Text("For either coefficient field, write a symmetric zero-diagonal matrix M and its complementary matrix C as follows. The six entries a, b, c, d, e, f are respectively the entries on 01, 02, 03, 12, 13, 23; C moves each entry to the opposite pair of vertices.")),
        Display(Eq(F.Id("M"), AlternatingMatrix(F.Id("a"), F.Id("b"), F.Id("c"), F.Id("d"), F.Id("e"), F.Id("f")))),
        Display(Eq(F.Id("C"), AlternatingMatrix(F.Id("f"), F.Id("e"), F.Id("d"), F.Id("c"), F.Id("b"), F.Id("a")))),
        Display(Eq(F.Id("t"), Add(Add(Multiply(F.Id("a"), F.Id("f")), Multiply(F.Id("b"), F.Id("e"))), Multiply(F.Id("c"), F.Id("d"))))),
        Display(And(Eq(Multiply(F.Id("M"), F.Id("C")), Multiply(F.Id("t"), F.Id("I"))),
            Eq(Multiply(F.Id("C"), F.Id("M")), Multiply(F.Id("t"), F.Id("I"))))),
        Paragraph(Text("Here I is the four-dimensional identity matrix. Multiplication gives t on every diagonal entry; every off-diagonal entry is a sum of two equal products and vanishes in characteristic two. If t is nonzero, Matrix.rank_diagonal gives rank 4 for tI. Matrix.rank_mul_le_left and Matrix.rank_le_width then give rank 4 for M.")),
        Paragraph(Text("If t is zero, Matrix.rank_add_rank_le_card_of_mul_eq_zero gives the next inequality. If M has a nonzero entry x on an edge, its principal two-by-two submatrix has diagonal zero and both off-diagonal entries x. Matrix.det_fin_two gives determinant minus x squared, equal to x squared in characteristic two, hence nonzero. Matrix.rank_of_det_ne_zero and Matrix.rank_submatrix_le give rank at least 2. The corresponding opposite pair in C gives the same lower bound for C, so the inequality forces rank 2 for M. If M is zero, Matrix.rank_zero gives rank 0.")),
        Display(new Formula.Relation(Add(Call("rank", F.Id("M")), Call("rank", F.Id("C"))), FormulaRelationOperator.LessThanOrEqual, D(4))),
        Paragraph(Text("For W, t is the sum of the supported pairing weights. For p equal to 0 or 3 this sum is zero. For p equal to 1 it is one nonzero weight. For p equal to 2 it equals the omitted third weight by the zero-sum identity, and is again nonzero. For B, each supported pairing contributes 1, so t is the image of p in ZMod 2: it is nonzero exactly for p equal to 1 or 3. An edge gives a nonzero entry in both W and B; when there are no edges both are zero. These are applications of the named Mathlib matrix results to the actual count, with only finite product expansion and characteristic-two cancellation between them."))));
    private static DocumentBlock RankTables() => new DocumentBlock.Section(H("Weighted and Binary Rank Tables"), Blocks(
        Paragraph(Text("With the parameters and E fixed above, the two tables are")),
        Display(Eq(Call("rank", F.Id("W")), Cases(
            Seq(D(4), Amp, Or(Eq(F.Id("p"), D(1)), Eq(F.Id("p"), D(2)))),
            Seq(D(2), Amp, And(Or(Eq(F.Id("p"), D(0)), Eq(F.Id("p"), D(3))), F.Id("E"))),
            Seq(D(0), Amp, Not(F.Id("E")))))),
        Display(Eq(Call("rank", F.Id("B")), Cases(
            Seq(D(4), Amp, Or(Eq(F.Id("p"), D(1)), Eq(F.Id("p"), D(3)))),
            Seq(D(2), Amp, And(Or(Eq(F.Id("p"), D(0)), Eq(F.Id("p"), D(2))), F.Id("E"))),
            Seq(D(0), Amp, Not(F.Id("E")))))),
        Paragraph(Text("Ranks here are Matrix.rank, natural numbers computed over the matrix's own field. The rows exhaust all graphs because p is between 0 and 3, and a supported perfect matching supplies edges. In particular, p equal to 0 alone does not distinguish rank 2 from rank 0; edge existence makes that distinction. The binary table holds for every H without any assumption on K or lambda."))));
    private static DocumentBlock GraphClassification() => new DocumentBlock.Section(H("Classification of the Entire Graph"), Blocks(
        Paragraph(Text("Two distinct supported pairings have no common edge, and their union is a four-cycle. The two remaining edges form the third pairing. If p is 2, either zero or one of the remaining edges can be present: including both would support the third pairing. Thus the entire graph is a four-cycle or a four-cycle with one diagonal, the diamond. Conversely, each of these entire graphs supports exactly two pairings. If p is 3, all three pairings occur, and their six edges exhaust the complete graph. This gives both directions of the following equivalences:")),
        Display(Iff(Eq(F.Id("p"), D(2)), Or(WholeGraph(Call("cycleGraph", D(4))),
            WholeGraph(Call("deleteEdges", Call("completeGraph", Call("Fin", D(4))), Call("edge", D(0), D(2))))))),
        Display(Iff(Eq(F.Id("p"), D(3)), Eq(F.Id("H"), Call("completeGraph", Call("Fin", D(4)))))),
        Paragraph(Text("In the first formula, deleteEdges denotes removal of the undirected edge 02, exactly the graph (top minus SimpleGraph.edge 0 2); this is a fixed representative of the diamond. Each quantified equivalence e is a permutation of all four vertices, and adjacency is preserved and reflected for every ordered pair. The classification is up to isomorphism of the entire graph, not containment of a cycle or diamond inside a larger graph. The complete-graph clause is literal graph equality. Both clauses hold for arbitrary H, including the edgeless graph, without an edge-existence hypothesis."))));
    private static DocumentBlock SignedDifference() => new DocumentBlock.Section(H("Signed Rank Difference and Scope"), Blocks(
        Paragraph(Text("Convert each natural-number rank separately to Int and then subtract. Subtracting the two tables gives")),
        Display(Eq(Subtract(Call("IntCast", Call("rank", F.Id("W"))), Call("IntCast", Call("rank", F.Id("B")))), Cases(
            Seq(D(2), Amp, Eq(F.Id("p"), D(2))),
            Seq(new Formula.Negate(D(2)), Amp, Eq(F.Id("H"), Call("completeGraph", Call("Fin", D(4))))),
            Seq(D(0), Amp, Otherwise())))),
        Paragraph(Text("IntCast denotes the natural-number cast to Int. For a four-cycle or diamond the ranks are 4 and 2; for the complete graph they are 2 and 4. With p equal to 1 both ranks are 4. With p equal to 0 and an edge both ranks are 2, and for the edgeless graph both are 0. Thus the difference is positive exactly on the two entire-graph isomorphism types in the p equal to 2 clause, negative exactly on the complete graph, and zero in every other case. A cast after natural-number subtraction would lose the negative value.")),
        Paragraph(Text("The weighted table and the signed difference require all four labels to be distinct in a characteristic-two field. They do not assert the same values for repeated labels, other characteristics, arbitrary edge weights, or more vertices. The binary table and the graph classification require only the four-vertex graph. These are algebraic and graph-theoretic consequences of the matching count and the cited matrix inequalities; they assert no physical realization, computational resource bound, or literature novelty."))));
    private static Formula MatchingStatement()
    {
        Formula g = F.Id("H");
        Formula j = F.Id("j"), i = F.Id("i"), k = F.Id("k"), m = F.Id("M");
        Formula supported = All("i", Call("Fin", D(4)), Call("Adj", g, i, Call("mate", j, i)));
        Formula sameEdges = All("i", Call("Fin", D(4)), All("k", Call("Fin", D(4)),
            Iff(Call("Adj", m, i, k), Eq(Call("mate", j, i), k))));
        Formula objects = All("M", Call("Subgraph", g), Iff(Call("IsPerfectMatching", m),
            Exists("j", Call("Fin", D(3)), And(supported, sameEdges))));
        return Disp(All("H", Call("SimpleGraph", Call("Fin", D(4))), And(objects, Eq(Call("pmCount", g),
            Seq(Indicator(And(Call("Adj", g, D(0), D(1)), Call("Adj", g, D(2), D(3)))), Plus,
                Indicator(And(Call("Adj", g, D(0), D(2)), Call("Adj", g, D(1), D(3)))), Plus,
                Indicator(And(Call("Adj", g, D(0), D(3)), Call("Adj", g, D(1), D(2)))))))));
    }
    private static DocumentBlock Display(Formula value) => new DocumentBlock.DisplayFormula(Disp(value));
    private static Formula Sub(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula Label(Formula index) => Call("lambda", index);
    private static Formula Entry(Formula matrix, Formula i, Formula j) => Call("Entry", matrix, i, j);
    private static Formula Otherwise() => Seq(Operatorname, Grp(F.Id("otherwise")));
    private static Formula Cases(Formula first, Formula second) => Seq(Begin, Grp(F.Id("cases")), first, RowBreak, second, End, Grp(F.Id("cases")));
    private static Formula Cases(Formula first, Formula second, Formula third) => Seq(Begin, Grp(F.Id("cases")), first, RowBreak, second, RowBreak, third, End, Grp(F.Id("cases")));
    private static Formula Not(Formula value) => Seq(Neg, Open, value, Close);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Or, Seq(Open, b, Close));
    private static Formula WholeGraph(Formula graph) => Exists("e", Call("Equiv", Call("Fin", D(4)), Call("Fin", D(4))),
        All("u", Call("Fin", D(4)), All("v", Call("Fin", D(4)),
            Iff(Call("Adj", F.Id("H"), Call("e", F.Id("u")), Call("e", F.Id("v"))), Call("Adj", graph, F.Id("u"), F.Id("v"))))));
    private static Formula AlternatingMatrix(Formula a, Formula b, Formula c, Formula d, Formula e, Formula f) => Seq(
        Begin, Grp(F.Id("bmatrix")),
        D(0), Amp, a, Amp, b, Amp, c, RowBreak,
        a, Amp, D(0), Amp, d, Amp, e, RowBreak,
        b, Amp, d, Amp, D(0), Amp, f, RowBreak,
        c, Amp, e, Amp, f, Amp, D(0),
        End, Grp(F.Id("bmatrix")));
    private static Formula Indicator(Formula p) => Call("indicator", p);
    private static Formula Call(string n, params Formula[] a) => a.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(n)) : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(n)), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Exists(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Iff, Seq(Open, b, Close));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.And, Seq(Open, b, Close));
}
