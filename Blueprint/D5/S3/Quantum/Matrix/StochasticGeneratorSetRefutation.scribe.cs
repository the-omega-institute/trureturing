using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class StochasticGeneratorSetRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/vomendeshahbeigi2024stochasticgenerators");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A column-stochastic matrix with six-cycle support cannot be obtained from the generators of Eq. (10).",
        H("The proposed stochastic generator set misses a six-cycle matrix"),
        Blocks(
            Paragraph(Text(
                "All matrices are real and have rows and columns indexed by Fin 3, namely 0, 1, 2. "
                    + "The symbol 1 denotes the identity matrix. A column-stochastic matrix has nonnegative "
                    + "entries and each column sums to one; these conditions are written out in claim.")),
            Node("v1", "V1", "The first vertex of Eq. (10)",
                Disp(Equal(Typed(V("V1"), MatrixType()),
                    MatrixEntries(D(1), D(0), D(1), D(0), D(1), D(0), D(0), D(0), D(0)))),
                "The first nonidentity vertex sends coordinates 0 and 2 to coordinate 0 and fixes coordinate 1."),
            Node("v2", "V2", "The second vertex of Eq. (10)",
                Disp(Equal(Typed(V("V2"), MatrixType()),
                    MatrixEntries(D(1), D(0), D(1), D(0), D(0), D(0), D(0), D(1), D(0)))),
                "The second nonidentity vertex sends coordinates 0 and 2 to coordinate 0 and sends coordinate 1 to coordinate 2."),
            Node("v3", "V3", "The cyclic vertex of Eq. (10)",
                Disp(Equal(Typed(V("V3"), MatrixType()),
                    MatrixEntries(D(0), D(0), D(1), D(1), D(0), D(0), D(0), D(1), D(0)))),
                "The third nonidentity vertex is the cyclic permutation matrix sending 0 to 1, 1 to 2, and 2 to 0."),
            Node("swap12", "swap12", "The transposition in Eq. (10)",
                Disp(Equal(Typed(V("swap12"), MatrixType()),
                    MatrixEntries(D(0), D(1), D(0), D(1), D(0), D(0), D(0), D(0), D(1)))),
                "The transposition interchanges coordinates 0 and 1 and fixes coordinate 2."),
            Node("gen", "gen", "The proposed generator set", GeneratorFormula(),
                "Equation (10) takes the union of the singleton containing swap12 and the real convex hull "
                    + "of the identity and V1, V2, V3. A convex combination has nonnegative real weights summing to one."),
            Node("genpow", "genPow", "Products of a fixed number of generators", ProductFormula(),
                "The set genPow(m) consists of products of exactly m elements of gen, with repetitions allowed. "
                    + "Zero factors give the identity. Each additional factor multiplies a shorter product on the left. "
                    + "This is the product length used in Definition 3."),
            Node("claim", "claim", "The proposed optimal length twenty", ClaimFormula(),
                "Theorem 3 asserts that every column-stochastic 3 by 3 matrix is a product of twenty elements "
                    + "of the set in Eq. (10). The conjecture in Section 4 asserts optimality: some column-stochastic "
                    + "matrix is not a product of nineteen. Since the identity belongs to gen, shorter products "
                    + "can be padded with identity factors, so the two clauses express the proposed optimal length twenty."),
            Describe.Lean(
                DescribeId.Create("stochastic-generator-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A six-cycle matrix contradicts the twenty-factor assertion"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(V("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take A = [[1/4, 0, 1/4], [3/4, 1/2, 0], [0, 1/2, 3/4]]. "
                            + "Its entries are nonnegative and every column sums to one. Its positive entries form "
                            + "the bipartite six-cycle row 0, column 0, row 1, column 1, row 2, column 2, row 0.")),
                    Paragraph(Text(
                        "A has the following indivisibility property: if B and C are column-stochastic and their product "
                            + "is a row and column permutation of A, then B or C is a permutation matrix. "
                            + "For each intermediate coordinate, the positive entries of the corresponding column "
                            + "of B and row of C form a rectangle in the support of the product. The six-cycle "
                            + "contains no rectangle with two rows and two columns. Covering its six edges by "
                            + "three rectangles therefore gives three stars centred at the three rows or at the "
                            + "three columns. Column normalization makes one factor a permutation matrix.")),
                    Paragraph(Text(
                        "No row and column permutation of A belongs to gen. Such a matrix has six positive "
                            + "entries, whereas swap12 has three. The convex hull has zeros at positions (0,1), "
                            + "(1,2), (2,0) and weakly decreasing diagonal entries. None of the thirty-six row and "
                            + "column permutations of A satisfies all these conditions. If a permuted A were a "
                            + "finite product from gen, indivisibility would let permutation factors be removed "
                            + "until a row and column permutation of A belonged to gen, a contradiction. "
                            + "In particular A is not a product of twenty generators, so claim is false."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("vom-ende-shahbeigi-2024-stochastic-generator-set-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("stochastic-generator-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula GeneratorFormula() => Disp(Equal(V("gen"),
        Seq(new Formula.SetLiteral([V("swap12")]), Sp, Cup, Sp,
            Call("convexHull", Reals(), new Formula.SetLiteral([
                Typed(D(1), MatrixType()), V("V1"), V("V2"), V("V3")])))));

    private static Formula ProductFormula()
    {
        Formula a = V("A"), g = V("g"), w = V("w"), m = V("m");
        Formula products = Seq(OpenBrace, Typed(a, MatrixType()), Sp, Mid, Sp,
            Some("g", MatrixType(), And(Member(g, V("gen")),
                Some("w", MatrixType(), And(Member(w, Call("genPow", m)),
                    Equal(a, Multiply(g, w)))))), CloseBrace);
        return Disp(And(Equal(Call("genPow", D(0)), new Formula.SetLiteral([Typed(D(1), MatrixType())])),
            All("m", Naturals(), Equal(Call("genPow", Add(m, D(1))), products))));
    }

    private static Formula ClaimFormula()
    {
        Formula a = V("A");
        return Disp(IffOf(V("claim"), And(
            All("A", MatrixType(), Imp(StochasticConditions(a), Member(a, Call("genPow", D(2, 0))))),
            Some("A", MatrixType(), And(StochasticConditions(a),
                new Formula.Not(Parenthesized(Member(a, Call("genPow", D(1, 9))))))))));
    }

    private static Formula StochasticConditions(Formula a) => And(
        All("i", Indices(), All("j", Indices(), LE(D(0), Apply(a, V("i"), V("j"))))),
        All("j", Indices(), Equal(
            Seq(new Formula.Subscript(Sum, Typed(V("i"), Indices())), Sp,
                Apply(a, V("i"), V("j"))), D(1))));

    private static Formula MatrixEntries(Formula a, Formula b, Formula c, Formula d, Formula e,
        Formula f, Formula g, Formula h, Formula i) => Seq(
        Begin, Grp(V("bmatrix")), a, Amp, b, Amp, c, RowBreak,
        d, Amp, e, Amp, f, RowBreak, g, Amp, h, Amp, i, End, Grp(V("bmatrix")));
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Indices() => Call("Fin", D(3));
    private static Formula MatrixType() => Call("Matrix", Indices(), Indices(), Reals());
    private static Formula Call(string name, params Formula[] arguments) => Apply(V(name), arguments);
    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
