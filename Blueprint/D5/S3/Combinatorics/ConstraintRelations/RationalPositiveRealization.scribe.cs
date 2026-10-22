using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ConstraintRelations;

internal sealed class RationalPositiveRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ConstraintRelations/RationalPositiveRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict five-mode rational networks have exactly graph-independent supports, with arbitrary positive masses.",
        H("Exact rational laws from strictly positive five-mode tables"),
        Blocks(
            Node("strict-full-table", "Strict positivity on all five allowed tuples", "Strict", StatementSource.WithoutFormula(),
                "Strict is a property of the existing Table: its value is positive at every tuple of A. The full eight-entry table is nonnegative, sums to one, and vanishes outside A by the Table structure. Thus its support is exactly 000, 100, 010, 110 and 001, including entries that a repeated scope never visits.", DescribeRole.Definition),
            Node("labelled-loop-graph", "Labelled undirected graphs with loops", "LoopGraph", StatementSource.WithoutFormula(),
                "A LoopGraph on n coordinates has a symmetric adjacency relation on Fin n. Diagonal adjacency is permitted. No irreflexivity assumption discards loops.", DescribeRole.Definition),
            Node("loop-independent-words", "Independent Boolean words", "Independent", StatementSource.WithoutFormula(),
                "A word a is independent when a(i) and a(j) are not simultaneously one at any adjacent pair i,j. A loop forces its coordinate to zero. The all-zero word is always independent; with no edges every word is independent.", DescribeRole.Definition),
            Node("strict-representability", "The exact finite representation predicate", "Representable", StatementSource.WithoutFormula(),
                "Representable P means that some finite natural hidden count m and factor count k admit an existing Network n m k. Each factor's existing Table is Strict, the existing partition is positive, and its existing normalized law equals P at every visible assignment. Factors have ordered triples of actual variables in Fin n plus Fin m, with repetition permitted. The weight is the finite product, including the empty product one; the marginal sums every hidden assignment.", DescribeRole.Definition),
            Node("strict-rational-classification", "All rational masses on every independent support", "result", StatementSource.FromAuthor(ResultFormula()),
                "For every natural n and every nonnegative rational law P on the Boolean n-cube with total one, P has an exact finite representation by strict five-mode factors if and only if its positive support is the independent-word family of some labelled undirected graph with loops. In particular this includes every n at least one, every positive rational mass assignment on such a support, isolated coordinates, loops and the singleton all-zero support. The same statement also holds for the zero-dimensional cube.", DescribeRole.Theorem),
            Paragraph(Text("For necessity, each factor on actual variables (u,w,t) excludes the pairs (u,t) and (w,t). Keep both directions and every diagonal exclusion to obtain a symmetric graph on the visible coordinates. A positive full weight satisfies every exclusion. Conversely an independent visible word extends positively by assigning zero to every hidden variable. Nonnegative finite sums detect a positive summand. The complete zero assignment proves that the partition is positive, even with no factors and with arbitrary finite hidden count.")),
            Paragraph(Text("The construction uses the existing normalized pin table, the indicator of A divided by five, on (o,o,o) for a fresh hidden variable o. This forces o to zero internally. Its scope (u,u,w) enforces the exclusion of simultaneous ones. The existing unary table has values one at 000, 100, 010 and 001, value c at 110, and zero elsewhere, divided by four plus c. On (u,u,o) it supplies activities one and c. Every c used here is positive.")),
            Paragraph(Text("A positive binary table B is realized by the full ternary table with value B(x,y) at (x,y,0), value one at 001, and zero elsewhere, divided by one plus the sum of the four B entries. Its scope is (u,v,o). All five allowed entries are positive and all eight entries are included in normalization. Binary weights and unary activities below are implemented by these actual ternary factors.")),
            Paragraph(Text("For a positive rational full-cube table w, choose a positive rational L so that r(a)=Lw(a)-1 is positive for every a. Define M(e)(a,s) as the product over coordinates of one when a(i)=s(i) and e otherwise. At zero this rational matrix is the identity. Continuity of the determinant and inverse gives a rational e strictly between zero and one for which M(e) is invertible and c=M(e) inverse times r has every entry positive. Thus one plus the sum over s of c(s)M(e)(a,s) equals Lw(a) exactly. Continuity establishes a single rational choice; the network uses no limiting operation.")),
            Paragraph(Text("Introduce one hidden selector for each full visible word s. Pairwise exclusion factors permit exactly the all-zero selector assignment and assignments with exactly one selected word. Its activity is c(s). The binary table between selector s and visible coordinate i is one when the selector is zero, and otherwise is one when a(i)=s(i) and e when they differ. Comparing entries with the fixed index s(i) does not complement a scope variable. The hidden pin and selector assignments give respectively one and c(s)M(e)(a,s), times the same positive normalization scalar. Every other hidden assignment violates a pin or an exclusion and has weight zero. The full hidden sum is therefore computed over its entire assignment space.")),
            Paragraph(Text("Given graph-independent support, extend P to the positive full-cube table w that equals P on independent words and one elsewhere. Add a visible exclusion factor for every adjacency pair, including diagonal pairs; nonedges can use the internally pinned scope. Their product is the independent-word indicator times a positive constant. The marginal is exactly C L P for a positive rational C. Summing P gives partition C L, and final normalization recovers P. Finite equivalences number the actual hidden variables and factors using the existing Network constructor.")),
            Paragraph(Text("The conclusion concerns globally normalized rational potentials. It supplies neither an efficiency bound nor a causal sampling interpretation. Constants, complemented scope literals, supplied equality or disequality, external unary or multivariate factors, and limits are absent from the factor language. The matrix argument and selector construction establish arbitrary weights as well as support."))
        ), []));

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m"), k = F.Id("k"), a = F.Id("a"), net = F.Id("net");
        Formula cube = Arrow(Call("Fin", n), Named("Bool")), rat = Named("Rat"), nat = Named("Nat");
        Formula hypotheses = And(All("a", cube, Rel(D(0), FormulaRelationOperator.LessThanOrEqual, Call("P", a))),
            Rel(Seq(F.Sum, Underscore, Grp(a, Sp, InMacro, Sp, cube), Sp, Call("P", a)), FormulaRelationOperator.Equal, D(1)));
        Formula strict = All("j", Call("Fin", k), Call("Strict", Call("table", Call("factor", net, F.Id("j")))));
        Formula representation = Exists("m", nat, Exists("k", nat, Exists("net", Call("Network", n, m, k),
            And(strict, And(Rel(D(0), FormulaRelationOperator.LessThan, Call("partition", net)),
                All("a", cube, Rel(Call("law", net, a), FormulaRelationOperator.Equal, Call("P", a))))))));
        Formula support = Exists("K", Call("LoopGraph", n), All("a", cube,
            Iff(Rel(D(0), FormulaRelationOperator.LessThan, Call("P", a)), Call("Independent", F.Id("K"), a))));
        return Disp(All("n", nat, All("P", Arrow(cube, rat), Imp(hypotheses, Iff(representation, support)))));
    }

    private static DocumentBlock Node(string id, string title, string name, StatementSource statement,
        string prose, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Named(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, Close, Sp, To, Sp, b);
    private static Formula All(string x, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, b);
    private static Formula Exists(string x, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.And, Grp(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.Iff, Grp(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.Implies, Grp(b));
}
