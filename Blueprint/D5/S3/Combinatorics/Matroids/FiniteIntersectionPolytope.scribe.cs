using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class FiniteIntersectionPolytopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual nonnegative rank-inequality intersection of two finite matroids has only zero-one extreme points.",
        H("Extreme points of finite matroid intersection"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-matroid-intersection-polytope"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/FiniteIntersectionPolytope.extreme_point_zero_one"),
            H("The rank-inequality intersection has zero-one extreme points"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/FiniteGeometry/goemans2015intersection")),
            Blocks(
                Paragraph(Text(
                    "Let E be any finite type in an arbitrary universe, and let M and N be native matroids on E with both grounds equal to all of E. For every subset U of E, write r(M,U) for the natural number ENat.toNat of Matroid.eRk M U, regarded as a real number in inequalities. All these extended ranks are finite. Define P to consist of actual real vectors x on E whose coordinates are nonnegative and whose sum on every U is at most both r(M,U) and r(N,U). The theorem says that every real extreme point of this P has each coordinate equal to zero or one.")),
                Paragraph(Text(
                    "The displayed P is the inequality region itself. The theorem assumes neither a convex-hull identity nor an integral dual. Empty E, loops, rank-zero matroids, unequal ranks and nonrepresentable matroids are included. There is no common-basis, nonempty-ground, positive-rank, loopless, supplied-chain or unique-equation hypothesis. The use of finite-set sums does not select an enumeration of E.")),
                Paragraph(Text(
                    "Fix an extreme point v. In each rank family, submodularity and the modular identity for finite sums show that the v-tight subsets are closed under union and intersection. Choose a maximal inclusion chain from that actual tight family. For a chain member A, its predecessor is the union of the strictly smaller chain members, and its layer is A minus that predecessor. The predecessor is tight, so its layer sum at v is the integer rank difference r(M,A) minus r(M,pred A).")),
                Paragraph(Text(
                    "Every tight subset contains each chain layer wholly or misses it. Indeed, the union of the predecessor with the intersection of that subset and A is tight and comparable with the chain. Maximality permits no proper intermediate layer cut. The layers are disjoint, cover the union of all tight subsets, and therefore recover every tight subset sum. The chain top is this tight union; it need not equal E. This construction gives the compression of actual equations rather than assuming an incidence span.")),
                Paragraph(Text(
                    "Apply the existing active-constraint kernel theorem to the complete actual finite inequality family: negative coordinate projections and subset-sum forms from both matroids. A direction killed by all zero-coordinate equations and both layer families is killed by every tight rank form, and hence is zero. Thus the layer equations and actual zero-coordinate equations determine v among all real vectors, without requiring an alternative vector to be feasible. No full-dimensionality assumption or externally supplied positive-slack bound is required.")),
                Paragraph(Text(
                    "Use the disjoint layers as rows, with the second family negated. Every coordinate has at most one endpoint in each family; give an uncovered side a dummy endpoint and delete the dummy rows. This identifies the layer matrix directly with a submatrix of an integer signed-incidence matrix. The existing signed-incidence theorem gives total unimodularity, and the existing unit-row extension adds exactly the zero-coordinate equations. No assertion is made that the complete subset-rank matrix is totally unimodular, or that arbitrary row operations preserve total unimodularity.")),
                Paragraph(Text(
                    "The resulting integer matrix A and integer right-hand side b satisfy A over the reals times v equals b. The existing integer inner-inverse theorem gives an integer B with ABA equal to A, including empty or rank-deficient matrices. Therefore the real cast of the integer vector B times b solves the same equations. Their proved uniqueness identifies it with v. Nonnegativity and the singleton rank bound, which holds also at loops, put each integer coordinate between zero and one.")),
                Paragraph(Text(
                    "Goemans's matroid-intersection notes, Theorem 6.6, give the classical vertex argument; Lemma 5.5 and Theorem 5.6 of the matroid-optimization notes supply tight-set closure and chain compression. The latter is the result referred to by the stale Theorem 4.6 cross-reference in the intersection notes. The two-family incidence context also appears as Claim 3 in the 2009 lecture notes. This formalization carries no originality or open-problem claim. Weighted optimization and fractional decomposition are prospective applications and are not conclusions of this theorem."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula e = V("E"), m = V("M"), n = V("N"), v = V("v"), x = V("x"), u = V("U");
        Formula vector = Seq(e, Sp, To, Sp, Reals);
        Formula bounds = All("U", Call("Set", e), And(
            Le(SubsetSum(x, u), Rank(m, u)), Le(SubsetSum(x, u), Rank(n, u))));
        Formula feasible = And(All("a", e, Le(D(0), App(x, V("a")))), bounds);
        Formula region = Seq(Left, OpenBrace, x, Colon, Sp, vector, Sp, Mid, Sp, feasible, Right, CloseBrace);
        Formula extreme = Rel(v, InMacro, Call("extremePoints", Reals, region));
        Formula result = All("a", e, Or(Equal(App(v, V("a")), D(0)), Equal(App(v, V("a")), D(1))));
        result = All("v", vector, Imp(extreme, result));
        result = Imp(Equal(Call("ground", n), V("univ")), result);
        result = Imp(Equal(Call("ground", m), V("univ")), result);
        result = All("N", Call("Matroid", e), result);
        result = All("M", Call("Matroid", e), result);
        result = Seq(OpenBracket, Call("Finite", e), CloseBracket, Comma, Sp, result);
        return All("E", new Formula.Subscript(V("Type"), V("u")), result);
    }

    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, V(name), Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Rel(Formula a, Formula relation, Formula b) => Seq(a, Sp, relation, Sp, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Rank(Formula m, Formula u) => Call("toNat", Call("eRk", m, u));
    private static Formula SubsetSum(Formula x, Formula u) =>
        Seq(new Formula.Subscript(Sum, Rel(V("a"), InMacro, u)), Sp, App(x, V("a")));
}
