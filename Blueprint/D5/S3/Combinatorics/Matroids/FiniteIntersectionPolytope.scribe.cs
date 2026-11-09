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
                    "Goemans's matroid-intersection notes, Theorem 6.6, give the classical vertex argument; Lemma 5.5 and Theorem 5.6 of the matroid-optimization notes supply tight-set closure and chain compression. The latter is the result referred to by the stale Theorem 4.6 cross-reference in the intersection notes. The two-family incidence context also appears as Claim 3 in the 2009 lecture notes. This formalization carries no originality or open-problem claim.")),
                Paragraph(Text(
                    "The zero-one conclusion is the integrality step in the following application. In every universe u, let E : Type u be finite, let M1 and M2 be native matroids on E with equal, possibly proper, grounds, assume that some common base exists, and let w : E -> Z be arbitrary. The actual sum of an integer q on a set B is the finite sum sum over e in B.toFinite.toFinset of q(e). The finite nonempty family of common bases therefore has an internally selected minimum w-sum B; no optimum, split, or certificate is supplied as a premise.")),
                Paragraph(Text(
                    "For a native matroid M and an integer q, the local-to-global step starts from every legal one-element exchange: b is in B, e is in M.E minus B, and insert e into B minus {b} is a base. For each real threshold t use the proper-ground set X_t = {e in M.E | (q(e):R) <= t} and I = B intersect X_t. If I were not an M.IsBasis of X_t, native augmentation supplies an element e in X_t and the existing exchange_base_over_independent_subset supplier supplies a removable b outside X_t, producing a cheaper base and contradicting the local inequality. The existing native_weighted_base_rank_saturation supplier then gives q(B) <= q(C) for every native base C, including proper-ground cases.")),
                Paragraph(Text(
                    "To compare the two matroids, use the tagged exchange graph built from the actual legal arcs (t,b,e). A true tag records a first-matroid exchange directed from b to e; a false tag records a second-matroid exchange directed from e to b. With equal grounds, both tags use the same outside set. The arc sign is zero on a true arc and w(b) - w(e) on a false arc. The weight of a walk is the sum over its complete edge list, so repeated edges and repeated vertices contribute with their multiplicities.")),
                Paragraph(Text(
                    "For a closed walk p with L edges, form the actual averaged exchange-base incidence vectors. For an edge a = (tag,b,e) and each tag t, let A_t(a) be the exchanged-base incidence only when tag = t, and let A_t(a) be chi_B otherwise. Thus, averaging over all L edge occurrences, z_t = (chi_B + sum_a A_t(a))/(L + 1). The denominator is positive, even for the empty walk. The tagged orientations give the closed-walk incidence balance; applying Maths.MaxPlusPotential.IsPotential.walkWeight_add_le to the incidence difference and to its negative retains both inequalities before they give z_true = z_false coordinate by coordinate. Each average is nonnegative, obeys every rank inequality of its native matroid, and has total coordinate sum equal to the cardinality of B.")),
                Paragraph(Text(
                    "Call this common vector H. For the total-cardinality objective subject to the two rank systems, card_max = |B|, attained by H and by the common-base incidence chi_B. Expose that maximum-cardinality face first, then the minimum-w exposed subface; compactness and the existing extreme-point existence result provide an extreme point on the subface, and extremality is inherited through both exposed faces. Apply the present zero-one theorem after replacing each native M by its upward-univ restriction M restricted to univ. The exact rank transport is Matroid.restrict_eRk_eq', which preserves every native rank used in the inequalities, while the native rank and base criteria reconstruct an actual base in the original ground from the zero-one point. Thus H yields a common base C of no greater w-cost.")),
                Paragraph(Text(
                    "The cost calculation is exact: if W is the repeated-edge walk sum of the signed arc weights, then cost(H) = weightSum(w,B) - W/(L + 1), with the division applying only to W. Since B was chosen to minimize the actual w-sum over all common bases, the integer sum on B is at most the integer sum on C, which is at most the linear w-cost of H, and the positive denominator forces W <= 0. This proves the closed-walk nonpositivity needed by the existing integer potential criterion without toggling a cycle or assuming a new exchange lemma.")),
                Paragraph(Text(
                    "The closed-walk criterion exists_isPotential_iff_forall_closedWalk_nonpos supplies a direct integer potential phi on all of E. Set c = phi and d = w - phi. On a true arc the potential inequality is c(b) <= c(e); on a false arc it is phi(e) + w(b) - w(e) <= phi(b), equivalently d(b) <= d(e). Applying the threshold local-to-global result to the two tags gives the same B as a global minimizer of c over every M1-base and of d over every M2-base: the actual finite c-sum on B is at most the c-sum on each M1-base, and the analogous d-sum inequality holds for every M2-base. Meanwhile c(e) + d(e) = w(e) pointwise for every e in the ambient E.")),
                Paragraph(Text(
                    "The construction includes empty E, empty or proper native grounds, empty common bases, rank zero, loops, coloops, and tied, negative, zero, or otherwise arbitrary integer weights whenever the common-base premise is met. It supplies the optimum and the split internally and makes no algorithm or complexity claim. Frank, A Weighted Matroid Intersection Algorithm, Journal of Algorithms 2 (1981), 328-336, gives the integral splitting for fixed-cardinality common independent sets (https://www.cs.elte.hu/~frank/cikkek/FrankJ6.PDF). Frank, Connections in Combinatorial Optimization, the author-posted corrected OUP proof, Theorem 13.2.4 and Corollary 13.2.6, pp. 424-425, explicitly treat common bases (https://www.cs.elte.hu/~frank/cikkek/FrankB1.pdf); those sources use maximum weights, and negating weights gives the minimum convention here. The paragraphs above record this reuse and application derivation from the existing compiled suppliers, rather than a newly admitted theorem or an originality claim."))),
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
