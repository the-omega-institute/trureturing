using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.IntervalReconstruction;

internal sealed class MonotoneIntervalStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform stability for complete inclusive interval observations of monotone real tuples.",
        H("Uniform noisy interval recovery"),
        Blocks(Describe.Lean(DescribeId.Create("monotone-interval-stability"),
            DeclarationHandle.Create("D5/S3/Combinatorics/IntervalReconstruction/MonotoneIntervalStability.result"),
            H("A constant depending only on the length"),
            StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For n≥3, O(n) is the finite set of endpoint pairs (i,j) with "
                    + "0≤i<j<n. For a tuple a:Fin(n)→Real, S(a,(i,j)) is the sum of a(r) "
                    + "over every i≤r≤j, including both endpoints. It is exactly "
                    + "Omega.MonotoneIntervalReconstruction.intervalSum applied to the tuple "
                    + "extended by zero outside Fin(n); no outside value occurs in these sums. "
                    + "Nonnegative(a) means every coordinate is nonnegative, and Monotone(a) "
                    + "means a(i)≤a(j) whenever i≤j. Perm(O(n)) consists of all bijections of "
                    + "the actual endpoint occurrences. Equal interval sums remain distinct "
                    + "occurrences. Singletons are omitted.")),
                Paragraph(Text("Fix a permutation π. On the vector space of pairs (a,b), impose "
                    + "the homogeneous linear inequalities expressing nonnegativity and "
                    + "monotonicity of both tuples, together with both signs of every linear "
                    + "difference S(a,p)−S(b,π(p)). Their common cone therefore consists "
                    + "exactly of monotone nonnegative pairs with exact matched observations. "
                    + "A noisy pair violates every defining inequality by at most ε. "
                    + "The homogeneous Hoffman bound supplies a point (a′,b′) of this cone "
                    + "whose displacement, measured by each coordinate-difference functional "
                    + "(x,y)↦x(i)−y(i), is at most C(π)ε.")),
                Paragraph(Text("The occurrence bijection gives equality of the actual observation "
                    + "multisets for a′ and b′, with all multiplicities. The existing exact "
                    + "reconstruction theorem gives a′=b′. Consequently the same bound controls "
                    + "|a(i)−b(i)|. There are finitely many permutations of O(n). Choose the "
                    + "nonnegative constant C as the sum of their constants C(π); it dominates "
                    + "every one of them and is chosen before a, b, ε and π. This proves the "
                    + "displayed statement for all n≥3.")),
                Paragraph(Text("The general homogeneous error-bound proof is due to the Tau Ceti "
                    + "contributors, TauCeti commit 557dcf0fc5cc930bb3dd80a7f1aff6d8f2288647, "
                    + "Geometry/Convex/Cone/ErrorBound.lean, under Apache License 2.0. It uses "
                    + "field-level Tucker alternatives and a pseudo-inverse of a linear map. "
                    + "The local mathematical declarations are in OmegaMath.Geometry.Convex.Cone.ErrorBound "
                    + "and OmegaMath.Combinatorics.MonotoneIntervalStability. The source attribution "
                    + "and complete license are in licenses/TauCeti.md and "
                    + "docs/reports/TauCeti-Apache-2.0.txt. Exact reconstruction is supplied by "
                    + "Omega.MonotoneIntervalReconstruction.reconstruct. Hoffman's classical source "
                    + "is On approximate solutions of systems of linear inequalities, Journal of "
                    + "Research of the National Bureau of Standards 49, 263–265.")),
                Paragraph(Text("All-zero tuples, repeated coordinates, tied sums and zero noise "
                    + "are included. No strictness, separation, integrality, magnitude bound, "
                    + "genericity or compatibility of matched endpoints is assumed. The result "
                    + "asserts existence of a finite real constant; it supplies no optimal "
                    + "constant, efficient reconstruction algorithm or solution of general Turnpike."))),
            DescribeRole.Theorem))));

    private static Formula V(string s) => FormulaDsl.Id(s);
    private static Formula Call(string s, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) =>
        Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, b);
    private static Formula Ex(string s, Formula t, Formula b) =>
        Seq(Exists, Sp, V(s), Colon, Sp, t, Comma, Sp, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Abs(Formula a) => Seq(Lvert, a, Rvert);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Statement()
    {
        var n = V("n"); var c = V("C"); var a = V("a"); var b = V("b");
        var eps = V("epsilon"); var pi = V("pi"); var p = V("p"); var i = V("i");
        var real = V("Real"); var fin = Call("Fin", n);
        var tuple = new Formula.TypeArrow(fin, real);
        var observations = Call("O", n);
        return All("n", V("Nat"), Imp(Le(D(3), n),
            Ex("C", real, And(Le(D(0), c),
            All("a", tuple, All("b", tuple,
            Imp(Call("Nonnegative", a), Imp(Call("Nonnegative", b),
            Imp(Call("Monotone", a), Imp(Call("Monotone", b),
            All("epsilon", real, Imp(Le(D(0), eps),
            All("pi", Call("Perm", observations),
            Imp(All("p", observations, Le(Abs(Sub(Call("S", a, p), Call("S", b, Call("apply", pi, p)))), eps)),
                All("i", fin, Le(Abs(Sub(Call("apply", a, i), Call("apply", b, i))), Mul(c, eps))))))))))))))));
    }
}
