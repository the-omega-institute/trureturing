using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class BornJaccardFixedOverlapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual positive compressions admit simultaneously prescribed overlap and exact interval defect.",
        H("Born interval fixed-overlap attainment"),
        Blocks(Describe.Lean(
            DescribeId.Create("born-jaccard-fixed-overlap-attainment"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/BornJaccardFixedOverlap.fixed_overlap_attainment"),
            H("Actual-line attainment for every overlap"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let n be at least two, rho a positive-definite Hermitian complex "
                    + "matrix of trace one, c a nonnegative real number, R any complex subspace, "
                    + "and T a two-dimensional subspace of the orthogonal complement of R. "
                    + "Neither R nor T must be invariant under rho. All weights and distances "
                    + "are those of BornJaccardTracialClassification, with this same rho. "
                    + "The operator K is the actual composition of inclusion of T, rho, and "
                    + "orthogonal projection onto T. Its sorted eigenvalues are M=lam(0) and "
                    + "m=lam(1). The theorem derives positivity, m at most M, the identity "
                    + "mu(T)=M+m, and positivity of c+mu(R)+M+m.")),
                Paragraph(Text("For every real r with 0 at most r and r strictly below one, "
                    + "there are unit vectors u,v in T with absolute inner product r. "
                    + "Their ambient lines are the images of their spans under the actual "
                    + "inclusion T into H. Both have dimension one, their intersection is "
                    + "zero, and their sum is T. The original meet-over-join distance defect "
                    + "at R+L, R+T, R+N equals r(M-m)/(c+mu(R)+M+m).")),
                Paragraph(Text("Choose an orthonormal eigenbasis e,f of the actual compression "
                    + "in decreasing eigenvalue order. Set a=sqrt((1+r)/2), b=sqrt((1-r)/2), "
                    + "u=ae+bf and v=ae-bf. Both a and b are strictly positive on the full "
                    + "allowed overlap domain. The two vectors have norm one and inner "
                    + "product exactly r. Their sum and difference recover e and f, while "
                    + "comparison of the e and f coordinates proves their spans disjoint. "
                    + "The two line weights are both (M+m+r(M-m))/2.")),
                Paragraph(Text("For every U contained in T, the actual orthogonal projection "
                    + "onto R+U is the sum of the projections onto R and U. Cyclicity of "
                    + "the trace identifies mu(T) with the real trace of the compression; "
                    + "the inner-product compression identity identifies its quadratic "
                    + "forms with those of rho. The actual interval meet and join therefore "
                    + "give defect (mu(L)+mu(N)-mu(T))/(c+mu(R)+mu(T)). This proves the "
                    + "attainment part of Theorem 2.1 of Born-weighted Jaccard projection "
                    + "geometry. The universal upper bound and hence maximality remain "
                    + "separate obligations. The cases r=0, M=m, and c+mu(R)=0 remain "
                    + "included. This is a repository derivation, with no originality claim."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Less, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Statement()
    {
        var n = F.Id("n"); var rho = F.Id("rho"); var c = F.Id("c");
        var R = F.Id("R"); var T = F.Id("T"); var r = F.Id("r");
        var u = F.Id("u"); var v = F.Id("v");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        var space = new Formula.Power(complex, n);
        var subs = Call("Sub", space);
        var zero = D(0); var one = D(1);
        var M = Call("lam", rho, T, zero); var m = Call("lam", rho, T, one);
        var L = Call("map", Call("span", u), Call("inclusion", T));
        var N = Call("map", Call("span", v), Call("inclusion", T));
        var s = Seq(M, Plus, m);
        var den = Seq(c, Plus, Call("mu", rho, R), Plus, Par(s));
        var lineFacts = And(Eqn(Call("dim", L), one),
            And(Eqn(Call("dim", N), one),
                And(Eqn(Call("meet", L, N), zero),
                    And(Eqn(Call("join", L, N), T),
                        Eqn(Call("Delta", rho, c, Call("join", R, L),
                            Call("join", R, T), Call("join", R, N)),
                            new Formula.Fraction(Seq(r, Par(Seq(M, Minus, m))), den))))));
        var witness = Some("u", T, Some("v", T,
            And(Eqn(Call("norm", u), one),
                And(Eqn(Call("norm", v), one),
                    And(Eqn(Call("norm", Call("inner", u, v)), r), lineFacts)))));
        var body = And(Lt(zero, m), And(Le(m, M),
            And(Eqn(Call("mu", rho, T), s), And(Lt(zero, den), witness))));
        var assumptions = And(Le(D(2), n),
            And(Call("PosDef", rho), And(Eqn(Call("Tr", rho), one),
                And(Le(zero, c), And(Le(T, Call("orthogonal", R)),
                    And(Eqn(Call("dim", T), D(2)), And(Le(zero, r), Lt(r, one))))))));
        return All("n", naturals, All("rho", Call("Matrix", n, n, complex),
            All("c", reals, All("R", subs, All("T", subs,
                All("r", reals, Imp(assumptions, body)))))));
    }
}
