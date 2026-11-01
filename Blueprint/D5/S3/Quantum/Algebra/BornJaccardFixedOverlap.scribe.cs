using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class BornJaccardFixedOverlapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact Born interval defect maximum at prescribed overlap is attained for every allowed overlap.",
        H("Born interval fixed-overlap maximum"),
        Blocks(Describe.Lean(
            DescribeId.Create("born-jaccard-fixed-overlap-maximum"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/BornJaccardFixedOverlap.fixed_overlap_maximum"),
            H("Exact maximum over all actual line pairs"),
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
                Paragraph(Text("Write Defects(rho,c,R,T,r) for the set of real d for which "
                    + "there are ordered complex lines L,N in T, both of dimension one, and "
                    + "unit vectors u in L and v in N with absolute inner product r, such "
                    + "that d is the original interval distance defect at R+map(L), R+T, "
                    + "R+map(N). IsGreatest says both that the displayed value belongs to "
                    + "this set and that every member is at most that value. Thus the "
                    + "statement includes every ordered line pair and simultaneous attainment.")),
                Paragraph(Text("For an arbitrary unit pair with eigenbasis coordinates (a,b) "
                    + "and (z,w), the residual-square identity bounds normSq(a)+normSq(z)-1 "
                    + "by the norm of conj(a)z+conj(b)w. The latter is exactly the prescribed "
                    + "overlap. Spectral expansion makes the numerator of the actual defect "
                    + "equal (M-m)(normSq(a)+normSq(z)-1). Multiplication by M-m and division "
                    + "by the derived positive denominator give the universal upper bound.")),
                Paragraph(Text("For every U contained in T, the actual orthogonal projection "
                    + "onto R+U is the sum of the projections onto R and U. Cyclicity of "
                    + "the trace identifies mu(T) with the real trace of the compression; "
                    + "the inner-product compression identity identifies its quadratic "
                    + "forms with those of rho. The actual interval meet and join therefore "
                    + "give defect (mu(L)+mu(N)-mu(T))/(c+mu(R)+mu(T)). This proves the fixed-overlap maximum in Theorem 2.1 of Born-weighted "
                    + "Jaccard projection geometry. The cases r=0, M=m, and c+mu(R)=0 remain "
                    + "included. This is a repository derivation, with no originality claim."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Statement()
    {
        var n = F.Id("n"); var rho = F.Id("rho"); var c = F.Id("c");
        var R = F.Id("R"); var T = F.Id("T"); var r = F.Id("r");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        var space = new Formula.Power(complex, n);
        var subs = Call("Sub", space);
        var zero = D(0); var one = D(1);
        var M = Call("lam", rho, T, zero); var m = Call("lam", rho, T, one);
        var s = Seq(M, Plus, m);
        var den = Seq(c, Plus, Call("mu", rho, R), Plus, Par(s));
        var body = Call("IsGreatest", Call("Defects", rho, c, R, T, r),
            new Formula.Fraction(Seq(r, Par(Seq(M, Minus, m))), den));
        var assumptions = And(Le(D(2), n),
            And(Call("PosDef", rho), And(Eqn(Call("Tr", rho), one),
                And(Le(zero, c), And(Le(T, Call("orthogonal", R)),
                    And(Eqn(Call("dim", T), D(2)), And(Le(zero, r), Lt(r, one))))))));
        return All("n", naturals, All("rho", Call("Matrix", n, n, complex),
            All("c", reals, All("R", subs, All("T", subs,
                All("r", reals, Imp(assumptions, body)))))));
    }
}
