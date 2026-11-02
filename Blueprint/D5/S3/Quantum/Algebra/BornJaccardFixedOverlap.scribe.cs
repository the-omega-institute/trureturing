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
            DescribeRole.Theorem),
            Paragraph(Text("Coincident-line boundary (Proposition 3.2). Keep the same n, rho, c, R "
                + "and T throughout. Write S=R+T and E(L)=R+L, with orthogonal sums. "
                + "For y in T the actual compression is Ky=P(T)(rho y), and a(L) is "
                + "the real quadratic form of K on any unit generator of L. In the notation "
                + "of the theorem, M=lam(0), m=lam(1). Put"),
                Math(Disp(BoundaryParameters())),
                Text("Choose one orthonormal eigenbasis e,f of K with eigenvalues M,m, "
                + "once for the entire family, also when M=m. For any unit x in T, "
                + "compression_inner and compression_quadratic identify a(L) with "
                + "M times the squared modulus of its e coordinate plus m times that of "
                + "its f coordinate. Those squared moduli sum to one, so m<=a(L)<=M "
                + "and s-a(L)>=m>0.")),
            Paragraph(Text("For every line L in T, distance_properties gives the zero diagonal "
                + "and symmetry. Since E(L) is contained in S, the actual meet and join "
                + "in its distance to S are E(L) and S. The projection and weight identities "
                + "projection_orthogonal_sup, weight_orthogonal_sup and weight_unit_line give"),
                Math(Disp(CoincidentValue())),
                Text("Thus this statement covers every coincident pair, not just an eigenline. "
                + "The disjoint-line hypotheses of interval_inf and interval_defect hold only "
                + "for distinct lines and are not used at coincidence.")),
            Paragraph(Text("Use the actual simultaneous source family (2.7), with e and f fixed:"),
                Math(Disp(BoundaryFamily())),
                Text("For every 0<=r<1 both coefficients are positive, the vectors are unit "
                + "and their inner product is r. Their lines L(r) and N(r) are distinct, "
                + "have zero intersection, and span T. These are the explicit vectors in "
                + "pair_construction used by fixed_overlap_attainment; the choice of "
                + "eigenbasis does not depend on r. Merely choosing an unrelated maximizer "
                + "for each r would not identify this limiting line. For either "
                + "w(r)=u(r) or w(r)=v(r), orthonormality gives"),
                Math(Disp(VectorConvergence())),
                Text("The limits are taken through 0<=r<1 as r tends to one. The continuity "
                + "of Real.sqrt, scalar multiplication and addition gives these vector limits "
                + "in the ambient H, using the actual inclusion of T into H.")),
            Paragraph(Text("To identify the topology on lines, let Q(x,y) be the ambient rank-one "
                + "operator z maps to inner(y,z)x. P(L) denotes the ambient orthogonal "
                + "projector onto L. For a unit w, starProjection_unit_singleton and "
                + "InnerProductSpace.rankOne_apply identify P(C w) with Q(w,w). "
                + "Additivity and conjugate additivity in the two rankOne arguments, "
                + "the triangle inequality and InnerProductSpace.norm_rankOne give"),
                Math(Disp(ProjectorConvergence())),
                Text("Consequently both actual line projectors converge in operator norm "
                + "to P(C e). This proves convergence in the topology of ambient orthogonal "
                + "projectors, with the same M-eigenline for both families. Also "
                + "P(E(L(r)))=P(R)+P(L(r)) and likewise for N(r), so both interval "
                + "elements converge to E(C e) in this topology. The continuity inputs "
                + "are pinned Mathlib results: Mathlib/Analysis/Real/Sqrt.lean, "
                + "Mathlib/Topology/Algebra/Module/Basic.lean and "
                + "Mathlib/Topology/Algebra/Group/Basic.lean; the projector and rankOne "
                + "identities are in Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean "
                + "and Mathlib/Analysis/InnerProductSpace/LinearMap.lean. These references "
                + "use mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679.")),
            Paragraph(Text("For r<1 the explicit weights are "
                + "a(L(r))=a(N(r))=(s+r(M-m))/2. unit_pair_geometry and interval_defect "
                + "therefore compute the distinct-pair defect; fixed_overlap_maximum "
                + "identifies it as the maximum at that overlap. At r=1 both actual "
                + "lines are C e and a(C e)=M. The preceding coincident calculation gives"),
                Math(Disp(BoundaryJump())),
                Text("For every r<1 the meet of E(L(r)) and E(N(r)) is R and their join "
                + "is S. At r=1 the meet and join are both E(C e). Thus the distance "
                + "between the distinct endpoints is s/(b+s), while its actual coincident "
                + "value is zero. The two distances to S converge to m/(b+s). "
                + "The positive discrepancy s/(b+s) is exactly the meet-over-join change; "
                + "substituting r=1 into the distinct-line formula is invalid.")),
            Paragraph(Text("All denominators above remain positive when c=0, R=0 or b=0, "
                + "because m>0 and s=M+m. For n=2 the assumptions force R=0 and T=H, "
                + "and the same argument applies. When M=m the chosen basis is still "
                + "fixed, all distinct-pair defects are zero, and the coincident endpoint "
                + "is -2m/(b+2m)<0, with positive discrepancy 2m/(b+2m). No invariance "
                + "of T or R under rho is used: compression_inner, compression_symmetric "
                + "and native_matrix_faithfulness justify the compression and its positive "
                + "eigenvalues, while weight_nonneg gives b>=0. This is an application "
                + "of the existing results to the coherent source family, with no originality "
                + "claim. Singular densities and "
                + "infinite-dimensional spaces remain outside these assumptions.")))));

    private static Formula Fr(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Sq(Formula x) => new Formula.Power(Par(x), D(2));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert);
    private static Formula P(Formula x) => Call("P", x);
    private static Formula E(Formula x) => Call("E", x);
    private static Formula A(Formula x) => Call("a", x);
    private static Formula Diff(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula W() => Par(Seq(F.Id("b"), Plus, F.Id("s")));
    private static Formula Defect(Formula x, Formula y, Formula z) =>
        Seq(new Formula.Subscript(Delta, F.Id("c")), Par(Seq(x, Comma, y, Comma, z)));
    private static Formula BoundaryParameters() => new Formula.Aligned([
        Eqn(F.Id("b"), Seq(F.Id("c"), Plus, Call("mu", Rho, F.Id("R")))),
        Eqn(F.Id("s"), Seq(F.Id("M"), Plus, F.Id("m"))),
        Seq(D(0), F.Lt, F.Id("m"), Leq, Sp, F.Id("M"), Comma, Quad,
            D(0), F.Lt, Seq(F.Id("b"), Plus, F.Id("s")))]);
    private static Formula CoincidentValue()
    {
        var L = F.Id("L"); var S = F.Id("S");
        var beta = Fr(Diff(F.Id("s"), A(L)), W());
        return new Formula.Aligned([
            Eqn(Call("d", E(L), S), beta),
            Seq(Defect(E(L), S, E(L)), F.Eq, Minus, D(2), Call("d", E(L), S),
                F.Eq, Minus, Fr(Seq(D(2), Par(Diff(F.Id("s"), A(L)))), W()),
                F.Lt, D(0))]);
    }
    private static Formula BoundaryFamily() => new Formula.Aligned([
        Eqn(Alpha, Seq(Sqrt, Grp(Fr(Seq(D(1), Plus, F.Id("r")), D(2))))),
        Eqn(Beta, Seq(Sqrt, Grp(Fr(Diff(D(1), F.Id("r")), D(2))))),
        Eqn(Call("u", F.Id("r")), Seq(Alpha, Sp, F.Id("e"), Plus, Beta, Sp, F.Id("f"))),
        Eqn(Call("v", F.Id("r")), Seq(Alpha, Sp, F.Id("e"), Minus, Beta, Sp, F.Id("f"))),
        Eqn(Call("L", F.Id("r")), Seq(Mathbb, Grp(F.Id("C")), Call("u", F.Id("r")))),
        Eqn(Call("N", F.Id("r")), Seq(Mathbb, Grp(F.Id("C")), Call("v", F.Id("r"))))]);
    private static Formula VectorConvergence() => new Formula.Aligned([
        Seq(Alpha, To, D(1), Comma, Quad, Beta, To, D(0)),
        Seq(Sq(Norm(Diff(Call("w", F.Id("r")), F.Id("e")))), F.Eq,
            Sq(Diff(Alpha, D(1))), Plus, Sq(Beta), F.Eq,
            D(2), Par(Diff(D(1), Alpha)), To, D(0))]);
    private static Formula ProjectorConvergence()
    {
        var w = F.Id("w"); var e = F.Id("e");
        var cw = Seq(Mathbb, Grp(F.Id("C")), w);
        var ce = Seq(Mathbb, Grp(F.Id("C")), e);
        return new Formula.Aligned([
            Eqn(Diff(P(cw), P(ce)), Seq(Call("Q", Diff(w, e), w), Plus,
                Call("Q", e, Diff(w, e)))),
            Seq(Norm(Diff(P(cw), P(ce))), Leq,
                D(2), Norm(Diff(w, e)), To, D(0))]);
    }
    private static Formula BoundaryJump()
    {
        var eLine = Seq(Mathbb, Grp(F.Id("C")), F.Id("e"));
        var limit = Fr(Diff(F.Id("M"), F.Id("m")), W());
        var endpoint = Seq(Minus, Fr(Seq(D(2), F.Id("m")), W()));
        return new Formula.Aligned([
            Seq(Defect(E(Call("L", F.Id("r"))), F.Id("S"), E(Call("N", F.Id("r")))),
                F.Eq, Fr(Seq(F.Id("r"), Par(Diff(F.Id("M"), F.Id("m")))), W()), To, limit),
            Eqn(Defect(E(eLine), F.Id("S"), E(eLine)), endpoint),
            Seq(limit, Minus, Par(endpoint), F.Eq, Fr(F.Id("s"), W()), F.Gt, D(0))]);
    }


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
