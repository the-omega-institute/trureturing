using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class NormalModulusTriangleConstantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/bourinlee2026symmetricmodulus");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Hermitian pair in dimension two rules out every normal-modulus triangle constant below one quarter.",
        H("The normal-modulus triangle constant in dimension two"),
        Blocks(
            SourceQuotation(),
            Entry("modulus", "IsModulus", "Positive modulus", Modulus(),
                "For complex 2×2 matrices X and P, IsModulus X P requires P to be positive semidefinite "
                + "and P²=X*X. Here X* is the conjugate transpose. The characterization “the positive square "
                + "root is unique” is quoted; the fixed-pair proof checks both conditions for each explicit P.",
                DescribeRole.Definition, true),
            Entry("normal", "IsNormalMatrix", "Normal matrices", Normal(),
                "IsNormalMatrix X means X*X=XX*. The witness matrices are Hermitian and therefore normal.",
                DescribeRole.Definition, true),
            Entry("constant-claim", "claim", "A constant smaller than one quarter", Claim(),
                "The claim asserts the existence of a real c<1/4 working for every normal complex 2×2 pair A,B. "
                + "For every PA,PB,PS satisfying IsModulus A PA, IsModulus B PB, and IsModulus (A+B) PS, "
                + "there must be a unitary V making PA+PB+cV(PA+PB)V*−PS positive semidefinite. "
                + "The real c is cast to a complex scalar. This is the smaller-constant assertion associated "
                + "with the question following Corollary 4.2; the source's upper bound at c=1/4 is not formalized here.",
                DescribeRole.Definition, false),
            Entry("refutation", "result", "Every smaller constant fails", Disp(Seq(Neg, Sp, V("claim"))),
                "Take A=diag(1,0), M=(1/25)[[9,−12],[−12,16]], and B=−M. "
                + "The matrix M is the projection onto (3,−4)/5. The lemmas modulus_A, modulus_M, and modulus_PS "
                + "give PA=A, PB=M, and PS=(4/5)I. Put D=A+M and x=(1,2). The lemmas d_pos, d_quad, "
                + "ps_quad, and d_upper give D≥0, x*Dx=2, x*PSx=4, and D≤(8/5)I. "
                + "The identity conjugation_quad holds for every matrix V. For unitary V, it and the conjugated positivity certificates give "
                + "0≤q=x*VDV*x≤8. The asserted inequality requires 4≤2+cq. If c≥0, this yields "
                + "4≤2+8c and c≥1/4; if c<0, it yields 4≤2. Both contradict c<1/4. "
                + "Thus the displayed Hermitian pair defeats every unitary for every smaller real constant. "
                + "Together with the source's Corollary 4.2, the lower bound gives the attained best constant "
                + "1/4 in dimension two; that upper bound is a source consequence rather than a theorem of this module. "
                + "As exact mathematical reasoning, A+B=(1/25)[[16,12],[12,−16]] is of reflection type, "
                + "with scalar modulus (4/5)I, whereas D has eigenvalues 2/5 and 8/5. The ratio "
                + "((4/5)−(2/5))/(8/5)=1/4 also governs the Schur version (4.1); that comparison is not formalized. "
                + "Sharpness in Theorem 4.1 for other positive maps between small dimensions and the classification "
                + "of equality cases are not settled by this result. The journal version's text is ASSUMED-UNVERIFIED; "
                + "the quotations refer to arXiv:2602.19607v1, §4.",
                DescribeRole.Theorem, false),
            Paragraph(Text(
                "For the arbitrary rank-one application, let n≥2 and retain the same ordered pair of nonzero "
                + "rank-one normal matrices A,B in Mₙ(ℂ), the right modulus |X|=sqrt(X*X), and D=|A|+|B|. "
                + "Define S(A,B)={c≥0 : there is U∈U(n) with D+cUDU*−|A+B| positive semidefinite}. "
                + "The group here is the full ambient unitary group, including transformations mixing the joint range "
                + "with its orthogonal complement.")),
            Paragraph(Text(
                "The normal spectral diagonalization Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal "
                + "and rank of a diagonal matrix give A=αP and B=βQ, with α,β≠0 and rank-one orthogonal "
                + "projections P,Q. Set a=|α|, b=|β|, ξ=a/α and ω=ξβ/b. Then a,b>0, |ξ|=|ω|=1, "
                + "ξA=aP and ξB=bωQ. The single multiplier ξ preserves each right modulus, including that of "
                + "A+B, since (ξX)*(ξX)=X*X. The positive-square-root uniqueness CFC.sqrt_unique applied to "
                + "(αP)*(αP)=a²P gives |A|=aP and likewise |B|=bQ, hence D=aP+bQ. "
                + "This correspondence preserves the actual relative phase and the actual feasible set S(A,B).")),
            Paragraph(Text(
                "For a rank-one projection P=uu* with u*u=1, PureStateHandshake.pure_state_handshake "
                + "gives PXP=tr(PX)P. Applying this to Q, and to the positive projections Q and I−Q, "
                + "shows 0≤tr(PQ)≤1. Thus r=sqrt(tr(PQ)) is real with 0≤r≤1. If r=0, the identity "
                + "tr((QP)*(QP))=tr(PQ)=0 gives QP=PQ=0. Consequently the right squared modulus of "
                + "aP+bωQ is a²P+b²Q=D², and |A+B|=D. If r=1, the trace of "
                + "(P−Q)*(P−Q) is 2−2tr(PQ)=0, so P=Q and |A+B|=|a+bω|P≤(a+b)P=D. "
                + "If ω=1, the normalized sum aP+bQ is positive semidefinite and again |A+B|=D. "
                + "In each of these three cases 0 belongs to S(A,B), is its least element, and equals its infimum. "
                + "The coincident-projection argument includes a+bω=0; none of these cases divides by an interior parameter.")),
            Paragraph(Text(
                "For 0<r<1 and ω≠1, set s=a+b, z=(a−b)/s, q=4ab/s², η=(1−Re ω)/2, "
                + "x=sqrt(1−q(1−r²)), y=sqrt(1−qr²η), x₀=sqrt(1−y²), and "
                + "W=z²+qr²(1−η). Then q=1−z², 0<q≤1, and 0<η≤1. The latter strict inequality "
                + "uses |ω|=1: Re ω=1 would force Im ω=0 and ω=1. Since qr²η≤r²<1, "
                + "one has 0<y<1; likewise 0<x<1, 0<x₀<1, x₀=sqrt(q)r sqrt(η), and "
                + "W=x²−x₀²≥0, hence x₀≤x. These bounds include a=b and η=1, with W allowed to vanish. "
                + "They justify the interior divisions by y, x₀ and x+x₀ while leaving the boundary arguments independent.")),
            Paragraph(Text(
                "The projection relations also give an ambient projection formula. "
                + "For t=tr(PQ)=r²<1, put R=(P+Q−PQ−QP)/(1−t). The sandwich identities "
                + "PQP=tP and QPQ=tQ imply R*=R, R²=R, RP=P and RQ=Q. "
                + "Therefore R is positive semidefinite; cyclicity of trace and tr(P)=tr(Q)=1 give tr(R)=2. "
                + "All these identities concern matrices on the full ambient space.")),
            Paragraph(Text(
                "The ambient lower-bound argument also applies independently of a two-dimensional reduction. "
                + "Let K=|A+B|−D, let e be a unit vector with Ke=ke, and suppose D≤LI. For every ambient "
                + "unitary U, conjugation gives UDU*≤LI. If c≥0 is feasible, adding the positive matrices "
                + "c(LI−UDU*) and cUDU*−K gives cLI−K≥0. Its quadratic form at e is cL−k≥0. "
                + "Thus every such U forces k≤cL; when L>0 and k>0, every c<k/L fails. "
                + "No invariance of the joint range under U is needed for this implication.")),
            Paragraph(Text(
                "For real parameters 0≤x<1 and 0<y<1, put "
                + "C=(sqrt((1−y)²+2(1−x²)(1−y)/y)−(1−y))/(1+x). "
                + "The radicand is strictly greater than (1−y)², so C>0. Squaring the defining equality "
                + "(1+x)C+(1−y)=sqrt((1−y)²+2(1−x²)(1−y)/y) gives "
                + "((1+x)/2)C²+(1−y)C−(1−x)(1−y)/y=0. If another positive d satisfies this equation, "
                + "subtracting the two equations factors as (d−C)(((1+x)/2)(d+C)+1−y)=0. "
                + "The second factor is positive, so d=C. This scalar identity requires a native spectral "
                + "identification before it can specify the optimum of S(A,B). The remaining interior obligations "
                + "are the right-modulus spectrum for this same pair, its positive defect eigenvalue, the attaining "
                + "ambient unitary, and the resulting exact coefficient and reverse zero-set implication.")))));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Bourin and Lee, Triangle inequalities for the operator symmetric modulus, arXiv:2602.19607v1, "
        + "§4, Corollary 4.2, verbatim: “Corollary 4.2. Let A, B ∈ Mn be normal. Then, for some unitary "
        + "V ∈ Mn, |A + B| ≤ |A| + |B| + (1/4) V(|A| + |B|)V*. If n ≥ 3, the constant 1/4 is the smallest "
        + "possible one.” The following paragraph asks verbatim: “However, contrarily to the Schur version "
        + "(4.1), it seems necessary to request n ≥ 3 in Corollary 4.2 to get sharpness of 1/4 "
        + "(what is the best constant for n = 2 ?).”"));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("bourin-lee-2026-normal-modulus-constant-n2"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Mat => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Complex);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Adj(Formula a) => Call("conjTranspose", a);
    private static Formula Pos(Formula a) => Call("PosSemidef", a);

    private static Formula Modulus() => Disp(All("X", Mat, All("P", Mat,
        Iff(Call("IsModulus", V("X"), V("P")),
            And(Pos(V("P")), Eq(Mul(V("P"), V("P")), Mul(Adj(V("X")), V("X"))))))));

    private static Formula Normal() => Disp(All("X", Mat,
        Iff(Call("IsNormalMatrix", V("X")),
            Eq(Mul(Adj(V("X")), V("X")), Mul(V("X"), Adj(V("X")))))));

    private static Formula Claim()
    {
        Formula sum = Add(V("PA"), V("PB"));
        Formula conjugate = Mul(Mul(V("V"), Parenthesized(sum)), Adj(V("V")));
        Formula correction = Seq(Call("ofReal", V("c")), Sp, Cdot, Sp, Parenthesized(conjugate));
        Formula conclusion = Ex("V", Mat, And(Call("memUnitaryGroup", V("V")),
            Pos(Sub(Add(sum, correction), V("PS")))));
        Formula moduli = All("PA", Mat, All("PB", Mat, All("PS", Mat,
            Imp(Call("IsModulus", V("A"), V("PA")),
                Imp(Call("IsModulus", V("B"), V("PB")),
                    Imp(Call("IsModulus", Add(V("A"), V("B")), V("PS")), conclusion))))));
        Formula pairs = All("A", Mat, All("B", Mat,
            Imp(Call("IsNormalMatrix", V("A")), Imp(Call("IsNormalMatrix", V("B")), moduli))));
        Formula bound = new Formula.Relation(V("c"), FormulaRelationOperator.LessThan,
            new Formula.Fraction(D(1), D(4)));
        return Disp(Iff(V("claim"), Ex("c", Real, And(bound, pairs))));
    }
}
