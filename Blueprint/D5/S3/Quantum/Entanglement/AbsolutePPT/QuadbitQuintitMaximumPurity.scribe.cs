using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QuadbitQuintitMaximumPurityDocument : IScribeDocumentDefinition
{
    private static Formula D(long n) => Num(n);
    private static Formula X(string n) => F.Id(n);
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula C => Seq(Mathbb, Grp(X("C")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(n.Contains('.') ? Seq(X(n.Split('.')[0]), Dot, X(n.Split('.')[1])) : X(n), [..xs]);
    private static Formula All(string n, Formula t, Formula f) => Seq(Forall, Sp,Par(Seq(X(n), Colon, t)), Comma, Par(f));
    private static Formula Ex(string n, Formula t, Formula f) => Seq(Exists, Sp,Par(Seq(X(n), Colon, t)), Comma, Par(f));
    private static Formula And(params Formula[] xs) => Seq(xs.SelectMany((f,i) => i==0 ? new[]{Par(f)} : new[]{Land, Sp,Par(f)}).ToArray());
    private static Formula Eqn(Formula a, Formula b) => Seq(a, F.Eq, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp,b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Rightarrow, Sp,Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Cdot, Sp,b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Sq(Formula a) => new Formula.Power(Par(a),D(2));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a,Comma,b));
    private static Formula J(Formula m, Formula n) => Par(Seq(Fin(m),Times, Sp,Fin(n)));
    private static Formula Mat(Formula j) => Call("Matrix",j,j,C);
    private static Formula Trace(Formula a) => Call("trace",a);
    private static Formula Purity(Formula a) => Call("re",Trace(Mul(a,a)));
    private static Formula Density(Formula a) => And(Call("PosSemidef",a),Eqn(Trace(a),D(1)));
    private static Formula Max => Frac(D(7),D(121));
    private static Formula Diagonal(Formula j, Formula a, Formula denominator)
    {
        var entries=Seq(X("if"),Par(Eqn(X("i"),a)),X("then"),Frac(D(3),denominator),X("else"),Frac(D(1),denominator));
        return Call("diagonal",Par(Seq(X("fun"),Par(Seq(X("i"),Colon,j)),Mapsto, Sp,entries)));
    }
    private static Formula Ray(Formula v) => Call("normalizedRay",v);
    private static Formula Generic(Formula body) => All("m",X("Nat"),All("n",X("Nat"),body));
    private static Formula MN => Mul(X("m"),X("n"));
    private static Formula GJ => J(X("m"),X("n"));
    private static Formula Vector => Seq(GJ,To, Sp,C);
    private static Formula StateExists(Formula p, bool prescribed=false)
    {
        var rho=X("rho"); var j=J(D(4),D(5));
        var facts=And(Density(rho),Call("APPT",rho),Eqn(Purity(rho),p));
        if(prescribed) facts=And(Eqn(rho,Diagonal(j,Pair(D(0),D(0)),D(22))),facts);
        return Ex("rho",Mat(j),facts);
    }
    private static Formula MaximumStatement()
    {
        var rho=X("rho"); var p=X("p");
        var values=Seq(OpenBrace,p,Colon,R,Mid, Sp,StateExists(p),CloseBrace);
        return And(All("rho",Mat(J(D(4),D(5))),Imp(And(Density(rho),Call("APPT",rho)),Le(Purity(rho),Max))),
            Eqn(Call("sSup",values),Max),StateExists(Max,true));
    }
    private static DocumentBlock Desc(string n, string title, Formula f, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("appt-quadbit-quintit-"+n.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity."+n),
            H(title),StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),role);

    public DocumentDefinition Create()
    {
        var v=X("v"); var a=X("a"); var denominator=Add(MN,D(2));
        var numerator=Add(D(1),Mul(D(2),Call("vecMulVec",v,Call("star",v))));
        var unit=Eqn(Call("dotProduct",Call("star",v),v),D(1));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The maximum purity of a literal four-by-five APPT density matrix is 7/121.",
            H("Four-by-five APPT maximum purity"),Blocks(
            Desc("normalizedRay","Normalized rank-one ray",
                Generic(All("v",Vector,Eqn(Ray(v),Mul(Frac(D(1),denominator),Par(numerator))))),
                "For arbitrary natural local dimensions m,n and a complex vector v on their product, normalizedRay is (I+2|v><v|)/(mn+2). Scalar multiplication uses the real reciprocal embedded into the complex numbers.",DescribeRole.Definition),
            Desc("normalized_ray","Density normalization and universal APPT of the ray",
                Generic(All("v",Vector,Imp(unit,And(Density(Ray(v)),Call("APPT",Ray(v)),
                    Eqn(Purity(Ray(v)),Frac(Add(MN,D(8)),Sq(denominator))))))),
                "The sole vector hypothesis is star(v) dot v=1. The normalized matrix is positive semidefinite, has complex trace exactly one, is APPT, and has real trace-square (mn+8)/(mn+2)^2. APPT quantifies over every global unitary on the full product space, with partial transpose on the second factor. A unitary sends v to another unit vector. LowRankRays.separableCone_one_add_two_rankOne makes I+2|Uv><Uv| separable; positive scaling and separableCone_partialTranspose_posSemidef give positivity after partial transpose. The rank-one square identity gives the trace-square formula. Dimensions with no unit vector are included conditionally, without an existence assumption.",DescribeRole.Theorem),
            Desc("normalized_basis_diagonal","Diagonal representative of the ray",
                Generic(All("a",GJ,Eqn(Ray(Call("Pi.single",a,D(1))),Diagonal(GJ,a,denominator)))),
                "For every coordinate a the normalized ray of its coordinate vector is diagonal, with one entry 3/(mn+2) at a and all other entries 1/(mn+2). This follows entrywise, including every off-diagonal entry.",DescribeRole.Theorem),
            Desc("claim","Literal density-matrix extremum",Seq(X("claim"),Iff, Sp,Par(MaximumStatement())),
                "The three clauses assert the universal upper bound, the real supremum of the attainable purity set, and existence of the prescribed diagonal density. Every matrix is complex and indexed by Fin 4 times Fin 5. Positivity, trace one and APPT are actual matrix properties.",DescribeRole.Definition),
            Desc("result","Sharp literal four-by-five maximum",MaximumStatement(),
                "For every positive semidefinite trace-one complex four-by-five matrix that remains PPT after every global unitary, Re trace(rho*rho) is at most 7/121. FiniteBellCorner.spectral_reduction supplies a single antitone nonnegative spectrum of length twenty, with mass one, both rank-three boundary matrices positive semidefinite, and exactly the same purity. Its boundary selector agrees with SpectralBoundaryTransfer.boundaryValues 11. DimensionTwentySpectralPurityBound applies the full insertion/deletion transfer from lengths eighteen and twenty-one through length nineteen. The normalized coordinate ray at (0,0) is the literal diagonal (3,1^19)/22; its trace is one, its purity is (20+8)/22^2=7/121, and the generic ray argument proves APPT after every global unitary. The attained upper bound gives the real supremum. Zero and repeated eigenvalues are permitted in the upper bound. No characterization of all maximizers, other dimensions, or unrestricted APPT purity theorem follows.",DescribeRole.Theorem))));
    }
}
