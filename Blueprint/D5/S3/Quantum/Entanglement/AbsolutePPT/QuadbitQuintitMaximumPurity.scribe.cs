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
            H(title),StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/QuantumStates/hildebrand2007pptspectra")),
            Blocks(Paragraph(Text(prose))),role);

    private static class CornerFormula
    {
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(StrataLint.Scribe.DefinitionDsl.Num(-n)) : StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Id(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula C => Seq(Mathbb, Grp(Id("C")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(string owner, string name) => Seq(Id(owner), Dot, Id(name));
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(name.Contains('.') ? Qualified(name.Split('.')[0], name.Split('.')[1]) : Id(name), [.. xs]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Imp(Formula p, Formula q) => Seq(Parenthesized(p), Rightarrow, Sp, q);
    private static Formula And(params Formula[] items) => Seq(items.SelectMany((f,i) => i==0 ? new[] {Parenthesized(f)} : new[] {Land, Sp, Parenthesized(f)}).ToArray());
    private static Formula Eq(Formula x, Formula y) => Seq(x, F.Eq, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Leq, Sp, y);
    private static Formula Lt(Formula x, Formula y) => Seq(x, F.Lt, y);
    private static Formula Add(params Formula[] xs) => Seq(xs.SelectMany((f,i) => i==0 ? new[] {f} : new[] {Plus, f}).ToArray());
    private static Formula Mul(Formula x, Formula y) => Seq(x, Cdot, Sp, y);
    private static Formula Pow(Formula x, int n) => new Formula.Power(Parenthesized(x), Int(n));
    private static Formula Arrow(Formula x, Formula y) => Seq(x, To, Sp, y);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Prod(Formula x, Formula y) => Parenthesized(Seq(x, Times, Sp, y));
    private static Formula Matrix(Formula i, Formula j, Formula field) => Call("Matrix", i, j, field);
    private static Formula Sum(string j, Formula ty, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(Id(j), Colon, ty)), Sp, body);
    private static Formula PSInt(Formula m) => Call("Matrix.PosSemidef", m);
    private static Formula Trace(Formula m) => Call("Matrix.trace", m);
    private static Formula N => Mul(Id("m"),Id("n"));
    private static Formula J => Prod(Fin(Id("m")),Fin(Id("n")));
    private static Formula l => Id("l");
    private static Formula rho => Id("rho");
    public static Formula BoundaryStatement()
    {
        var q=Id("q"); var value=Call("val",q); var total=Id("N");
        var index=Seq(Id("if"),Sp,Lt(value,Int(3)),Sp,Id("then"),Sp,value,
            Sp,Id("else"),Sp,Add(Seq(total,Minus,Int(9)),value));
        return All("N",Id("Nat"),Imp(Le(Int(9),total),
            All("l",Arrow(Fin(total),R),All("q",Fin(Int(9)),
                Eq(Call("cornerBoundaryValues",total,l,q),
                    Call("l",Parenthesized(Seq(index,Colon,Fin(total)))))))));
    }
    private static Formula LabelledDiagonal() => Call("diagonal",
        Parenthesized(Seq(Id("fun"),Parenthesized(Seq(Id("p"),Colon,J)),Mapsto,Sp,
            Parenthesized(Seq(Call("l",Call("e",Id("p"))),Colon,C)))));
    private static Formula Packing => Call("Equiv",J,Fin(N));
    public static Formula DiagonalNecessaryStatement()
    {
        var boundary=Call("cornerBoundaryValues",N,l);
        return All("m",Id("Nat"),All("n",Id("Nat"),
            Imp(And(Le(Int(3),Id("m")),Le(Int(3),Id("n"))),
                All("e",Packing,All("l",Arrow(Fin(N),R),
                    Imp(Call("APPT",LabelledDiagonal()),
                        And(PSInt(Call("K1",boundary)),PSInt(Call("K2",boundary)))))))));
    }
    public static Formula DiagonalSpectralStatement()
    {
        var purity=Eq(Call("Complex.re",Trace(Mul(rho,rho))),
            Sum("i",Fin(N),Pow(Call("l",Id("i")),2)));
        var conclusion=And(Call("Antitone",l),All("i",Fin(N),Le(Int(0),Call("l",Id("i")))),
            Eq(Sum("i",Fin(N),Call("l",Id("i"))),Int(1)),Call("APPT",LabelledDiagonal()),purity);
        var exists=Seq(Exists,Sp,Parenthesized(Seq(l,Colon,Arrow(Fin(N),R))),Comma,Sp,conclusion);
        return All("m",Id("Nat"),All("n",Id("Nat"),All("e",Packing,
            All("rho",Matrix(J,J,C),Imp(And(PSInt(rho),Eq(Trace(rho),Int(1)),Call("APPT",rho)),exists)))));
    }
    public static Formula SpectralStatement()
    {
        var boundary=Call("cornerBoundaryValues",N,l);
        var purity=Eq(Call("Complex.re",Trace(Mul(rho,rho))),
            Sum("i",Fin(N),Pow(Call("l",Id("i")),2)));
        var conclusion=And(Call("Antitone",l),All("i",Fin(N),Le(Int(0),Call("l",Id("i")))),
            Eq(Sum("i",Fin(N),Call("l",Id("i"))),Int(1)),
            PSInt(Call("K1",boundary)),PSInt(Call("K2",boundary)),purity);
        var exists=Seq(Exists,Sp,Parenthesized(Seq(l,Colon,Arrow(Fin(N),R))),Comma,Sp,conclusion);
        return All("m",Id("Nat"),All("n",Id("Nat"),Imp(And(Le(Int(3),Id("m")),Le(Int(3),Id("n"))),
            All("rho",Matrix(J,J,C),Imp(And(PSInt(rho),Eq(Trace(rho),Int(1)),Call("APPT",rho)),exists)))));
    }
    }

    public DocumentDefinition Create()
    {
        var v=X("v"); var a=X("a"); var denominator=Add(MN,D(2));
        var numerator=Add(D(1),Mul(D(2),Call("vecMulVec",v,Call("star",v))));
        var unit=Eqn(Call("dotProduct",Call("star",v),v),D(1));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The maximum purity of a literal four-by-five APPT density matrix is 7/121.",
            H("Four-by-five APPT maximum purity"),Blocks(
            Desc("cornerBoundaryValues","Nine extremal spectral coordinates",CornerFormula.BoundaryStatement(),
                "For every total dimension N at least nine, the selector observes the top three and bottom six ordered coordinates. Its proof argument 9<=N is omitted from this display. At N=20 it is the same observation as SpectralBoundaryTransfer.boundaryValues 11.",DescribeRole.Definition),
            Desc("diagonal_necessary_both","Both pencils from one labelled APPT diagonal",CornerFormula.DiagonalNecessaryStatement(),
                "For arbitrary m,n>=3, any equivalence e from Fin m times Fin n to Fin(mn), and any real vector l, APPT of the diagonal with entries l(e(p)) forces both K1 and K2 on cornerBoundaryValues(mn,l) to be positive semidefinite. The proof argument 9<=mn is suppressed in the selector. No sorting, nonnegativity, trace or mass condition is assumed. Relabel the actual diagonal by the composite of the existing full packing and e inverse, then use the same finite-complement Bell construction. This is a global unitary relabelling before APPT is applied; no arbitrary packing is commuted through partial transpose.",DescribeRole.Theorem),
            Desc("diagonal_spectral_reduction","A sorted spectrum retaining its actual APPT diagonal",CornerFormula.DiagonalSpectralStatement(),
                "For all natural m,n, every supplied equivalence e, and every complex positive semidefinite trace-one APPT matrix rho on the product, there exists one antitone nonnegative real vector l of length mn with total mass one. Its actual diagonal with entries l(e(p)) is APPT, and Re trace(rho*rho) is the sum of the squares of l. There is no local-dimension lower bound; in zero total dimension the trace-one premise is impossible. Sorted Hermitian diagonalization is performed once, and unitary invariance gives the APPT diagonal, trace and trace-square. This retained diagonal allows both Bell-pencil necessity and the uniform rank-four mass test to use the same spectrum. The original spectral_reduction follows by applying diagonal_necessary_both to this diagonal. At local dimensions four and seven the two tests jointly supply the three hypotheses of the length-28 purity estimate.",DescribeRole.Theorem),
            Desc("spectral_reduction","Necessary spectral matrices in arbitrary finite local dimensions",CornerFormula.SpectralStatement(),
                "For all natural m,n at least three, every positive semidefinite trace-one complex matrix on Fin m × Fin n satisfying literal APPT has an antitone nonnegative spectrum l of length mn and mass one. The proof argument 9≤mn is suppressed in the displayed cornerBoundaryValues selector. Both existing real matrices K1 and K2 evaluated on the nine extremal spectral coordinates are positive semidefinite, and Re trace(rho*rho) equals the sum of all mn spectral squares. Repeated and zero eigenvalues are included. Embed Fin 3 into each local factor. Their product c has a finite complement, identified with Fin(mn−9) by cardinality. Extend the Bell unitary and its swapped partner by identity on this complement. Partial transpose commutes with compression along this product: both entries at (i,j),(k,l) equal rho(c(i,l),c(k,j)). The existing Bell principal identity then gives the two necessary matrices. Ordered spectral diagonalization uses an arbitrary global packing only as a unitary conjugation; it assumes no partial-transpose covariance of that packing. These conditions are necessary and do not assert APPT sufficiency. At mn=24 the boundary equals QutritSpectralReduction.boundaryValues 5 and permits direct use of the existing dimension-24 sharp certificate. Hildebrand Theorem 2, PDF page 5 of quant-ph/0502170, already gives APPT 4×6→3×8 at fixed total dimension 24, so the qutrit maximum and established attaining ray imply the 4×6 scalar value. At total dimension twenty, the selector is SpectralBoundaryTransfer.boundaryValues 11. The length-twenty bound follows by the full rank-three insertion/deletion theorem from endpoint lengths eighteen and twenty-one, first reaching nineteen and then twenty. For the four-by-five product, the normalized coordinate ray (I+2|00><00|)/22 is exactly diagonal (3,1^19)/22. Its trace is one and its trace-square is (20+8)/22^2=7/121. For any global unitary U, the unit vector U|00> yields a separable numerator by LowRankRays.separableCone_one_add_two_rankOne; positive normalization and separableCone_partialTranspose_posSemidef imply APPT. At total dimension twenty-four, the same argument combined directly with QutritN8PurityBound.certificate_bound gives Re trace(rho^2)<=8/169 for every literal four-by-six APPT density. The coordinate ray (I+2|00><00|)/26 has diagonal (3,1^23)/26, is positive semidefinite with trace one, remains PPT after every global unitary, and has purity (24+8)/26^2=8/169. Thus the four-by-six real purity supremum is attained at 8/169. This known application uses the baseline-frozen qutrit bound at fixed total dimension and requires no extra spectral certificate. It is an application exposition, not an independently new four-by-six result. The varying-total-dimension inference for length twenty is the separate insertion/deletion argument. Neither application describes all maximizers or establishes an unrestricted APPT theorem. The four-by-five upper bound applies spectral_reduction to the density matrix and then applies the length-twenty insertion/deletion bound to that same ordered spectrum.",DescribeRole.Theorem),
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
                "For every positive semidefinite trace-one complex four-by-five matrix that remains PPT after every global unitary, Re trace(rho*rho) is at most 7/121. spectral_reduction supplies a single antitone nonnegative spectrum of length twenty, with mass one, both rank-three boundary matrices positive semidefinite, and exactly the same purity. Its boundary selector agrees with SpectralBoundaryTransfer.boundaryValues 11. DimensionTwentySpectralPurityBound applies the same-delivery new full insertion/deletion transfer from lengths eighteen and twenty-one through length nineteen. The normalized coordinate ray at (0,0) is the literal diagonal (3,1^19)/22; its trace is one, its purity is (20+8)/22^2=7/121, and the generic ray argument proves APPT after every global unitary. The attained upper bound gives the real supremum. Zero and repeated eigenvalues are permitted in the upper bound. No characterization of all maximizers, other dimensions, or unrestricted APPT purity theorem follows.",DescribeRole.Theorem))));
    }
}
