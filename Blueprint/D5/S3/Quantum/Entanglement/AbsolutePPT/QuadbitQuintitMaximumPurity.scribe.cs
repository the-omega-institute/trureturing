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
    private static Formula LabelledDiagonal()
    {
        var entry=Call("Complex.ofReal",Call("l",Call("e",Id("p"))));
        return Call("diagonal",Parenthesized(Seq(Id("fun"),Parenthesized(Seq(Id("p"),Colon,J)),Mapsto,Sp,entry)));
    }
    public static Formula DiagonalNecessaryStatement()
    {
        var boundary=Call("cornerBoundaryValues",N,l);
        return All("m",Id("Nat"),All("n",Id("Nat"),Imp(And(Le(Int(3),Id("m")),Le(Int(3),Id("n"))),
            All("e",Call("Equiv",J,Fin(N)),All("l",Arrow(Fin(N),R),
                Imp(Call("APPT",LabelledDiagonal()),And(PSInt(Call("K1",boundary)),PSInt(Call("K2",boundary)))))))));
    }
    public static Formula DiagonalSpectralStatement()
    {
        var conclusion=And(Call("Antitone",l),All("i",Fin(N),Le(Int(0),Call("l",Id("i")))),
            Eq(Sum("i",Fin(N),Call("l",Id("i"))),Int(1)),Call("APPT",LabelledDiagonal()),
            Eq(Call("Complex.re",Trace(Mul(rho,rho))),Sum("i",Fin(N),Pow(Call("l",Id("i")),2))));
        var exists=Seq(Exists,Sp,Parenthesized(Seq(l,Colon,Arrow(Fin(N),R))),Comma,Sp,conclusion);
        return All("m",Id("Nat"),All("n",Id("Nat"),All("e",Call("Equiv",J,Fin(N)),
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
            Desc("diagonal_necessary_both","Both pencils for the actual labelled diagonal",CornerFormula.DiagonalNecessaryStatement(),
                "For arbitrary natural m,n at least three, every labelling e:(Fin m × Fin n) ≃ Fin(mn) and every real diagonal l, actual APPT of diag(l composed with e) implies positive semidefiniteness of both K1 and K2 on cornerBoundaryValues(mn,l). This selector is (l0,l1,l2,l_(mn−6),...,l_(mn−1)); its proof 9≤mn follows from the two dimension bounds and is suppressed in the display. There is no ordering, nonnegativity, normalization, strictness or distinctness premise. The proof packs a genuine three-by-three product corner and extends its Bell unitaries by the finite complement. Arbitrary labellings are related by global permutation unitaries, not by a claimed partial-transpose covariance. Both necessary pencils are retained; they do not give an APPT sufficiency theorem. This public source interface exposes the already used corner construction in the Hildebrand framework and is not a new discovery merely because it is public.",DescribeRole.Theorem),
            Desc("diagonal_spectral_reduction","One spectrum retaining its actual APPT diagonal",CornerFormula.DiagonalSpectralStatement(),
                "For every natural m,n, with no dimension lower bound, every supplied equivalence e:(Fin m × Fin n) ≃ Fin(mn), and every complex matrix rho on that product, assume rho is positive semidefinite, has trace one and is APPT after all global unitaries. There is one real l:Fin(mn)→R that is antitone, coordinatewise nonnegative, has total mass one, has an actual APPT labelled diagonal diag(l composed with e), and satisfies Re trace(rho*rho)=sum_i l_i^2. All five conclusion clauses refer to this single spectrum. Zero-dimensional products stay in the quantified domain; trace one then makes the premises infeasible rather than justifying a dimension restriction. Repeated and zero eigenvalues are included. The proof chooses sorted eigenvalues, diagonalizes rho by a global unitary and transports APPT back to that same diagonal. It does not sort again for the rank-four row. The original spectral_reduction telescope remains public and unchanged: at m,n≥3 it consumes this diagonal and diagonal_necessary_both to recover both K1 and K2. Standard spectral diagonalization and the earlier source interface are not claimed as new mathematics.",DescribeRole.Theorem),
            Desc("spectral_reduction","Necessary spectral matrices in arbitrary finite local dimensions",CornerFormula.SpectralStatement(),
                "For all natural m,n at least three, every positive semidefinite trace-one complex matrix on Fin m × Fin n satisfying literal APPT has an antitone nonnegative spectrum l of length mn and mass one. The proof argument 9≤mn is suppressed in the displayed cornerBoundaryValues selector. Both existing real matrices K1 and K2 evaluated on the nine extremal spectral coordinates are positive semidefinite, and Re trace(rho*rho) equals the sum of all mn spectral squares. Repeated and zero eigenvalues are included. Embed Fin 3 into each local factor. Their product c has a finite complement, identified with Fin(mn−9) by cardinality. Extend the Bell unitary and its swapped partner by identity on this complement. Partial transpose commutes with compression along this product: both entries at (i,j),(k,l) equal rho(c(i,l),c(k,j)). The existing Bell principal identity then gives the two necessary matrices. Ordered spectral diagonalization uses an arbitrary global packing only as a unitary conjugation; it assumes no partial-transpose covariance of that packing. These conditions are necessary and do not assert APPT sufficiency. At mn=24 the boundary equals QutritSpectralReduction.boundaryValues 5 and permits direct use of the existing dimension-24 sharp certificate. Hildebrand Theorem 2, PDF page 5 of quant-ph/0502170, already gives APPT 4×6→3×8 at fixed total dimension 24, so the qutrit maximum and established attaining ray imply the 4×6 scalar value. At total dimension twenty, the selector is SpectralBoundaryTransfer.boundaryValues 11. The length-twenty bound follows by the full rank-three insertion/deletion theorem from endpoint lengths eighteen and twenty-one, first reaching nineteen and then twenty. For the four-by-five product, the normalized coordinate ray (I+2|00><00|)/22 is exactly diagonal (3,1^19)/22. Its trace is one and its trace-square is (20+8)/22^2=7/121. For any global unitary U, the unit vector U|00> yields a separable numerator by LowRankRays.separableCone_one_add_two_rankOne; positive normalization and separableCone_partialTranspose_posSemidef imply APPT. At total dimension twenty-four, the same argument combined directly with QutritN8PurityBound.certificate_bound gives Re trace(rho^2)<=8/169 for every literal four-by-six APPT density. The coordinate ray (I+2|00><00|)/26 has diagonal (3,1^23)/26, is positive semidefinite with trace one, remains PPT after every global unitary, and has purity (24+8)/26^2=8/169. Thus the four-by-six real purity supremum is attained at 8/169. This known application uses the baseline-frozen qutrit bound at fixed total dimension and requires no extra spectral certificate. It is an application exposition, not an independently new four-by-six result. The varying-total-dimension inference for length twenty is the separate insertion/deletion argument. Neither application describes all maximizers or establishes an unrestricted APPT theorem. The four-by-five upper bound applies spectral_reduction to the density matrix and then applies the length-twenty insertion/deletion bound to that same ordered spectrum.",DescribeRole.Theorem),
            Paragraph(Text("An exact four-by-n application. For every natural n>=14 let J=Fin 4 × Fin n, N=4n, t=(3N+4)/8 in natural-number division, D=12n+2t and F(n)=(36n+16t)/D^2. Then D>0 and t=ceil(3n/2). A density is an actual complex J-by-J positive semidefinite matrix rho with complex trace exactly one. Partial transpose is on the second tensor factor, Gamma(M)[(i,j),(k,h)]=M[(i,h),(k,j)]. APPT means Gamma(U rho U*) is positive semidefinite for every global unitary U on J. Purity is Re tr(rho rho). The application gives purity at most F(n), an attained real sSup equal to F(n), and the explicit attaining state below. For even n the value is 4/(15n); for odd n it is (60n+8)/(15n+1)^2. The current evidence boundary for this application is stated below.")),
            Paragraph(Text("Use diagonal_spectral_reduction once with the row-major equivalence e(i,j)=j+n*i. It returns a single ordered nonnegative spectrum l of mass one, actual APPT of diag(l composed with e), and the purity equality. This arbitrary global labelling is not assumed to commute with partial transpose. On this same labelled diagonal, diagonal_necessary_both supplies the actual Bell pencils K1 and K2 on cornerBoundaryValues N l=(l_0,l_1,l_2,l_(N−6),...,l_(N−1)); uniform_rank_four_necessary supplies sum(top6)<=sum(bottom10). The four-by-four product-corner proof tests eta=sum_a |aa>; Gamma(|eta><eta|) is the swap, with six antisymmetric negative columns and ten symmetric or diagonal positive columns. Extend the spectral assignment and pair rotation by the actual finite complement and apply partial_transpose_trace_duality. Product compression commutes with Gamma. No eigenvalue simplicity, strict positivity or sufficiency of the necessary rows is used. Apply QuadbitUniformSpectralBound.actual_k1_l4_purity_bound at N=4n>=56 to this l, its order, nonnegativity, mass one, the rank-four row and the literal K1 matrix. Identifying the entries of K1 with its displayed spectrum matrix gives sum l_i^2<=(9N+16t)/(3N+2t)^2=F(n). The older three_row_scalar_bound at N>=67 remains a separate, unchanged theorem; it is not the source of the n>=14 threshold.")),
            Paragraph(Text("For attainment take the row-major coordinate projector P(p,p)=1 when e(p)<t and zero otherwise, with every off-diagonal entry zero. It is Hermitian and idempotent, has matrix rank t and complex trace t, and has exactly t supported coordinates and 4n−t complementary coordinates. Set rhoStar=(3I+2P)/D. Its t high diagonal entries are 5/D and its remaining 4n−t entries are 3/D. Positivity and trace one follow from P>=0, tr(P)=t and D=3N+2t; (3I+2P)^2=9I+16P gives purity F(n). For every global unitary U, Q=UPU* is Hermitian idempotent, so H=2Q−I is a unitary reflection and a contraction in Euclidean norm. ContractionBlocks.separableCone_scalar_add_of_opNorm_le_one at local dimension four makes 4I+H=3I+2Q separable. Positive real normalization and QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef prove Gamma(U rhoStar U*)>=0 for every U. The reflection application follows AhiableKothakondaWinterEq31. This proves actual APPT of an attaining density, rather than feasibility of only necessary spectral tests.")),
            Paragraph(Text("Let A_n={p in R | there exists a complex positive semidefinite trace-one rho on J with APPT(rho) and Re tr(rho rho)=p}. The coordinate density puts F(n) in A_n, and the universal upper bound makes A_n bounded above by F(n). Consequently its real supremum sSup A_n equals F(n) and is attained. Natural-number rounding gives 2t=3n for even n and 2t=3n+1 for odd n, giving both parity formulas above. This does not classify all maximizers.")),
            Paragraph(Text("The onset is least in the eventual sense: the assertion that this F(n) is the APPT maximum for every n above an integer threshold cannot start at 13 or earlier. At n=13, the published rank-one vertex rho13=(I+2|00><00|)/54 is the retained normalized coordinate ray. normalized_ray and normalized_basis_diagonal give positivity, trace one, APPT after all global unitaries and purity (52+8)/54^2=5/243. Here t=20 and F(13)=197/9604, with 5/243−197/9604=149/2333772>0. Thus even the proposed upper bound F(13) fails, while the n>=14 application gives the eventual threshold14. This comparison does not determine the maximum at13 or at any other dimension7 through13. The scalar N>=56 theorem is never applied at N=52.")),
            Paragraph(Text("Ahiable–Kothakonda–Winter, arXiv:2608.03390v2, Theorem6.3 and Corollary6.4, already give the inner-polytope optimum, the two-level spectrum (5^t,3^(4n−t))/D, its attainers and the transition n*=7+3sqrt(5), strictly between13 and14. Their rank-one vertex supplies the n13 witness just used. Conjecture6.7 concerns the unrestricted APPT upper bound; the formulas, attainers and transition are prior work. The prior exact rectangular theorem APPTReview.appt_rectangular_maximum_formula in mxym/math at commit 479acd5d6269faf94433ad6b694c5b7979027c69, formalizations/appt-high-dimensional-review/APPTReview/RectangularMaximum.lean, already gives the rounded physical maximum for m>=3 and n>=m^3−m−2, hence for m=4 and n>=58. Its mathematical result is cited and no external code is transplanted. The candidate additional universal APPT upper-bound range is14<=n<=57, subject to current closure, official acceptance and further literature comparison. This does not resolve general m, all finite four-row dimensions, all maximizers or equality of APPT and absolute-separability sets; global priority and uniqueness are not established.")),
            Paragraph(Text("Evidence distinction. The earlier n>=17 application compiled with an accepted scoped axiom closure containing only Classical.choice, Quot.sound and propext; that historical result and its closure evidence are preserved. Official CI has now compiled the physical suppliers, ContinuousSpectrumAssembly and the entire n>=14 application, including its final anonymous least-onset application. The scalar N>=56 theorem also has a separate selected successful build. The current full axiom/report closure, the four public supplier registration audits and final official acceptance remain pending. The scalar Reg square-nonnegativity repair and these Scribe/Reg source changes are uncompiled. Historical scalar audit issues #17891 and #17908 do not establish registration of the four supplier targets. These observations do not certify whole-library health or unique completion."), Text(" Sources: "), Ref("D5/L/QuantumStates/hildebrand2007pptspectra"), Text("; "), Ref("D5/L/QuantumStates/ahiablekothakondawinter2026geometry")),
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
            Paragraph(Text("A four-by-seven application. Let J = Fin 4 × Fin 7 and let rho be a complex J-by-J positive semidefinite matrix with trace one. Write Gamma for transpose on the second factor: Gamma(A)[(i,j),(k,h)] = A[(i,h),(k,j)]. Literal APPT means Gamma(V rho V*) is positive semidefinite for every global unitary V on J. Purity is Re tr(rho rho). The following calculation gives the attained maximum 1/25 for this set of actual density matrices.")),
            Paragraph(Text("Fix one decreasing spectrum l = (l_0,...,l_27), with l_i nonnegative, sum_i l_i = 1, and Re tr(rho rho) = sum_i l_i^2. More precisely, choose the ordered eigenvalues used in QutritHildebrandSufficiency.OrderedDiagonalization.sorted_diagonalization and a bijection e : J ≃ Fin 28. That theorem writes rho = V diag(l composed with e) V*. QutritSpectralReduction.appt_unconjugate makes this same labelled diagonal APPT. The construction in spectral_reduction uses these ordered eigenvalues and a particular product-corner packing. Any other e is related to that packing by a full coordinate permutation, itself an allowed global unitary. Trace and trace-square are preserved by QutritSpectralReduction.unitary_trace and unitary_purity_trace. Keep this one l and this actual APPT diagonal for every subsequent test; separately feasible spectra cannot be combined.")),
            Paragraph(Text("At total dimension 28 the boundary selector is (l_0,l_1,l_2,l_22,l_23,l_24,l_25,l_26,l_27). Denote QutritSpectralReduction.K1 of this vector by K_0 and K2 by K_1. Explicitly, K_0 = [2l_27,l_26-l_0,l_24-l_1; l_26-l_0,2l_25,l_23-l_2; l_24-l_1,l_23-l_2,2l_22] and K_1 = [2l_27,l_26-l_0,l_25-l_1; l_26-l_0,2l_24,l_23-l_2; l_25-l_1,l_23-l_2,2l_22]. Both are positive semidefinite. To see this on the fixed diagonal, embed a genuine three-by-three product corner and permute its entries to [l_27,l_26,l_24; l_0,l_25,l_23; l_1,l_2,l_22], with l_3,...,l_21 in the complement. This is QutritSpectralReduction.pack of the displayed boundary. Extend its bell unitary by identity on the complement; bell_pt_principal makes the partial-transpose principal matrix one half of K_0. The swap56 permutation interchanges the corner entries l_24 and l_25, and the same Bell test yields one half of K_1. Only product compression commutes with Gamma; a general packing is used as unitary conjugation, without an assumed partial-transpose covariance.")),
            Paragraph(Text("The same diagonal gives an additional rank-four test. In a four-by-four product corner let eta = sum_{a=0}^3 |aa> and let F|ab> = |ba>. Directly, Gamma(|eta><eta|) = F. The six vectors (|ab>-|ba>)/sqrt(2), a<b, are F-eigenvectors of eigenvalue -1; the six symmetric partners and four |aa> have eigenvalue +1. Assign l_0,...,l_5 to the six antisymmetric columns and l_18,...,l_27 to the ten other columns; assign l_6,...,l_17 to the twelve-dimensional complement. These assignments extend to a permutation of the full labelled diagonal, and the pair rotations extend to a global unitary. Finite permutation extension is the application of Equiv.Perm.exists_extending_pair; product-corner unitary extension is the construction already used in spectral_reduction.")),
            Paragraph(Text("Let A be the resulting conjugate of the labelled diagonal, and extend eta by zero outside the product corner. APPT and its quadratic test at eta give 0 <= eta* Gamma(A) eta = tr(Gamma(A)|eta><eta|) = tr(A Gamma(|eta><eta|)) = sum_{i=18}^{27} l_i - sum_{i=0}^{5} l_i. The middle equality is the entrywise trace-pairing identity for second-factor partial transpose, obtained by interchanging the two second-factor indices in the finite sum. Thus L := sum_{i=18}^{27} l_i - sum_{i=0}^{5} l_i is nonnegative jointly with K_0 and K_1 for this l. No eigenvalue simplicity or strict positivity is required. The two pencils together with L >= 0 are necessary conditions; their sufficiency for APPT is not asserted.")),
            Paragraph(Text("Here is an exact rational decomposition for the resulting purity estimate. All following indices start at zero. Set x_i = l_i-l_{i+1} for 0 <= i < 27 and x_27 = l_27; then x >= 0. Let y = (x_1,...,x_26,x_0-2x_27), v = (1,1,0)^T, and U = [1,0; -1,0; 0,1]. For s in {0,1}, put q_s = v^T K_s v, R_s = U^T K_s U, b_s = U^T K_s v, and S_s = q_s R_s - b_s b_s^T. Put T = q_0 R_1 + q_1 R_0 - b_0 b_1^T - b_1 b_0^T, and delta = 2637/1000000. The symmetric rational matrices P,H,B_si,C_s and vector w are specified completely below; no numerical approximation is intended.")),
            Paragraph(Text("For every real l of length 28, the polynomial identity is (sum_i l_i)^2/25 - sum_i l_i^2 = y^T P y + x^T H x + sum_{s=0}^1 sum_{i=0}^{27} x_i tr(B_si K_s) + L sum_{i=0}^{27} w_i x_i + delta(q_0+q_1)(tr(K_0)+tr(K_1)) + delta L(q_0+q_1) + tr(C_0 S_0) + tr(C_1 S_1) + tr(C_2 T). This is an equality before imposing ordering, normalization or positivity. Substituting the displayed matrices and l_i = sum_{j=i}^{27} x_j reduces both sides to the same quadratic polynomial over the rationals.")),
            Paragraph(Text("For the coefficient tables, an upper row of a symmetric d-by-d matrix at row i lists entries in columns i,...,d-1; the lower triangle is obtained by symmetry. A sextuple (a,b,c,d,e,f) means the symmetric three-by-three matrix [a,b,c; b,d,e; c,e,f]. These conventions specify every entry, including every zero. The following upper rows specify 1000000 P, a 27-by-27 matrix:")),
            Paragraph(Text("P upper row 0: (2637,-1,0,0,0,0,-1,0,0,0,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-2,-2,-3,-4,-3,0).")),
            Paragraph(Text("P upper row 1: (120997,-3479,-4080,-4596,-1521,870,1080,2069,3009,3939,4715,5286,5669,5881,5927,6006,7169,7736,7571,7179,-1949,6197,2885,1626,-4717,-1).")),
            Paragraph(Text("P upper row 2: (73730,-4334,-6206,-2035,720,1216,1959,2475,2871,3131,3282,3364,3388,3331,3226,3859,4395,4924,5514,-2332,2311,1020,252,-3429,0).")),
            Paragraph(Text("P upper row 3: (72210,-10463,-6468,-1268,561,1466,1586,1596,1588,1576,1577,1604,1651,1707,2351,2805,3480,4374,-5387,-1354,-1710,-2124,-4245,0).")),
            Paragraph(Text("P upper row 4: (98623,-13162,-6343,-2250,9,239,99,-14,-57,-21,127,422,827,1803,2138,2962,4354,-10214,-5953,-4681,-5842,-6402,0).")),
            Paragraph(Text("P upper row 5: (99179,-6532,-5736,-1904,522,1341,1425,1354,1327,1398,1603,1943,2802,3101,3616,4404,-7971,-3780,-3100,-4312,-5554,0).")),
            Paragraph(Text("P upper row 6: (105692,-6552,-4529,-513,2404,3457,3602,3543,3533,3646,3891,4529,4797,5131,5463,-4439,-1201,-1165,-2633,-5040,0).")),
            Paragraph(Text("P upper row 7: (106239,-6848,-4853,-608,2461,3526,3619,3524,3543,3740,4381,4607,4769,4735,-4915,-1820,-1856,-3132,-4844,0).")),
            Paragraph(Text("P upper row 8: (111519,-6603,-4436,36,3236,4294,4351,4288,4417,4939,5053,5031,4693,-4429,-1627,-1904,-3249,-4829,0).")),
            Paragraph(Text("P upper row 9: (120099,-6588,-4285,467,3852,4973,5115,5227,5575,5486,5255,4689,-4352,-1688,-2102,-3573,-5056,0).")),
            Paragraph(Text("P upper row 10: (130611,-6727,-4249,886,4595,5961,6381,6378,5925,5457,4749,-4222,-1914,-2444,-3973,-5261,0).")),
            Paragraph(Text("P upper row 11: (141491,-7068,-4321,1393,5720,7628,7139,6147,5464,4757,-4194,-2458,-3046,-4479,-5378,0).")),
            Paragraph(Text("P upper row 12: (151747,-7448,-4270,2525,8025,7473,5997,5218,4704,-4389,-3406,-3959,-5092,-5398,-1).")),
            Paragraph(Text("P upper row 13: (161006,-7335,-3285,5169,6445,5379,4790,4671,-4869,-4780,-5155,-5761,-5322,-1).")),
            Paragraph(Text("P upper row 14: (169553,-5706,-2507,2415,3960,4231,4759,-5710,-6540,-6528,-6380,-5155,-1).")),
            Paragraph(Text("P upper row 15: (176288,-8792,-4550,461,2959,4867,-7031,-8457,-7793,-6740,-4876,-1).")),
            Paragraph(Text("P upper row 16: (177491,-9829,-6813,-567,4622,-8791,-9983,-8330,-6529,-4407,-1).")),
            Paragraph(Text("P upper row 17: (157911,-5804,-1181,6020,-3177,-4597,-5074,-4646,-3793,0).")),
            Paragraph(Text("P upper row 18: (167005,-3957,3372,-3588,-4163,-5510,-4483,-3495,0).")),
            Paragraph(Text("P upper row 19: (187566,-3083,-9548,-7608,-8199,-4639,-3031,0).")),
            Paragraph(Text("P upper row 20: (213249,-24996,-13187,-11607,-4659,-2268,0).")),
            Paragraph(Text("P upper row 21: (238384,-20382,-11842,-8088,-4047,-1).")),
            Paragraph(Text("P upper row 22: (314987,-12920,-7693,-4112,-1).")),
            Paragraph(Text("P upper row 23: (362883,-8212,-2498,-2).")),
            Paragraph(Text("P upper row 24: (241851,-2719,-3).")),
            Paragraph(Text("P upper row 25: (97210,-2).")),
            Paragraph(Text("P upper row 26: (2637).")),
            Paragraph(Text("The following upper rows specify 2000000 H, a 28-by-28 matrix:")),
            Paragraph(Text("H upper row 0: (0,5276,59190,103213,117936,165009,300042,437770,527419,640394,755383,859064,949173,1026296,1092173,1149544,1201946,1257014,1481021,1583552,1596342,1588711,2234278,2644288,2493197,2169468,872631,0).")),
            Paragraph(Text("H upper row 1: (5274,1065509,1473284,1590097,1694262,1982476,2267350,2498946,2737652,2964444,3166924,3341900,3489040,3610062,3708858,3791528,3873292,4353601,4532292,4427903,4243726,4204309,3673480,2972759,2418756,1283387,5272).")),
            Paragraph(Text("H upper row 2: (237720,1301544,1553902,1750692,2185043,2611323,2982356,3344337,3681334,3981131,4239630,4455391,4629478,4765923,4872271,4970803,5675663,5902539,5633722,5219624,4920204,3797207,3058945,2540494,1476841,89050).")),
            Paragraph(Text("H upper row 3: (145612,972778,1412726,2016248,2594988,3109128,3593544,4037282,4431078,4771100,5055598,5284842,5461252,5589034,5683442,6191720,6228404,5928204,5521326,5007048,3706870,2950088,2361072,1372082,73936).")),
            Paragraph(Text("H upper row 4: (146878,1225142,2000379,2727417,3382570,3988605,4539028,5026527,5447576,5800297,6084258,6300251,6449053,6538647,6612993,6223319,5656564,5021994,4512208,3301815,2672303,2160614,1277793,73966).")),
            Paragraph(Text("H upper row 5: (217166,1395326,2272314,3066618,3791888,4447984,5028714,5530464,5951144,6289590,6544930,6714464,6798868,6618076,5981554,5327674,4644460,4159484,3079950,2554792,2106318,1297314,107534).")),
            Paragraph(Text("H upper row 6: (205234,1387282,2268180,3070304,3802008,4460820,5042176,5542912,5961484,6296978,6546692,6711226,6519305,5871492,5206867,4513498,4040101,2968420,2464671,2036552,1253879,97378).")),
            Paragraph(Text("H upper row 7: (213460,1400438,2286180,3094704,3829320,4488738,5069042,5567678,5983334,6313232,6557956,6373289,5732350,5074899,4389254,3915803,2859838,2383571,1981430,1223359,102232).")),
            Paragraph(Text("H upper row 8: (217346,1413308,2305874,3117834,3853220,4511684,5090016,5585842,5995928,6320748,6152396,5527862,4887076,4218484,3738812,2703278,2258194,1886170,1197060,115348).")),
            Paragraph(Text("H upper row 9: (226362,1439162,2335278,3147858,3882052,4538454,5113976,5604226,6009182,5879125,5292872,4690511,4060584,3592513,2592312,2175345,1831380,1189031,126858).")),
            Paragraph(Text("H upper row 10: (242314,1476138,2373056,3184146,3915894,4569288,5139128,5624118,5548516,5016776,4468940,3893576,3440592,2488582,2103462,1791842,1194310,144600).")),
            Paragraph(Text("H upper row 11: (262190,1518390,2414028,3222276,3950494,4597886,5162260,5154429,4690486,4210193,3702182,3262893,2372418,2025609,1752534,1210931,170880).")),
            Paragraph(Text("H upper row 12: (283478,1561190,2454214,3258422,3979892,4621290,4693940,4310584,3910230,3481726,3055780,2241372,1940224,1712306,1239816,206396).")),
            Paragraph(Text("H upper row 13: (304154,1601062,2490342,3286876,4001090,4165969,3875684,3567625,3230838,2820727,2098062,1850205,1673644,1282847,251252).")),
            Paragraph(Text("H upper row 14: (322672,1634990,2517014,3305320,3571988,3386328,3183334,2951202,2563152,1948444,1761078,1640764,1342600,305648).")),
            Paragraph(Text("H upper row 15: (336850,1657492,2536308,2916095,2845624,2761321,2648306,2293143,1802200,1681043,1619424,1422317,370126).")),
            Paragraph(Text("H upper row 16: (343628,1679002,2198921,2260290,2310305,2333302,2026075,1672554,1620287,1616180,1525393,445530).")),
            Paragraph(Text("H upper row 17: (351650,1419185,1649036,1856047,2036974,1792213,1581298,1593127,1639140,1652769,531392).")),
            Paragraph(Text("H upper row 18: (308270,1395865,1970145,2471892,2117231,1776987,1693462,1690714,1678860,555986).")),
            Paragraph(Text("H upper row 19: (327306,1609391,2428338,2061765,1767604,1684055,1703484,1784817,641348).")),
            Paragraph(Text("H upper row 20: (362882,1734982,1609946,1572605,1596325,1712778,1976069,786414).")),
            Paragraph(Text("H upper row 21: (411138,1112642,1383360,1522854,1735064,2200408,952132).")),
            Paragraph(Text("H upper row 22: (505934,1599271,1780151,1987172,2186669,703934).")),
            Paragraph(Text("H upper row 23: (616842,1640877,1906524,1903991,717936).")),
            Paragraph(Text("H upper row 24: (690570,1580366,1590964,599898).")),
            Paragraph(Text("H upper row 25: (465506,1213628,493322).")),
            Paragraph(Text("H upper row 26: (181148,349190).")),
            Paragraph(Text("H upper row 27: (0).")),
            Paragraph(Text("The 28 sextuples for 2000000 B_0,i, in increasing i from 0 to 27, are: (425439,425439,0,425439,0,0); (584946,496760,298742,430982,256014,159236); (427646,373362,147016,424338,147068,150006); (390948,343744,265278,393996,268648,270700); (223330,174548,131360,225518,134362,165334); (183018,109190,64234,185144,67460,142614); (161170,90606,55024,162500,58014,128736); (147392,83004,51974,146840,54498,129686); (135746,55780,50994,133410,52696,140674); (144982,51184,52974,141738,54468,153412); (165662,55732,56100,160968,57662,172892); (194242,61144,59172,186812,60872,199514); (230574,66008,61368,218794,63242,232500); (275628,70746,62186,257636,64244,270596); (330994,76690,61840,304844,63924,312452); (398862,86132,61578,362954,63154,356772); (482246,102678,64354,436140,64332,403164); (585546,133938,77948,531422,74932,455100); (753828,312904,280538,703654,282022,657710); (927110,428778,385892,883908,396930,809370); (1033538,422594,311596,999136,325350,756272); (1130992,388320,190146,1126134,198324,626270); (720510,-36312,-7128,750202,16330,229168); (842262,228556,70464,847896,-90894,291134); (786380,324408,-42636,712422,-32742,280818); (654900,200324,34976,256398,16634,189302); (410496,47620,54350,95638,11448,96014); (5300,5300,0,5300,0,0).")),
            Paragraph(Text("The 28 sextuples for 2000000 B_1,i, in increasing i from 0 to 27, are: (468830,468830,0,468830,0,0); (639514,543522,326868,471054,280116,173734); (447878,395736,154554,449678,156754,150858); (392156,348120,265600,402392,272918,269198); (222200,174512,130896,227400,135928,164374); (181964,108852,63838,186582,68240,141806); (160866,91106,54866,164204,58610,128356); (147110,83248,51872,147872,55128,129326); (136054,56442,51122,134134,53106,140376); (145366,52070,52930,142576,54644,153038); (165876,56618,55714,161984,57642,172416); (194296,61956,58510,187902,60678,199028); (230608,66710,60688,219670,62894,232168); (275788,71196,61992,257594,63758,270624); (331376,76574,62928,302538,63354,313046); (399492,84914,65026,356228,62608,358108); (483110,99542,71290,422030,63972,405410); (586754,127842,88884,506854,74790,458530); (760584,308172,291066,681408,277956,664676); (940488,422728,402956,847960,388358,820354); (1052910,409342,340898,923358,310912,770566); (1148160,364446,227448,995396,183786,638050); (718074,-34196,-3202,731384,14414,229086); (845784,213134,80546,797888,-85590,293106); (768324,146382,152590,313124,20332,308102); (677044,208190,36124,255952,16326,191006); (417856,51052,54208,97432,10440,97264); (5274,5274,0,5274,0,0).")),
            Paragraph(Text("The remaining coefficients are C_0 = [7617,29576;29576,178296]/1000000, C_1 = [4280,9757;9757,60584]/1000000, C_2 = [3916,7596;7596,47754]/1000000, and w = (0,2637,40181,91988,380063,488702,580065,653253,716932,758875,784768,797699,798190,786087,760642,720231,661459,576967,351132,132685,74497,55488,54035,79399,102430,80084,44096,0)/1000000.")),
            Paragraph(Text("The matrix P and the 52 interior matrices B_si, 1 <= i <= 26, have rational LDL^T factorizations with strictly positive pivots. One exact specification of the factorization for any of these matrices M is L_ii = 1, L_ij = 0 for j>i, d_i = M_ii - sum_{k<i} L_ik^2 d_k and L_ji = (M_ji - sum_{k<i} L_jk L_ik d_k)/d_i for j>i. All 27 pivots for P and all 156 interior B pivots are positive. The four endpoint matrices B_00,B_0,27,B_10,B_1,27 are respectively 425439 vv^T/2000000, 5300 vv^T/2000000, 468830 vv^T/2000000 and 2637 vv^T/1000000, so they are positive semidefinite without a nonzero pivot assumption. The two LDL pivots for C_0 are 7617/1000000 and 60417607/952125000; those for C_1 are 107/25000 and 164100471/4280000000; those for C_2 are 979/250000 and 16163181/489500000. Hence all three C_s are positive semidefinite. Every entry of H and w is nonnegative, and delta is positive. These are finite rational sign and factorization calculations; psd_of_rat_ldl in QutritSpectralReduction supplies their positive-semidefinite interpretation.")),
            Paragraph(Text("It remains to justify the two Schur terms without dividing by q_s. For any real positive semidefinite K, the symmetric bilinear form B(a,b) = a^T K b satisfies B(a,b)^2 <= B(a,a) B(b,b), including a zero pivot; this is LinearMap.BilinForm.apply_sq_le_of_symm with Matrix.toBilin' K. Test at a=v and b=Uz to obtain z^T S_s z >= 0. For the mixed term let d_s = (Uz)^T K_s(Uz) and c_s = v^T K_s(Uz). Then c_s^2 <= q_s d_s, and multiplication gives (c_0 c_1)^2 <= (q_0 d_1)(q_1 d_0). Apply two_mul_le_add_of_sq_le_mul with a=q_0 d_1, b=q_1 d_0 and r=c_0 c_1 to get z^T T z = q_0 d_1 + q_1 d_0 - 2c_0 c_1 >= 0. No sign assumption on c_s and no invertibility assumption is used.")),
            Paragraph(Text("Every summand in the decomposition is now nonnegative. The P term is a positive-semidefinite quadratic form; the H term is a sum of nonnegative coefficients times x_i x_j. For the B and C terms use nonnegativity of tr(AB) for real positive semidefinite matrices, supplied by RHLinalg.trace_mul_nonneg_of_posSemidef. The other terms use x >= 0, w >= 0, L >= 0, q_s >= 0 and nonnegative traces of K_s. Since sum_i l_i = 1, the identity yields sum_i l_i^2 <= 1/25, and therefore Re tr(rho rho) <= 1/25 for every literal four-by-seven APPT density matrix.")),
            Paragraph(Text("Attainment uses the retained normalized_ray and normalized_basis_diagonal at m=4, n=7 and v=|00>. They give rho_* = (I+2|00><00|)/30 = diag(3,1^27)/30. The numerator is I plus twice a rank-one projector. Its trace is 28+2 = 30 and its squared numerator is I+8|00><00|, with trace 28+8 = 36. Thus rho_* has trace one and purity 36/900 = 1/25. For every global unitary V, the vector V|00> is unit: LowRankRays.separableCone_one_add_two_rankOne makes I+2|V00><V00| separable, positive scaling preserves the separable cone, and QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef gives its positive second-factor partial transpose. This proves actual APPT of the attaining state, rather than feasibility of only the necessary relaxation.")),
            Paragraph(Text("Let A be the real attainable-purity set {p : there exists a complex positive semidefinite rho on J with tr(rho)=1, APPT(rho), and Re tr(rho rho)=p}. The explicit rho_* puts 1/25 in A; the universal bound makes 1/25 an upper bound. Hence max A = sSup A = 1/25. The identity makes no restriction on the number of distinct eigenvalues. At rho_* the gap coordinates have x_0 = 2x_27 and all x_1,...,x_26 zero, explaining the transverse coordinates; this does not classify all equality cases. A counterexample to the pencils with L omitted would concern only a necessary relaxation, not an APPT state.")),
            Paragraph(Text("The two spectral matrices have the Hildebrand Eq. (5), Corollary 4 origin recorded in the existing Hildebrand Library note. Their use here is necessary product-corner testing; total dimension 28 is not a three-by-integer product and is not obtained by the four-by-six to three-by-eight fixed-dimension transfer. The separable-ray source is Vidal–Tarrach, Robustness of entanglement, Eq. (41), printed page 15 (DOI 10.1103/PhysRevA.59.141). The construction and rational combination above are a project application of these retained results and the pinned bilinear and order inequalities."), Text(" Sources: "), Ref("D5/L/QuantumStates/hildebrand2007pptspectra"), Text("; "), Ref("D5/L/QuantumBounds/vidaltarrach1999robustness")),
            Paragraph(Text("Ahiable–Kothakonda–Winter, arXiv:2608.03390v2, Corollary 6.4 and Eq. (44), pages 26–27, give (mn+8)/(mn+2)^2 and the spectrum (3,1^(mn-1))/(mn+2) inside the inscribed APPT polytope when n<n*. At m=4, n* = 7+3 sqrt(5) > 7, so its value is 1/25. The calculation above establishes that value for the full actual APPT set in the single four-by-seven sector. Conjecture 6.7, page 29, quantifies over other local dimensions as well; neither that full conjecture, classification of maximizers, nor equality of APPT with absolute separability follows from this sector calculation."), Text(" Source: "), Ref("D5/L/QuantumStates/ahiablekothakondawinter2026geometry")),
            Desc("claim","Literal density-matrix extremum",Seq(X("claim"),Iff, Sp,Par(MaximumStatement())),
                "The three clauses assert the universal upper bound, the real supremum of the attainable purity set, and existence of the prescribed diagonal density. Every matrix is complex and indexed by Fin 4 times Fin 5. Positivity, trace one and APPT are actual matrix properties.",DescribeRole.Definition),
            Desc("result","Sharp literal four-by-five maximum",MaximumStatement(),
                "For every positive semidefinite trace-one complex four-by-five matrix that remains PPT after every global unitary, Re trace(rho*rho) is at most 7/121. spectral_reduction supplies a single antitone nonnegative spectrum of length twenty, with mass one, both rank-three boundary matrices positive semidefinite, and exactly the same purity. Its boundary selector agrees with SpectralBoundaryTransfer.boundaryValues 11. DimensionTwentySpectralPurityBound applies the same-delivery new full insertion/deletion transfer from lengths eighteen and twenty-one through length nineteen. The normalized coordinate ray at (0,0) is the literal diagonal (3,1^19)/22; its trace is one, its purity is (20+8)/22^2=7/121, and the generic ray argument proves APPT after every global unitary. The attained upper bound gives the real supremum. Zero and repeated eigenvalues are permitted in the upper bound. No characterization of all maximizers, other dimensions, or unrestricted APPT purity theorem follows.",DescribeRole.Theorem))));
    }
}
