using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class SixSupportLaplacianLowRootDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-support weighted quotient, its symmetric representative, and the sharp balanced spectral threshold.",
        H("Six-support quotient and balanced threshold"), Blocks(
            Paragraph(Text("The support order for C is 1,2,3,12,13,23. The public source is paper/core/body.tex in the-omega-institute/ideal-intersection-laplacian at commit b93becea662a746badeadba42fdc3d3eb3db9382. Its quotient and energy occur on lines 574–600 and 774–784; its balanced sharpness proposition occurs on lines 114–145. The matrix model and balanced statement are attributed to that source. The Lean proofs and this exposition are independently authored; no novelty or graph-integrality classification is asserted.")),
            Node("quotient", "The literal nonsymmetric quotient", "quotient", ABC(Eq(Q(), QuotientMatrix())),
                "Rows and columns have the stated original support order. Multiplying on the left by diag(a,b,c,ab,ac,bc) makes the matrix symmetric.", DescribeRole.Definition),
            Node("weights", "Support weights", "weights", ABC(Eq(W(), Vector(V("a"),V("b"),V("c"),Mul(V("a"),V("b")),Mul(V("a"),V("c")),Mul(V("b"),V("c"))))),
                "The final three weights are the pair-support class sizes.", DescribeRole.Definition),
            Node("permutation", "Paired-coordinate reversal", "supportPermutation", Eq(Call("supportPermutation"),Call("permutation",Vector(D(0),D(1),D(2),D(5),D(4),D(3)))),
                "This involution changes the support order to 1,2,3,23,13,12.", DescribeRole.Definition),
            Node("roots", "Square-root diagonal", "rootWeights", ABC(Eq(Roots(),Vector(Sqrt(V("a")),Sqrt(V("b")),Sqrt(V("c")),Mul(Sqrt(V("b")),Sqrt(V("c"))),Mul(Sqrt(V("a")),Sqrt(V("c"))),Mul(Sqrt(V("a")),Sqrt(V("b")))))),
                "All six entries are positive when a,b,c are positive. Their squares are the reordered support weights.", DescribeRole.Definition),
            Node("symmetric", "The symmetric representative", "symmetric", ABC(Eq(S(), SymmetricMatrix())),
                "The paired diagonal is a,b,c; each singleton is coupled to its complementary pair by minus sqrt(a)sqrt(b)sqrt(c), equal to minus sqrt(abc) at positive parameters.", DescribeRole.Definition),
            Node("transport", "Return to the actual quotient", "toQuotientVector", ABC(All("z",Vec(),All("i",FinSix(),Eq(App(Call("toQuotientVector",V("a"),V("b"),V("c"),V("z")),V("i")),
                Div(App(V("z"),PermInverse(V("i"))),App(Roots(),PermInverse(V("i")))))))),
                "The inverse coordinate permutation and positive inverse diagonal preserve nonzero vectors and transport the same real eigenvalue to C.", DescribeRole.Definition),
            Node("geometry", "Weighted energy, kernel and similarity", "quotient_geometry", ABC(PositiveABC(Geometry())),
                "The energy is a sum over the singleton triangle and the three complementary-pair edges. Positivity forces all six coordinates of a zero-kernel vector to agree. The symmetric form is also a sum of six real squares. The exact similarity and eigenvector transport concern C itself.", DescribeRole.Theorem),
            Node("small-second", "A negative plane at a small second weight", "small_second_negative_plane", SmallSecond(),
                "For positive a,b,c with a at most b and b at most three, put p=sqrt(a)sqrt(b)sqrt(c), A=b+c+bc, B=a+c+ac, and t=(A+B+sqrt(a)sqrt(b)+1)/p. The plane consists of (u,v,0,tu,tv,0) in reordered coordinates. Its first two coordinates make the parametrization injective. The two paired diagonal contributions are nonpositive, and the singleton cross term is controlled by the square of u+v. The quadratic form of the symmetric matrix minus three times the identity is strictly negative on every nonzero vector of this plane. No division by a−3 or b−3 occurs, so their equality boundaries are included.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("positive-real", "Low eigenvalue for every positive real triple", "positive_real_low_eigenvalue", ABC(Imp(Lt(D(0),V("a")),Imp(Le(V("a"),V("b")),Imp(Le(V("b"),V("c")),Ex("e",Real(),And(Lt(D(0),V("e")),Lt(V("e"),D(3)),Ex("z",Vec(),And(Ne(V("z"),D(0)),Eq(MulVec(Q(),V("z")),Smul(V("e"),V("z"))))))))))),
                "For balanced weights at least one, the proof directly consumes the balanced threshold theorem and its actual quotient eigenpair. For the remaining triples it uses three explicit negative planes for the symmetric matrix shifted by three. When b is at most three, the small-second plane applies. When a is at most three but b is greater than three, the paired b and c coordinates are eliminated and the positive singleton diagonal completes a square; this includes a equal to three. When a is greater than three, the source comparison matrix is nonpositive on vectors (x,sqrt(b)y,sqrt(c)y): its form is minus (b+c)/2 times (x+2sqrt(a)y) squared minus 3/(2a) times (2bc-a(b+c))x squared. Ordering makes the latter coefficient nonnegative, including equal parameters. The positive Schur correction makes the lifted plane strictly negative. This explicit plane is a repository synthesis of the source geometry. A vector in each plane is chosen orthogonal to the simple zero kernel. The real Hermitian spectral expansion then forces a positive eigenvalue below three. The proved similarity transports its nonzero real eigenvector to the actual nonsymmetric quotient C. No ordered-eigenvalue convention or unproved inertia count is assumed.", DescribeRole.Theorem),
            Node("low", "The balanced smaller root", "balancedLow", All("m",Real(),Eq(Low(V("m")),LowFormula(V("m")))),
                "The discriminant is strictly positive for m at least one.", DescribeRole.Definition),
            Node("balanced", "Balanced smallest positive eigenvalue and sharp threshold", "balanced_sharp_threshold", Balanced(),
                "The factorization gives zero, m squared plus m, and the two quadratic roots, each quadratic root counted twice. For q_m(x)=x squared minus (m squared plus 4m)x plus 3m squared, q_m(0)=3m squared is positive, q_m(m)=minus m cubed is negative, and q_m(3)=9−12m is negative when m is at least one. The smaller quadratic root lies between zero and m; the larger root exceeds m squared plus m. A nonzero real symmetric eigenvector is constructed and transported by the proved similarity to C. Rationalization gives the strict lower bound 3m/(m+4), while the upper bound is three. The lower bound tends to three, so squeezing proves the real limit and the positive-integer subsequence limit. For every K below three there is a positive integer m whose smallest positive quotient eigenvalue exceeds K; every other positive real quotient eigenvalue then also exceeds K. Thus no constant smaller than three bounds the smallest positive quotient eigenvalues uniformly. The positive-real theorem supplies the same uniform bound for unequal ordered weights; the integer consequence follows by specializing its parameters.", DescribeRole.Theorem),
            IntegerFiniteness())));

    private static DocumentBlock IntegerFiniteness()
    {
        Formula b=V("b"),u=V("u"),r=V("r"),t=V("t"),q=V("q"),a=V("A"),bb=V("B"),c=V("C");
        Formula d0=new Formula.Subscript(V("D"),Num(0)),tr=new Formula.Subscript(V("T"),r);
        Formula l0=new Formula.Subscript(V("L"),Num(0)),m0=new Formula.Subscript(V("M"),Num(0));
        Formula lr=new Formula.Subscript(V("L"),r),mr=new Formula.Subscript(V("M"),r),hr=new Formula.Subscript(V("H"),r);
        Formula f=Call("F",u,b),g=Call("G",u,b),qq=V("Q");
        return new DocumentBlock.Section(H("Integer points on the endpoint equality polynomial"),Blocks(
            Paragraph(Text("The equality-curve remark in paper/sections/endpoint-one-spectrum.tex, label rem:endpoint-one-equality-curve, at the same public revision b93becea662a746badeadba42fdc3d3eb3db9382 supplies the polynomial below. The scalar C in this section denotes its constant term in q, distinct from the quotient matrix above. We give an elementary arithmetic derivation of finiteness by applying the existing facts that a nonzero polynomial over the integers has finitely many roots, a finite union of finite sets is finite, and a set with finite projection and finite fibers is finite. These are supplied by Polynomial.finite_setOfPred_isRoot, Set.Finite.biUnion and Set.Finite.of_finite_fibers. The parameter domain is all integer pairs (a,b), with no positivity or spectral-ordering assumption.")),
            Equation(t,Mul(b,Add(b,Num(2)))),
            Equation(q,Mul(V("a"),Sub(t,V("a")))),
            Equation(a,Sub(Mul(Num(3),b),Num(1))),
            Equation(bb,Mul(b,Sub(Add(Pow(b,2),Mul(Num(4),b)),Num(1)))),
            Equation(c,Negate(Mul(Mul(Sub(Add(Pow(b,2),Mul(Num(2),b)),Num(1)),Sub(Add(Pow(b,2),Mul(Num(3),b)),Num(1))),Sub(Sum(Pow(b,3),Mul(Num(3),Pow(b,2)),Mul(Num(3),b)),Num(1))))),
            Equation(Call("G",V("a"),b),Sum(Mul(a,Pow(q,2)),Mul(bb,q),c)),
            Paragraph(Text("Let n=|b| be at least four. The triangle inequality gives |A|≥2n and |B|≤3n³. The three factors in |C| are bounded respectively by 2n², 2n² and 3n³, so |C|≤18n⁷. If G(a,b)=0 and x=|q|, then 2nx²≤3n³x+18n⁷. Were x>4n³, we would have 24n³x<6nx² and 144n⁷<9nx². Multiplying the preceding weak inequality by eight would then give 16nx²<15nx², a contradiction. Thus |q|≤4n³.")),
            Paragraph(Text("The involution a↦t−a preserves q and G. Choose u from a and t−a with |u|≤|t−u|, and put v=t−u. Since |b+2|≥n−2 and n≥4, n²≤2|t|≤2(|u|+|v|)≤4|v|. Multiplication by |u|, together with |uv|=|q|≤4n³, gives |u|n²≤16n³, hence |u|≤16n. The chosen pair (u,b) is still a solution. This choice preserves b and works for both signs of b; it is used only to bound the projection, so both original involution partners remain in the final set.")),
            Paragraph(Text("In the following identities write q=u(t−u). Define the auxiliary integer F and the following polynomials. All displayed polynomial identities hold over the integers without division.")),
            Equation(f,Sub(Sub(Sub(Mul(Num(9),Pow(u,2)),Mul(Num(3),u)),Mul(Num(3),Pow(b,2))),Mul(Num(13),b))),
            Equation(qq,Sum(Mul(Sub(Mul(Num(27),b),Num(9)),Pow(u,2)),Mul(Sum(Mul(Negate(Num(54)),Pow(b,3)),Mul(Negate(Num(90)),Pow(b,2)),Mul(Num(45),b),Negate(Num(3))),u),Mul(Num(27),Pow(b,5)),Mul(Num(99),Pow(b,4)),Mul(Num(54),Pow(b,3)),Mul(Negate(Num(66)),Pow(b,2)),Mul(Num(11),b),Negate(Num(1)))),
            Equation(l0,Mul(Mul(Num(3),Sub(Add(Mul(Num(3),Pow(b,2)),Mul(Num(6),b)),Num(1))),Sum(Mul(Negate(Num(21)),Pow(b,2)),Mul(Num(8),b),Num(1)))),
            Equation(m0,Sum(Mul(Negate(Num(333)),Pow(b,5)),Mul(Negate(Num(1197)),Pow(b,4)),Mul(Negate(Num(258)),Pow(b,3)),Mul(Num(1436),Pow(b,2)),Mul(Negate(Num(661)),b),Num(81))),
            Equation(Mul(Num(81),g),Sum(Mul(f,qq),Mul(u,l0),m0)),
            Paragraph(Text("For n≥1 and |u|≤16n, summing absolute monomials and using nʲ≤nᵏ for j≤k gives |Q−27b⁵|≤12519n⁴, |L₀|≤900n⁴ and |M₀|≤3966n⁵. The first constant is 36·256+192·16+231=12519; the second is 3·10·30=900; the third is 333+1197+258+1436+661+81=3966. For n≥1000, 12519n⁴≤26n⁵, and hence |Q|≥27n⁵−12519n⁴≥n⁵. On a solution the identity gives |F|n⁵≤|FQ|=|uL₀+M₀|≤(16·900+3966)n⁵=18366n⁵. Cancelling the positive n⁵ yields |F(u,b)|≤18366. Thus every solution with |b|≥1000 has a representative with the same b and an integer r=F(u,b) in [−18366,18366].")),
            Paragraph(Text("For each fixed integer r, define the following polynomials in b. Here A, B and C retain their definitions above.")),
            Equation(d0,Sub(Add(Mul(Num(3),Pow(b,2)),Mul(Num(6),b)),Num(1))),
            Equation(tr,Sum(Mul(Num(3),Pow(b,2)),Mul(Num(13),b),r)),
            Equation(lr,Mul(Mul(Num(3),d0),Sum(Mul(a,d0),Mul(Negate(Num(2)),Mul(a,tr)),Mul(Num(9),bb)))),
            Equation(mr,Sum(Mul(Mul(a,tr),Add(Pow(d0,2),tr)),Mul(Negate(Num(9)),Mul(bb,tr)),Mul(Num(81),c))),
            Paragraph(Text("When F(u,b)=r, the identities 9q=3uD₀−Tᵣ and 9u²=3u+Tᵣ reduce 81G(u,b) to uLᵣ+Mᵣ. For a solution Mᵣ=−uLᵣ, so the eliminant below vanishes. No division by Lᵣ occurs, including when Lᵣ=0.")),
            Equation(hr,Sub(Add(Mul(Num(9),Pow(mr,2)),Mul(Num(3),Mul(mr,lr))),Mul(tr,Pow(lr,2)))),
            Equation(hr,Mul(Sub(Sub(Mul(Num(9),Pow(u,2)),Mul(Num(3),u)),tr),Pow(lr,2))),
            Paragraph(Text("The second equality holds under the two equations F(u,b)=r and G(u,b)=0; its right side is zero. Expanding the defining polynomials gives:")),
            Equation(lr,Sum(Mul(Negate(Num(189)),Pow(b,4)),Mul(Sub(Negate(Num(306)),Mul(Num(54),r)),Pow(b,3)),Mul(Sub(Num(216),Mul(Num(90),r)),Pow(b,2)),Mul(Sub(Mul(Num(54),r),Num(6)),b),Negate(Num(3)),Mul(Negate(Num(6)),r))),
            Equation(mr,Sum(Mul(Sub(Mul(Num(27),r),Num(333)),Pow(b,5)),Mul(Sub(Mul(Num(99),r),Num(1197)),Pow(b,4)),Mul(Sub(Mul(Num(63),r),Num(258)),Pow(b,3)),Mul(Sub(Num(1436),Mul(Num(30),r)),Pow(b,2)),Mul(Sum(Mul(Num(3),Pow(r,2)),Mul(Negate(Num(2)),r),Negate(Num(661))),b),Num(81),Negate(Pow(r,2)),Negate(r))),
            Paragraph(Text("These expansions show that Hᵣ has degree at most ten. Its coefficient of b¹⁰ is 9(27r−333)²−3·189²=729((3r−37)²−147). For any integer r, (3r−37)² is congruent to one modulo three, whereas 147 is congruent to zero. The coefficient is therefore nonzero. Hᵣ is a nonzero polynomial of degree exactly ten and has finitely many integer roots.")),
            Paragraph(Text("The b-projection of G(a,b)=0 is contained in [−999,999] together with the union of the root sets of Hᵣ for integers r in [−18366,18366]. Both intervals are finite, and each root set is finite, so the projection is finite. For every fixed integer b, the polynomial G(a,b) in a has quartic coefficient 3b−1. It is nonzero because 3b=1 has no integer solution; its integer root set, and hence each a-fiber, is finite. Applying finiteness from finite projection and finite fibers proves that the set of all (a,b) in ℤ² with G(a,b)=0 is finite. This includes zero and negative coordinates, every small-b fiber, and both involution partners.")),
            Paragraph(Text("This application establishes finiteness of the stated polynomial zero set. An effective list of points, emptiness and classification require further arguments. Relating the polynomial to admissible graph or matrix parameters is a separate mathematical step. The arithmetic argument does not establish geometric irreducibility, Kummer models, full constant fields or separability, local orders or ramification, or genus-three and genus-ten calculations. The public source's geometric discussion is separate from the polynomial and elementary finiteness argument given here."))));
    }

    private static Formula Sum(params Formula[] terms) => terms.Aggregate(Add);
    private static DocumentBlock Equation(Formula left,Formula right) => new DocumentBlock.DisplayFormula(Eq(left,right));

    private static DocumentBlock Node(string id,string title,string name,Formula f,string text,DescribeRole role,AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("six-"+id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(f)),provenance ?? AssessedProvenance.FromLiterature(Source),Blocks(Paragraph(Text(text))),role);
    private static Formula V(string s)=>F.Id(s);
    private static Formula Real()=>new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Nat()=>new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula FinSix()=>Call("Fin",D(6));
    private static Formula Vec()=>new Formula.TypeArrow(FinSix(),Real());
    private static Formula Call(string s,params Formula[] a)=>a.Length==0?Seq(Operatorname,Grp(V(s))):new Formula.Apply(Seq(Operatorname,Grp(V(s))),[..a]);
    private static Formula App(Formula f,params Formula[] a)=>new Formula.Apply(f,[..a]);
    private static Formula All(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Ex(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(s),t,b);
    private static Formula Rel(Formula a,FormulaRelationOperator op,Formula b)=>new Formula.Relation(a,op,b);
    private static Formula Eq(Formula a,Formula b)=>Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b)=>Rel(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Lt(Formula a,Formula b)=>Rel(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a,Formula b)=>Rel(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(params Formula[] a)=>a.Length==1?a[0]:new Formula.Logic(a[0],FormulaLogicOperator.And,And(a[1..]));
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Div(Formula a,Formula b)=>new Formula.Fraction(a,b);
    private static Formula Pow(Formula a,byte n)=>new Formula.Power(a,D(n));
    private static Formula Negate(Formula a)=>new Formula.Negate(a);
    private static Formula Sqrt(Formula a)=>Call("sqrt",a);
    private static Formula Smul(Formula a,Formula b)=>Seq(a,Sp,Cdot,Sp,b);
    private static Formula Lambda(string s,Formula t,Formula b)=>Seq(LambdaLower,Sp,V(s),Sp,Colon,Sp,t,Sp,Mapsto,Sp,b);
    private static Formula ABC(Formula f)=>All("a",Real(),All("b",Real(),All("c",Real(),f)));
    private static Formula PositiveABC(Formula f)=>Imp(Lt(D(0),V("a")),Imp(Lt(D(0),V("b")),Imp(Lt(D(0),V("c")),f)));
    private static Formula Q()=>Call("quotient",V("a"),V("b"),V("c"));
    private static Formula S()=>Call("symmetric",V("a"),V("b"),V("c"));
    private static Formula W()=>Call("weights",V("a"),V("b"),V("c"));
    private static Formula Roots()=>Call("rootWeights",V("a"),V("b"),V("c"));
    private static Formula PermInverse(Formula i)=>Call("inverse",Call("supportPermutation"),i);
    private static Formula Join(Formula separator,Formula[] a)=>Seq([..a.SelectMany((v,i)=>i==0?new[]{v}:new[]{separator,v})]);
    private static Formula Vector(params Formula[] a)=>Seq(OpenBracket,Join(Comma,a),CloseBracket);
    private static Formula Matrix(params Formula[][] r)=>Seq(Begin,Grp(V("pmatrix")),Join(RowBreak,[..r.Select(x=>Join(Amp,x))]),End,Grp(V("pmatrix")));
    private static Formula QuotientMatrix()
    {
        Formula a=V("a"),b=V("b"),c=V("c"),ab=Mul(a,b),ac=Mul(a,c),bc=Mul(b,c),o=D(0);
        return Matrix([Add(Add(b,c),bc),Negate(b),Negate(c),o,o,Negate(bc)],
            [Negate(a),Add(Add(a,c),ac),Negate(c),o,Negate(ac),o],
            [Negate(a),Negate(b),Add(Add(a,b),ab),Negate(ab),o,o],
            [o,o,Negate(c),c,o,o],[o,Negate(b),o,o,b,o],[Negate(a),o,o,o,o,a]);
    }
    private static Formula SymmetricMatrix()
    {
        Formula a=V("a"),b=V("b"),c=V("c"),o=D(0),p=Mul(Mul(Sqrt(a),Sqrt(b)),Sqrt(c));
        Formula ab=Mul(Sqrt(a),Sqrt(b)),ac=Mul(Sqrt(a),Sqrt(c)),bc=Mul(Sqrt(b),Sqrt(c));
        return Matrix([Add(Add(b,c),Mul(b,c)),Negate(ab),Negate(ac),Negate(p),o,o],
            [Negate(ab),Add(Add(a,c),Mul(a,c)),Negate(bc),o,Negate(p),o],
            [Negate(ac),Negate(bc),Add(Add(a,b),Mul(a,b)),o,o,Negate(p)],
            [Negate(p),o,o,a,o,o],[o,Negate(p),o,o,b,o],[o,o,Negate(p),o,o,c]);
    }
    private static Formula At(string s,byte i)=>App(V(s),D(i));
    private static Formula Diff(byte i,byte j)=>Pow(Sub(At("z",i),At("z",j)),2);
    private static Formula Energy()=>Add(Add(Add(Mul(Mul(V("a"),V("b")),Diff(0,1)),Mul(Mul(V("a"),V("c")),Diff(0,2))),Mul(Mul(V("b"),V("c")),Diff(1,2))),Mul(Mul(Mul(V("a"),V("b")),V("c")),Add(Add(Diff(0,5),Diff(1,4)),Diff(2,3))));
    private static Formula MulVec(Formula m,Formula z)=>Call("mulVec",m,z);
    private static Formula Geometry()
    {
        Formula z=V("z"),p=Call("supportPermutation"),q=Q();
        Formula energy=All("z",Vec(),Eq(Call("dotProduct",Lambda("i",FinSix(),Mul(App(W(),V("i")),App(z,V("i")))),MulVec(q,z)),Energy()));
        Formula kernel=All("z",Vec(),Iff(Eq(MulVec(q,z),D(0)),Ex("t",Real(),Eq(z,Lambda("i",FinSix(),V("t"))))));
        Formula baseFacts=And(energy,kernel,Eq(MulVec(q,Lambda("i",FinSix(),D(1))),D(0)),Eq(Call("vecMul",W(),q),D(0)));
        Formula similarity=Eq(S(),Mul(Mul(Call("diagonal",Roots()),Call("submatrix",q,p,p)),Call("diagonal",Lambda("i",FinSix(),Call("inverse",App(Roots(),V("i")))))));
        Formula v=Call("toQuotientVector",V("a"),V("b"),V("c"),z);
        Formula transport=All("e",Real(),All("z",Vec(),Imp(Ne(z,D(0)),Imp(Eq(MulVec(S(),z),Smul(V("e"),z)),And(Ne(v,D(0)),Eq(MulVec(q,v),Smul(V("e"),v)))))));
        return And(baseFacts,Call("PosSemidef",S()),similarity,transport);
    }
    private static Formula Low(Formula m)=>Call("balancedLow",m);
    private static Formula Discriminant(Formula m)=>Sub(Pow(Add(m,D(4)),2),D(1,2));
    private static Formula LowFormula(Formula m)=>Div(Sub(Add(Pow(m,2),Mul(D(4),m)),Mul(m,Sqrt(Discriminant(m)))),D(2));
    private static Formula BalancedAt(Formula m)
    {
        Formula q=Call("quotient",m,m,m),l=Low(m),z=V("z"),e=V("e"),x=V("x");
        Formula pair=Ex("z",Vec(),And(Ne(z,D(0)),Eq(MulVec(q,z),Smul(l,z))));
        Formula min=All("e",Real(),Imp(Lt(D(0),e),All("z",Vec(),Imp(Ne(z,D(0)),Imp(Eq(MulVec(q,z),Smul(e,z)),Le(l,e))))));
        Formula quadratic=Add(Sub(Pow(x,2),Mul(Add(Pow(m,2),Mul(D(4),m)),x)),Mul(D(3),Pow(m,2)));
        Formula factor=All("x",Real(),Eq(Call("det",Sub(Smul(x,D(1)),q)),Mul(Mul(x,Sub(Sub(x,Pow(m,2)),m)),Pow(quadratic,2))));
        return And(pair,Lt(D(0),l),Lt(l,m),Lt(Div(Mul(D(3),m),Add(m,D(4))),l),Lt(l,D(3)),Eq(l,Div(Mul(D(6),m),Add(Add(m,D(4)),Sqrt(Discriminant(m))))),min,factor,Lt(l,Add(Pow(m,2),m)),Lt(Add(Pow(m,2),m),Div(Add(Add(Pow(m,2),Mul(D(4),m)),Mul(m,Sqrt(Discriminant(m)))),D(2))));
    }
    private static Formula SmallSecond()
    {
        Formula u=V("u"),t=V("t"),vecTwo=new Formula.TypeArrow(Call("Fin",D(2)),Real());
        Formula plane=Vector(App(u,D(0)),App(u,D(1)),D(0),Mul(t,App(u,D(0))),Mul(t,App(u,D(1))),D(0));
        Formula injective=Call("Injective",Lambda("u",vecTwo,plane));
        Formula negative=All("u",vecTwo,Imp(Ne(u,D(0)),Lt(Call("dotProduct",plane,MulVec(Sub(S(),Smul(D(3),D(1))),plane)),D(0))));
        return ABC(PositiveABC(Imp(Le(V("a"),V("b")),Imp(Le(V("b"),D(3)),Ex("t",Real(),And(injective,negative))))));
    }
    private static Formula Balanced()
    {
        Formula n=V("n"),k=V("K"),z=V("z");
        Formula realClause=All("m",Real(),Imp(Le(D(1),V("m")),BalancedAt(V("m"))));
        Formula realLimit=Call("Tendsto",Call("balancedLow"),Call("atTop"),Call("nhds",D(3)));
        Formula integerLimit=Call("Tendsto",Lambda("n",Nat(),Low(Call("realCast",n))),Call("atTop"),Call("nhds",D(3)));
        Formula sharp=All("K",Real(),Imp(Lt(k,D(3)),Ex("n",Nat(),And(Le(D(1),n),Lt(k,Low(Call("realCast",n))),Ex("z",Vec(),And(Ne(z,D(0)),Eq(MulVec(Call("quotient",Call("realCast",n),Call("realCast",n),Call("realCast",n)),z),Smul(Low(Call("realCast",n)),z))))))));
        return And(realClause,realLimit,integerLimit,sharp);
    }
}
