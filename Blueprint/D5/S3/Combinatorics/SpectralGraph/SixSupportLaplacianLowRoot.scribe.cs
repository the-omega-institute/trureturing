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
                "The factorization gives zero, m squared plus m, and the two quadratic roots, each quadratic root counted twice. For q_m(x)=x squared minus (m squared plus 4m)x plus 3m squared, q_m(0)=3m squared is positive, q_m(m)=minus m cubed is negative, and q_m(3)=9−12m is negative when m is at least one. The smaller quadratic root lies between zero and m; the larger root exceeds m squared plus m. A nonzero real symmetric eigenvector is constructed and transported by the proved similarity to C. Rationalization gives the strict lower bound 3m/(m+4), while the upper bound is three. The lower bound tends to three, so squeezing proves the real limit and the positive-integer subsequence limit. For every K below three there is a positive integer m whose smallest positive quotient eigenvalue exceeds K; every other positive real quotient eigenvalue then also exceeds K. Thus no constant smaller than three bounds the smallest positive quotient eigenvalues uniformly. The positive-real theorem supplies the same uniform bound for unequal ordered weights; the integer consequence follows by specializing its parameters.", DescribeRole.Theorem))));

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
