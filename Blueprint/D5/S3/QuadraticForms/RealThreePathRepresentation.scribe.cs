using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class RealThreePathRepresentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original arbitrary marker and finite nonnegative readout determine a real-linear minimal complete complex Hilbert representation, with the original baseline and label-preserving uniqueness.",
        H("Original real-linear Hilbert models"),
        Blocks(Paragraph(Text("V is an arbitrary real vector space, U is an arbitrary function and q is finite real-valued. Balance means exactly RealThreePathPolar.Balance, the original F140 relation for all original x,y and all real t. There is no original topology or regularity hypothesis. The phase omega is -1/2+i sqrt(3)/2.")),
        new DocumentBlock.DisplayFormula(ModelConditions()),
        Paragraph(Text("HilbertModel(U,q) consists of a complex Hilbert carrier H, complete with its normed additive group and complex inner product, an original real-linear map label:V to H, the displayed norm and phase conditions, and the displayed minimality condition. The constructed carrier has the universe of V. Converse carriers may have any independent universe; the two carriers in uniqueness are independently quantified. No nontriviality condition excludes the zero carrier or zero label map.")),
        Describe.Lean(
            DescribeId.Create("original-visible-quotient"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/RealThreePathRepresentation.original_visible_quotient"),
            H("Actual radical descent and competing-model factorization"),
            StatementSource.FromAuthor(Disp(QuotientStatement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For the displayed B, N=ker(B) and W=V/N; pi is the original real quotient map. These are abbreviations in the formula, not extra premises. B and g are real bilinear maps; T and every factor map are real-linear. The same original q and U determine B, the quotient, the quotient form and the quotient marker.")),
                Paragraph(Text("The real polar theorem supplies B and its actual radical. Subtracting the three-direction identity proves that marker values at equal quotient classes agree; the same identity proves additivity and real scalar compatibility modulo that radical. Quotient.liftOn therefore gives a lawful real-linear T with T(pi(x))=pi(U(x)). LinearMap.liftQ₂ descends the existing bilinear form, and positivity plus the actual radical identity gives a positive definite quotient form. The original orbit sum gives I+T+T squared=0 on every quotient class. Bilinear isometry holds on arbitrary quotient arguments by quotient surjectivity.")),
                Paragraph(Text("Every competing original model has norm zero on N, because its norm-square readout is the same derived B(x,x). Its original real-linear label therefore factors through the actual real quotient using Submodule.liftQ. This is proved for all minimal original models, rather than assumed for the constructed model or replaced by additive-only labels."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("original-hilbert-characterization"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/RealThreePathRepresentation.original_hilbert_characterization"),
            H("Full original representation, arbitrary-model converse and unique unitary"),
            StatementSource.FromAuthor(Disp(Characterization())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The first conjunct gives a complete minimal model exactly when the original F140 law holds. The second gives the converse for any complete complex Hilbert carrier and any original real-linear F satisfying the norm and phase equations; no minimality is needed there. Consequently the existential representation is equivalent to the source formulation that does not demand minimality in advance. The third conjunct quantifies every pair of minimal original models and gives a unique complex-linear isometry equivalence preserving each original label. The last conjunct retains q(0) as the global minimum.")),
                Paragraph(Text("On the derived radical quotient, the real bilinear form and the cyclotomic marker relation imply the additive three-way law for its nonnegative diagonal. ThreeWayPositiveKernel.three_way_hilbert_characterization supplies its existing complete minimal Hilbert representation and uniqueness; no new completion or Gram framework is introduced.")),
                Paragraph(Text("The supplier label is initially additive. For each fixed quotient vector x, its scalar-line map a(t)=label(tx) has norm bounded by norm(label(x)) times abs(t), by real bilinearity of the derived diagonal. AddMonoidHomClass.continuous_of_bound and map_real_smul then make this scalar-line map real-linear. This proves the label respects the original real scalars. The only continuity is on the numerical scalar line, not an added topology or continuity premise on V.")),
                Paragraph(Text("Each competing original real-linear model descends through the same derived radical. The descended norm and phase equations and unchanged label range make it a model of the same additive supplier. Applying the supplier's unique unitary to those two descended models and using quotient surjectivity proves label-preserving uniqueness for the original models themselves.")),
                Paragraph(Text("For the converse, expand the three original outputs F(x)+t F(y), F(x)+t omega F(y), and t omega F(x)+F(y). The equations conj(omega) omega=1 and 1+omega+conj(omega)=0 cancel every mixed inner-product term, leaving the exact original right side, including its original readouts at tx and ty. Constant nonnegative q is admitted through the zero model; it supplies no escape or novelty claim. The completion represents the original observations and does not assert availability of new preparations."))),
            DescribeRole.Theorem),
        Paragraph(Text("Application to finite actual menus. Work on the same complex plane C, regarded as R squared, and fix U(z)=omega*z with omega=-1/2+i sqrt(3)/2, exactly ThreeWayPositiveKernel.omega. Let M be any finite family of actual triples (x,y,t) in C times C times R, including the empty family. Repeated triples may be identified because they ask the identical equality at identical points. For each triple retain the seven actual reading points x+t*y, x+t*U(y), t*U(x)+y, x, y, t*x and t*y. Let A be their union together with zero, let G={1,omega,omega^2,-1,-omega,-(omega^2)}, and set S={g*a : g in G, a in A}. Every occurrence of the same actual point has the same readout; the two sides are never sampled independently.")),
        Paragraph(Text("For this same S and every real epsilon>0 define the following real-valued functions on all of C. The square outside P is the square of the entire product.")),
        new DocumentBlock.DisplayFormula(FiniteMenuReadout()),
        Paragraph(Text("Each factor norm(z-a) squared is (Re(z)-Re(a)) squared plus (Im(z)-Im(a)) squared. Finite products, squares and sums therefore make q_epsilon a polynomial in the two real coordinates and give ContDiff R infinity q_epsilon, with no smoothness premise. This asserts real smoothness on R squared. Both summands are nonnegative, and norm(z) squared is strictly positive for every z other than zero. Since zero belongs to S, P(0)=0 and q_epsilon(0)=0. These conclusions hold for every finite M and every positive epsilon.")),
        Paragraph(Text("The exact phase satisfies omega cubed=1 and norm(omega)=1. Multiplication by omega and by -1 permutes S. For either multiplier g, reindexing the same finite product by a=g*b and using norm(g*z-g*b)=norm(z-b) gives P(g*z)=P(z). Thus q_epsilon(U(z))=q_epsilon(z) and q_epsilon(-z)=q_epsilon(z) for all z. The finite-set reindexing uses Finset.prod_image and Finset.card_image_of_injective; no extra invariance hypothesis on q_epsilon is introduced.")),
        Paragraph(Text("For every actual point a in S one product factor vanishes, so P(a)=0 and q_epsilon(a)=norm(a) squared. In particular every reading in every triple of M agrees exactly with the standard square model. The original check for a readout q is the displayed equality, including its baseline and the unaltered readouts at t*x and t*y.")),
        new DocumentBlock.DisplayFormula(FiniteMenuCheck()),
        Paragraph(Text("Apply the arbitrary-model converse of original_hilbert_characterization with V=C as a real vector space, H=C with its usual complete complex Hilbert structure, F the identity real-linear map, U(z)=omega*z and q(z)=norm(z) squared. Its norm and phase equations are identities, so this standard readout passes the original equality for every x,y in C and every real t. Substitution of the identical actual readings and zero baseline proves that q_epsilon passes every listed check.")),
        Paragraph(Text("To see why the same q_epsilon fails a genuine original instance, put B=sum over a in S of norm(a) and c=q_epsilon(1). Choose a real r>max(B+1,1,(c+1)/epsilon). Finset.single_le_sum and norm_sub_norm_le give norm(r-a)>1 for every a in S. The zero factor is r squared; Finset.mul_prod_erase and Finset.one_le_prod₀ give P(r)>=r squared. Consequently q_epsilon(r)>=r^2+epsilon*r^4>c*r^2. All real r here are embedded in the same C, and epsilon>0 is the original arbitrary parameter.")),
        Paragraph(Text("If q_epsilon satisfied every original F140 check, its nonnegativity would allow the forward implication of original_hilbert_characterization to supply a complete minimal HilbertModel for this same U and q_epsilon. Its original real-linear label L and zero baseline give q_epsilon(r)=norm(L(r*1)) squared=r squared*norm(L(1)) squared=r squared*q_epsilon(1) for every real r, contradicting the preceding strict inequality. Negating the universal original check therefore gives actual x,y in C and an actual real t where the displayed equality fails. This triple lies outside M because every triple in M passes. Completion and label-preserving minimal uniqueness are supplied by the existing characterization; no new representation construction is needed.")),
        Paragraph(Text("This application concerns unrestricted readout functions and preserves all original real parameters. It includes empty menus and coincident reading points. A known finite-dimensional function class can have a different finite certification theorem whose hypotheses and range require their own justification. The argument distinguishes finite readouts used by each verification from one fixed finite menu certifying the universal law. It supplies a mathematical application of the existing characterization and finite-product/calculus facts, with no claim of literature novelty, physical realization or access to additional preparations.")))));

    private static Formula FiniteMenuReadout()
    {
        var z=V("z");var a=V("a");
        return Seq(Equal(Call("P",z),Seq(Prod,Underscore,Grp(Member(a,V("S"))),Sp,Sq(Call("norm",Sub(z,a))))),
            Comma,Sp,Equal(Seq(V("q"),Underscore,Grp(Varepsilon),Open,z,Close),
                Add(Sq(Call("norm",z)),Multiply(Varepsilon,Sq(Call("P",z))))),
            Comma,Sp,Varepsilon,Sp,Gt,Sp,D(0));
    }
    private static Formula FiniteMenuCheck()
    {
        var x=V("x");var y=V("y");var t=V("t");
        Formula Q(Formula z)=>Call("q",z);
        Formula U(Formula z)=>Call("U",z);
        return Equal(Add(Add(Add(Q(Add(x,Multiply(t,y))),Q(Add(x,Multiply(t,U(y))))),
                Q(Add(Multiply(t,U(x)),y))),Multiply(D(3),Q(D(0)))),
            Add(Add(Add(Multiply(D(2),Q(x)),Q(y)),Q(Multiply(t,x))),Multiply(D(2),Q(Multiply(t,y)))));
    }

    private static Formula QuotientStatement()
    {
        var a=V("V");var x=V("x");var y=V("y");var z=V("z");var w=V("w");var b=V("B");var g=V("g");var r=V("R");
        var n=Call("ker",b);var quotient=Call("Quotient",a,n);
        Formula Pi(Formula s)=>Call("mkQ",n,s);
        Formula B(Formula s,Formula t)=>Call("B",s,t);
        Formula G(Formula s,Formula t)=>Call("g",s,t);
        Formula T(Formula s)=>Call("T",s);
        Formula U(Formula s)=>Call("U",s);
        var polar=All("x",a,All("y",a,Equal(B(x,y),Div(Sub(Call("q",Add(x,y)),Call("q",Sub(x,y))),D(4)))));
        var sym=All("x",a,All("y",a,Equal(B(x,y),B(y,x))));
        var diag=All("x",a,Equal(Call("q",x),Add(Call("q",D(0)),B(x,x))));
        var radical=All("x",a,Seq(Paren(Equal(B(x,x),D(0))),Sp,Iff,Sp,Member(x,n)));
        var lift=All("x",a,All("y",a,Equal(G(Pi(x),Pi(y)),B(x,y))));
        var pos=All("z",quotient,Seq(D(0),Sp,Le,Sp,G(z,z)));
        var definite=All("z",quotient,Seq(Paren(Equal(G(z,z),D(0))),Sp,Iff,Sp,Equal(z,D(0))));
        var marker=All("x",a,Equal(T(Pi(x)),Pi(U(x))));
        var isometry=All("z",quotient,All("w",quotient,Equal(G(T(z),T(w)),G(z,w))));
        var cycle=All("z",quotient,Equal(Add(Add(z,T(z)),T(T(z))),D(0)));
        var factor=All("R",Model(),ExistsF("F",Linear(Real,quotient,Call("H",r)),All("x",a,
            Equal(Call("F",Pi(x)),Call("label",r,x)))));
        return Telescope(Implies(And(Nonnegative(),Balance()),ExistsF("B",Bilinear(a),
            And(polar,sym,diag,radical,ExistsF("g",Bilinear(quotient),ExistsF("T",Linear(Real,quotient,quotient),
                And(lift,pos,definite,marker,isometry,cycle,factor)))))));
    }
    private static Formula Characterization()
    {
        var a=V("V");var x=V("x");var h=V("H");var r=V("R");var s=V("S");
        var iff=Seq(Paren(Balance()),Sp,Iff,Sp,Call("Nonempty",Model()));
        var norm=All("x",a,Equal(Call("q",x),Add(Call("q",D(0)),Sq(Call("norm",Call("F",x))))));
        var phase=All("x",a,Equal(Call("F",Call("U",x)),Multiply(V("omega"),Call("F",x))));
        var converse=All("H",Call("Type"),Seq(Instances(h),Comma,Sp,All("F",Linear(Real,a,h),
            Implies(norm,Implies(phase,Balance())))));
        var unitary=All("R",Model(),All("S",Model(),Seq(Exists,Bang,Sp,V("e"),Sp,Colon,Sp,
            Call("LinearIsometryEquiv",Complex,Call("H",r),Call("H",s)),Comma,Sp,
            All("x",a,Equal(Call("e",Call("label",r,x)),Call("label",s,x))))));
        var minimum=Implies(Balance(),All("x",a,Seq(Call("q",D(0)),Sp,Le,Sp,Call("q",x))));
        return Telescope(Implies(Nonnegative(),And(iff,converse,unitary,minimum)));
    }
    private static Formula ModelConditions()
    {
        var a=V("V");var r=V("R");var x=V("x");
        Formula L(Formula z)=>Call("label",r,z);
        return Telescope(All("R",Model(),And(
            Call("CompleteSpace",Call("H",r)),Call("NormedAddCommGroup",Call("H",r)),
            Call("InnerProductSpace",Complex,Call("H",r)),
            All("x",a,All("y",a,Equal(L(Add(x,V("y"))),Add(L(x),L(V("y")))))),
            All("t",Real,All("x",a,Equal(L(Multiply(V("t"),x)),Multiply(V("t"),L(x))))),
            All("x",a,Equal(Call("q",x),Add(Call("q",D(0)),Sq(Call("norm",L(x)))))),
            All("x",a,Equal(L(Call("U",x)),Multiply(V("omega"),L(x)))),
            Equal(Call("topologicalClosure",Call("span",Complex,Call("range",Call("label",r)))),V("top")))));
    }
    private static Formula Instances(Formula h)=>Seq(OpenBracket,Call("NormedAddCommGroup",h),CloseBracket,Sp,
        OpenBracket,Call("InnerProductSpace",Complex,h),CloseBracket,Sp,OpenBracket,Call("CompleteSpace",h),CloseBracket);
    private static Formula Telescope(Formula body)
    {
        var a=V("V");
        return All("V",Call("Type"),Seq(OpenBracket,Call("AddCommGroup",a),CloseBracket,Sp,
            OpenBracket,Call("Module",Real,a),CloseBracket,Comma,Sp,
            All("U",Arrow(a,a),All("q",Arrow(a,Real),body))));
    }
    private static Formula Model()=>Call("HilbertModel",V("U"),V("q"));
    private static Formula Balance()=>Call("Balance",V("U"),V("q"));
    private static Formula Nonnegative()=>All("x",V("V"),Seq(D(0),Sp,Le,Sp,Call("q",V("x"))));
    private static Formula Linear(Formula k,Formula a,Formula b)=>Call("LinearMap",k,a,b);
    private static Formula Bilinear(Formula a)=>Linear(Real,a,Linear(Real,a,Real));
    private static Formula V(string n)=>F.Id(n);
    private static Formula Real=>Seq(Mathbb,Grp(V("R")));
    private static Formula Complex=>Seq(Mathbb,Grp(V("C")));
    private static Formula Add(Formula a,Formula b)=>Seq(a,Sp,Plus,Sp,b);
    private static Formula Sub(Formula a,Formula b)=>Seq(a,Sp,Minus,Sp,b);
    private static Formula Sq(Formula a)=>Seq(a,Caret,Grp(D(2)));
    private static Formula Div(Formula a,Formula b)=>Seq(Frac,Grp(a),Grp(b));
    private static Formula Paren(Formula a)=>Seq(Open,a,Close);
    private static Formula Arrow(Formula a,Formula b)=>Paren(Seq(a,Sp,To,Sp,b));
    private static Formula Member(Formula a,Formula b)=>Seq(a,Sp,InMacro,Sp,b);
    private static Formula Implies(Formula a,Formula b)=>Seq(Paren(a),Sp,Rightarrow,Sp,b);
    private static Formula All(string n,Formula t,Formula b)=>Seq(Forall,Sp,Paren(Seq(V(n),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula ExistsF(string n,Formula t,Formula b)=>Seq(Exists,Sp,Paren(Seq(V(n),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula And(params Formula[] terms)=>Seq([..terms.SelectMany((t,i)=>i==0?new[]{Paren(t)}:new[]{Sp,Land,Sp,Paren(t)})]);
}
