using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class RealThreePathFiniteQueryBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every prescribed finite three-path menu has an explicit smooth positive extension which preserves all tested values and both finite symmetries but fails global balance.",
        H("The exact boundary of finite three-path queries"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-query-boundary"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/RealThreePathFiniteQueryBoundary.finite_query_boundary"),
            H("An explicit simultaneous countermodel for every finite menu"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Fix the original real vector space C, with U(z)=omega z and omega=-1/2+i sqrt(3)/2. A recipe r is a triple (x,y,t) in C by C by R. Its readPoints are exactly 0, x, y, tx, ty, x+ty, x+tU(y), and tU(x)+y. For any finite menu M of such recipes, A is the union of their readPoints. S=phaseClosure(A) is the union, over a in A together with zero, of a, omega a, omega squared a, -a, -omega a, and -omega squared a. Thus S is finite, contains zero and every point actually read, and is closed under U and negation. Empty menus are included.")),
                new DocumentBlock.DisplayFormula(Disp(Definitions())),
                Paragraph(Text("The existential q in the statement is required to equal this explicit perturbedReadout(S,epsilon) as a function on the whole original C. The same q supplies every conclusion. ContDiff R infinity q means smoothness in the original two real coordinates. NormSq(z) is the ordinary Euclidean squared modulus. Positivity away from zero is pointwise strict positivity, with no uniform lower bound asserted.")),
                new DocumentBlock.DisplayFormula(Disp(TestLaw())),
                Paragraph(Text("Passes(q,r) means precisely the displayed equation, with Q(z)=q(z)-q(0) throughout. Balance(U,q) quantifies the same equation over all original x,y and every real t. The right side retains Q(tx) and Q(ty) as actual readouts; no squared gain is assumed. The displayed finite-menu statement therefore preserves the original tests and their baseline, rather than substituting a calibrated relation.")),
                Paragraph(Text("The construction is C140 Proposition 4.6. Since omega cubed and NormSq(omega) are one, the six-point orbits are permuted by phase and negation. Reindexing the finite distance product preserves P under both operations. Every a in S contributes a zero factor at a, so q(a)=NormSq(a). In particular q(0)=0. Smoothness follows from finite products of smooth squared distances. The nonnegative squared perturbation preserves nonnegativity and the strict positivity supplied by NormSq away from zero. The standard squared-modulus model satisfies Balance by the existing original Hilbert characterization, so equality of all original tested values preserves every listed test.")),
                Paragraph(Text("For the obstruction, restrict to the real ray. P(t) is the evaluation of the real polynomial R(X), the product over a in S of (X-Re(a)) squared plus Im(a) squared. Each factor is monic of degree two; consequently R squared has degree 4 times the cardinality of S, at least four. If q satisfied global Balance, raw_real_polar would give a real bilinear diagonal, and q(0)=0 would force q(t)=t squared q(1). The explicit perturbation would then imply R(X) squared=((q(1)-1)/epsilon) X squared, since these polynomials agree at every real t. The right side has degree at most two, a contradiction. This uses the frozen polar theorem without reconstructing the representation.")),
                Paragraph(Text("The result concerns unrestricted original real-valued readouts and an arbitrary prescribed finite menu. The countermodel may depend on that menu and epsilon. It does not assert that one fixed nonquadratic readout passes every finite menu, nor does it rule out finite certification within a separately specified finite-dimensional function class. It supplies a mathematical countermodel and makes no claim that the function is a physical preparation or probability law."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var m=V("M"); var e=V("epsilon"); var s=V("S"); var q=V("q"); var z=V("z");
        var r=V("r"); var a=V("a");
        var hypotheses=Seq(D(0),Sp,Lt,Sp,e);
        var conclusion=And(
            Equal(q,Call("perturbedReadout",s,e)),
            Member(D(0),s),
            All("r",Call("Recipe"),Implies(Member(r,m),Seq(Call("readPoints",r),Sp,Subseteq,Sp,s))),
            Call("ContDiff",Real,Infty,q),
            All("z",Complex,Seq(D(0),Sp,Le,Sp,Call("q",z))),
            All("z",Complex,Implies(Seq(z,Sp,Neq,Sp,D(0)),Seq(D(0),Sp,Lt,Sp,Call("q",z)))),
            Equal(Call("q",D(0)),D(0)),
            All("z",Complex,Equal(Call("q",Mul(V("omega"),z)),Call("q",z))),
            All("z",Complex,Equal(Call("q",Seq(Minus,z)),Call("q",z))),
            All("a",Complex,Implies(Member(a,s),Equal(Call("q",a),Call("NormSq",a)))),
            All("r",Call("Recipe"),Implies(Member(r,m),Call("Passes",q,r))),
            Seq(Neg,Call("Balance",V("U"),q)));
        return All("M",Call("Finset",Call("Recipe")),All("epsilon",Real,
            Implies(hypotheses,Seq(V("let"),Sp,V("S"),Sp,Eq,Sp,Call("phaseClosure",Call("biUnion",m,V("readPoints"))),
                Semi,Sp,ExistsF("q",Arrow(Complex,Real),conclusion)))));
    }

    private static Formula Definitions()
    {
        var z=V("z"); var a=V("a"); var p=Call("P",z);
        return Seq(Equal(p,Seq(Prod,Underscore,Grp(Seq(a,InMacro,V("S"))),Call("NormSq",Sub(z,a)))),
            Comma,Sp,Equal(Call("q",z),Add(Call("NormSq",z),Mul(V("epsilon"),Pow(p,D(2))))));
    }

    private static Formula TestLaw()
    {
        var x=V("x");var y=V("y");var t=V("t");
        Formula Q(Formula z)=>Call("Q",z);
        Formula U(Formula z)=>Call("U",z);
        return Equal(Add(Add(Q(Add(x,Mul(t,y))),Q(Add(x,Mul(t,U(y))))),Q(Add(Mul(t,U(x)),y))),
            Add(Add(Add(Mul(D(2),Q(x)),Q(y)),Q(Mul(t,x))),Mul(D(2),Q(Mul(t,y)))));
    }

    private static Formula V(string n)=>F.Id(n);
    private static Formula Real=>Seq(Mathbb,Grp(V("R")));
    private static Formula Complex=>Seq(Mathbb,Grp(V("C")));
    private static Formula Add(Formula a,Formula b)=>Seq(a,Sp,Plus,Sp,b);
    private static Formula Sub(Formula a,Formula b)=>Seq(a,Sp,Minus,Sp,b);
    private static Formula Mul(Formula a,Formula b)=>Multiply(a,b);
    private static Formula Pow(Formula a,Formula b)=>Seq(Paren(a),Caret,Grp(b));
    private static Formula Paren(Formula a)=>Seq(Open,a,Close);
    private static Formula Arrow(Formula a,Formula b)=>Paren(Seq(a,Sp,To,Sp,b));
    private static Formula Member(Formula a,Formula b)=>Seq(a,Sp,InMacro,Sp,b);
    private static Formula Implies(Formula a,Formula b)=>Seq(Paren(a),Sp,Rightarrow,Sp,b);
    private static Formula All(string n,Formula t,Formula b)=>Seq(Forall,Sp,Paren(Seq(V(n),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula ExistsF(string n,Formula t,Formula b)=>Seq(Exists,Sp,Paren(Seq(V(n),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula And(params Formula[] terms)=>Seq([..terms.SelectMany((t,i)=>i==0?new[]{Paren(t)}:new[]{Sp,Land,Sp,Paren(t)})]);
}
