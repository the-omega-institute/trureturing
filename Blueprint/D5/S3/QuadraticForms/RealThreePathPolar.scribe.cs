using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class RealThreePathPolarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original real-scalar three-path law derives a positive real bilinear polar without assuming additivity of the marker or regularity of the readout.",
        H("Original finite readout and real polarization"),
        Blocks(Describe.Lean(
            DescribeId.Create("real-three-path-balance"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/RealThreePathPolar.Balance"),
            H("The unchanged original relation"),
            StatementSource.FromAuthor(Disp(Telescope(Seq(Call("Balance",V("U"),V("q")),Sp,Iff,Sp,Paren(Law()))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("V is an arbitrary real vector space. U is an arbitrary function, and q is finite real-valued. Q(x) abbreviates q(x)-q(0), using the same original baseline in every occurrence. In particular Q(tx) and Q(ty) remain original readouts, with no homogeneity assumption. No topology, U(0)=0, additivity, linearity, periodicity or norm is supplied."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("raw-real-polar"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/RealThreePathPolar.raw_real_polar"),
            H("A derived positive real bilinear polar and actual radical"),
            StatementSource.FromAuthor(Disp(PolarStatement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("B ranges over real bilinear maps V by V to the real numbers, and ker(B) is the kernel of the real-linear map x mapped to B(x,-). All displayed properties hold for one and the same derived B. Thus its diagonal zero set is an actual real subspace, rather than an assumed quotient certificate.")),
                Paragraph(Text("Exchanging the original inputs cancels the two marker terms. The resulting scalar exchange relation separates an additive odd part A from an even part E. A finite sqrt(2) substitution gives E(2x)=4E(x); a finite translate recurrence gives the parallelogram identity. TauCeti.QuadraticMap.ofParallelogram is then applied directly, supplying the integer quadratic map and its existing bilinear polar companion.")),
                Paragraph(Text("The nonnegative original q bounds E below. Integer scaling and the Archimedean order force E to be nonnegative; on its zero set the same argument forces A to vanish. The scalar exchange relation gives b(x,ty)=b(tx,y). For each fixed x, the additive scalar function t mapped to b(tx,x) is nonnegative on nonnegative t by the square-root substitution. Monotonicity and rational sandwiches identify it with t b(x,x). Polarizing this identity proves actual real bilinearity on the original real vector space.")),
                Paragraph(Text("The original relation at x=y=0 makes U(0) invisible. It then gives Q(tU(x))=Q(tx), both even and odd invariance, and the three-direction bilinear relation. That relation forces additivity of U modulo the radical; diagonal invariance then yields full bilinear isometry. The orbit sum x+U(x)+U(U(x)) is radical. Since A vanishes there and is marker-invariant, 3A(x)=0. This proves the complete odd drift vanishes, not merely that it is additive.")),
                Paragraph(Text("The live non-finite step is the lower-bound and Archimedean scalar estimate used in raw_even_data and real_polar. Finite polynomial and phase identities are consumed proof helpers and carry no separate escape credit. This result supplies the original_visible_quotient theorem and the original real-linear Hilbert characterization. It asserts a mathematical representation of the original readouts, not that completion creates physical preparations."))),
            DescribeRole.Theorem))));

    private static Formula Law()
    {
        var x=V("x");var y=V("y");var t=V("t");var a=V("V");
        Formula Q(Formula z)=>Paren(Sub(Call("q",z),Call("q",D(0))));
        Formula U(Formula z)=>Call("U",z);
        return All("x",a,All("y",a,All("t",Real,Equal(
            Add(Add(Q(Add(x,Mul(t,y))),Q(Add(x,Mul(t,U(y))))),Q(Add(Mul(t,U(x)),y))),
            Add(Add(Add(Mul(D(2),Q(x)),Q(y)),Q(Mul(t,x))),Mul(D(2),Q(Mul(t,y))))))));
    }

    private static Formula PolarStatement()
    {
        var a=V("V");var x=V("x");var y=V("y");var b=V("B");
        Formula B(Formula s,Formula t)=>Call("B",s,t);
        Formula U(Formula z)=>Call("U",z);
        var polar=All("x",a,All("y",a,Equal(B(x,y),Div(Sub(Call("q",Add(x,y)),Call("q",Sub(x,y))),D(4)))));
        var sym=All("x",a,All("y",a,Equal(B(x,y),B(y,x))));
        var diag=All("x",a,Equal(Call("q",x),Add(Call("q",D(0)),B(x,x))));
        var positive=All("x",a,Seq(D(0),Sp,Le,Sp,B(x,x)));
        var inv=All("x",a,Equal(B(U(x),U(x)),B(x,x)));
        var orient=All("x",a,All("y",a,Equal(Add(Add(B(x,y),B(x,U(y))),B(U(x),y)),D(0))));
        var isometry=All("x",a,All("y",a,Equal(B(U(x),U(y)),B(x,y))));
        var radical=All("x",a,Seq(Paren(Equal(B(x,x),D(0))),Sp,Iff,Sp,Member(x,Call("ker",b))));
        var cycle=All("x",a,Member(Add(Add(x,U(x)),U(U(x))),Call("ker",b)));
        return Telescope(Implies(And(Nonnegative(),Call("Balance",V("U"),V("q"))),
            ExistsF("B",Call("LinearMap",Real,a,Call("LinearMap",Real,a,Real)),
                And(polar,sym,diag,positive,inv,orient,isometry,radical,cycle))));
    }

    private static Formula Telescope(Formula body)
    {
        var a=V("V");
        return All("V",Call("Type"),Seq(OpenBracket,Call("AddCommGroup",a),CloseBracket,Sp,
            OpenBracket,Call("Module",Real,a),CloseBracket,Comma,Sp,
            All("U",Arrow(a,a),All("q",Arrow(a,Real),body))));
    }
    private static Formula Nonnegative()=>All("x",V("V"),Seq(D(0),Sp,Le,Sp,Call("q",V("x"))));
    private static Formula V(string n)=>F.Id(n);
    private static Formula Real=>Seq(Mathbb,Grp(V("R")));
    private static Formula Add(Formula a,Formula b)=>Seq(a,Sp,Plus,Sp,b);
    private static Formula Sub(Formula a,Formula b)=>Seq(a,Sp,Minus,Sp,b);
    private static Formula Mul(Formula a,Formula b)=>Multiply(a,b);
    private static Formula Div(Formula a,Formula b)=>Seq(Frac,Grp(a),Grp(b));
    private static Formula Paren(Formula a)=>Seq(Open,a,Close);
    private static Formula Arrow(Formula a,Formula b)=>Paren(Seq(a,Sp,To,Sp,b));
    private static Formula Member(Formula a,Formula b)=>Seq(a,Sp,InMacro,Sp,b);
    private static Formula Implies(Formula a,Formula b)=>Seq(Paren(a),Sp,Rightarrow,Sp,b);
    private static Formula All(string n,Formula t,Formula b)=>Seq(Forall,Sp,Paren(Seq(V(n),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula ExistsF(string n,Formula t,Formula b)=>Seq(Exists,Sp,Paren(Seq(V(n),Sp,Colon,Sp,t)),Comma,Sp,b);
    private static Formula And(params Formula[] terms)=>Seq([..terms.SelectMany((t,i)=>i==0?new[]{Paren(t)}:new[]{Sp,Land,Sp,Paren(t)})]);
}
