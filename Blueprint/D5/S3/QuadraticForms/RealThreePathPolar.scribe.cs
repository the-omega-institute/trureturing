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
                Paragraph(Text("The lower-bound and Archimedean scalar estimates in raw_even_data and real_polar supply the real scalar structure. This result supplies original_visible_quotient and the original real-linear Hilbert characterization. The representation describes the original readouts; physical preparations require their own realization assumptions.")),
                new DocumentBlock.Section(H("Application: all-angle two-output characterization"), Blocks(
                Paragraph(Text("Let V be any real vector space, in any universe, and let A : V to the real numbers satisfy A(x) >= 0 for every x. Thus all readouts are finite. The following equivalence uses every real coefficient pair c,s with c squared plus s squared equal to one, including both signs. The existential quantifier is unique. IsPosSemidef means symmetry and a nonnegative diagonal, exactly as in LinearMap.BilinForm.IsPosSemidef.")),
                new DocumentBlock.DisplayFormula(Disp(AngleCharacterization())),
                Paragraph(Text("Put a0=A(0) and q(x)=A(x)-a0. Subtracting the same two baseline terms preserves the rotation-total law and gives q(0)=0. The coefficients (0,1), with second input zero, give q(-x)=q(x). Put r=1/sqrt(2). Applying the law to (z,0) at (r,r) gives 2q(rz)=q(z). Applying it to (x,y) at the same coefficients, using evenness and this scaling at x+y and x-y, gives q(x+y)+q(x-y)=2q(x)+2q(y).")),
                Paragraph(Text("Apply TauCeti.QuadraticMap.ofParallelogram with f=q, codomain the real numbers, and injectivity of multiplication by two. Its integer quadratic map E evaluates to q at every original vector. The original nonnegativity assumption gives E(x) >= -a0. Apply quadratic_nonneg with c=a0 to obtain E(x) >= 0. This step allows arbitrary nonnegative baselines; it does not assume that the centered response is positive in advance.")),
                Paragraph(Text("For any real t, take d=sqrt(1+t squared)>0 and coefficients (1/d,t/d). Rotation of the pair (dx,dy), followed by the two axis cases (dx,0) and (dy,0), gives E(x+ty)+E(tx-y)=E(x)+E(tx)+E(y)+E(ty). Here evenness replaces E(-tx+y) by E(tx-y). Subtracting the parallelogram identity E(tx+y)+E(tx-y)=2E(tx)+2E(y) gives the precise scalar-exchange premise below. No scalar homogeneity has been supplied.")),
                new DocumentBlock.DisplayFormula(Disp(ScalarExchange())),
                Paragraph(Text("Apply real_polar to this same E, its nonnegativity, and this exchange identity. It gives one real bilinear form B with B(x,y)=(E(x+y)-E(x)-E(y))/2, B(x,y)=B(y,x), and B(x,x)=E(x). The positive_additive_scalar argument inside real_polar derives real linearity from positivity of an additive scalar function. The diagonal identity and nonnegativity give IsPosSemidef, and A(x)=a0+B(x,x). The parallelogram identity also identifies this B with (A(x+y)-A(x-y))/4, since the baseline cancels.")),
                Paragraph(Text("For uniqueness, if C is another symmetric bilinear form with A(x)=a0+C(x,x), then C and B have equal diagonals at x, y, and x+y. Expanding at x+y and using symmetry gives 2C(x,y)=2B(x,y), hence C=B. Conversely, substitute A(x)=a0+B(x,x) and expand both rotated diagonals by bilinearity. The mixed terms cancel and their sum is (c squared+s squared)(B(x,x)+B(y,y)), which equals B(x,x)+B(y,y). The two baseline terms occur on both sides.")),
                Paragraph(Text("This application has no marker U and does not invoke Balance or raw_real_polar as an extra premise. It assumes no norm, topology, continuity, dimension bound, scalar homogeneity or nondegeneracy. The zero vector space, every nonnegative constant A, the zero form and forms with a radical are included; uniqueness concerns symmetric positive semidefinite forms. It is a consequence of the existing quadratic and real-polar constructions, with no claim of mathematical novelty or physical realization. The fixed-angle Hamel construction and the later calibration of a physical source are separate assertions."))))),
            DescribeRole.Theorem))));

    private static Formula AngleCharacterization()
    {
        var a=V("V");var x=V("x");var y=V("y");var c=V("c");var s=V("s");
        Formula A(Formula z)=>Call("A",z);
        var invariant=Equal(
            Add(A(Add(Mul(c,x),Mul(s,y))),A(Add(Mul(Seq(Minus,s),x),Mul(c,y)))),
            Add(A(x),A(y)));
        var law=All("x",a,All("y",a,All("c",Real,All("s",Real,
            Implies(Equal(Add(Mul(c,c),Mul(s,s)),D(1)),invariant)))));
        var form=Call("BilinForm",Real,a);
        var representation=Seq(Exists,Bang,Sp,Paren(Seq(V("B"),Sp,Colon,Sp,form)),Comma,Sp,
            And(Call("IsPosSemidef",V("B")),All("x",a,Equal(A(x),Add(A(D(0)),Call("B",x,x))))));
        return All("V",Call("Type"),Seq(OpenBracket,Call("AddCommGroup",a),CloseBracket,Sp,
            OpenBracket,Call("Module",Real,a),CloseBracket,Comma,Sp,All("A",Arrow(a,Real),
                Implies(All("x",a,Seq(D(0),Sp,Le,Sp,A(x))),Paren(Seq(Paren(law),Sp,Iff,Sp,Paren(representation)))))));
    }

    private static Formula ScalarExchange()
    {
        var x=V("x");var y=V("y");var t=V("t");
        Formula E(Formula z)=>Call("E",z);
        var difference=Sub(E(Add(x,Mul(t,y))),E(Add(Mul(t,x),y)));
        var terms=Add(Sub(Sub(E(x),E(y)),E(Mul(t,x))),E(Mul(t,y)));
        return All("x",V("V"),All("y",V("V"),All("t",Real,Equal(difference,terms))));
    }

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
