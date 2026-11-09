using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class ThreeWayPositiveKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original nonnegative three-way law on any additive group is equivalent to a complete minimal complex Hilbert representation, with a unique label-preserving complex-linear unitary between any two representations.",
        H("The original-group Hilbert representation"),
        Blocks(Describe.Lean(
            DescribeId.Create("three-way-hilbert-characterization"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/ThreeWayPositiveKernel.three_way_hilbert_characterization"),
            H("Complete representation, converse and unique unitary"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("A is an arbitrary additive commutative group, U an arbitrary additive endomorphism, and q an arbitrary finite real-valued nonnegative function. The balance law is universal in both original labels. There is no topology, rational or real scalar action, divisibility, faithfulness, invertibility, finite dimension or bounded iteration depth on A.")),
                Paragraph(Text("Rep(U,q) denotes HilbertRepresentation U q: it packages a complex inner-product space H with a normed additive group and completeness, an additive label map iota:A to H, and exactly the following conditions. The converse accepts any carrier universe, and the two carrier universes in uniqueness are independent; the constructed carrier has the original label universe. A linear isometry equivalence over the complex numbers is the unitary appearing in the statement.")),
                new DocumentBlock.DisplayFormula(ModelConditions()),
                Paragraph(Text("The phase is omega=-1/2+i sqrt(3)/2. ThreeWayBalance.three_way_quadratic_structure is applied directly to the original A to obtain an integer quadratic map Q. Half its existing polar bilinear companion is the symmetric pairing b(x,y)=(q(x+y)-q(x-y))/4, with b(x,x)=q(x). The original U-invariance and invisible orbit sums imply b(Ux,Uy)=b(x,y) and b(Ux,y)+b(x,Uy)=-b(x,y).")),
                Paragraph(Text("The structural theorem also gives q(z+Dx)=q(z) for every original z,x, where Dx=x+Ux+U squared x. Its parameters are exactly the same A,U,q and the same universal balance hypothesis as in this representation theorem. This full-background identity concerns readouts; it does not impose Dx=0 on A.")),
                Paragraph(Text("More explicitly, b is the integer bilinear map (1/2) times Q.polarBilin. Linearity of this existing polar companion gives additivity in each slot, symmetry follows by exchanging x,y, and QuadraticMap.polar_self gives b(x,x)=q(x), hence nonnegativity on the diagonal. For any other symmetric biadditive real pairing c with c(x,x)=q(x), expansion of c(x+y,x+y) gives q(x+y)=q(x)+2c(x,y)+q(y). Thus c(x,y)=(q(x+y)-q(x)-q(y))/2, which equals the displayed polarization formula by the parallelogram law. The diagonal q therefore determines this pairing uniquely, including degenerate and zero cases; no division in A is used.")),
                Paragraph(Text("Nonnegative integer Gram sums are values of b on actual finite integer sums in A. IsLocalization.exist_integer_multiples_of_finite clears rational coefficients; DenseRange.piMap applied to Rat.denseRange_cast and closedness of a finite polynomial inequality then supplies arbitrary real coefficients. Continuity belongs only to the numerical coefficient vector, not to A.")),
                new DocumentBlock.DisplayFormula(KernelFormula()),
                Paragraph(Text("The complex Gram K uses the convention conjugate-linear in its first label. For complex coefficients z, its quadratic sum is the real Gram quadratic sum on the same labels x and Ux with coefficients Re(z)+Im(z)/sqrt(3) and 2Im(z)/sqrt(3). This proves positivity for every finite support, including the zero kernel. The covariance is K(Ux,y)=conj(omega)K(x,y).")),
                Paragraph(Text("The scalar kernel is lifted to K(x,y) times the identity continuous linear map on the complex numbers. RKHS.posSemidef_iff_re_sum_kernel' supplies the exact interface, RKHS.OfKernel supplies the completed carrier, and RKHS.OfKernel.kernel_ofKernel recovers the original entries. Kernel vectors at value 1 define the additive labels. Their diagonal inner product gives q, covariance gives omega, and RKHS.kerFun_dense gives the closed complex span. No independent completion framework is constructed.")),
                Paragraph(Text("For any two complete minimal representations, real polarization and the specified phase force their full complex Gram to equal K. Each embeds into functions on the original labels by v mapped to the inner products of each label with v; density makes this map injective. The resulting reproducing kernel spaces have identical kernels, so RKHS.equiv and RKHS.equiv_kerFun give a label-preserving complex-linear isometry equivalence. Density of the original label span proves that any other such equivalence agrees everywhere. No nontriviality assumption excludes the zero representation.")),
                Paragraph(Text("Conversely, the norm-square identity in any representation gives the balance law: omega has modulus one and 1+omega+omega squared is zero, so all mixed inner-product terms cancel. This establishes both directions under the original additive-group hypotheses. The construction is mathematical completion and scalar extension; it asserts no native physical real-scalar operation or process implementation."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var a=V("A"); var x=V("x"); var y=V("y"); var u=V("U"); var q=V("q");
        Formula Q(Formula t)=>Call("q",t);
        Formula U(Formula t)=>Call("U",t);
        Formula Rep()=>Call("HilbertRepresentation",u,q);
        var nonneg=All("x",a,Seq(D(0),Sp,Le,Sp,Q(x)));
        var balance=All("x",a,All("y",a,Equal(
            Add(Add(Q(Add(x,y)),Q(Add(x,U(y)))),Q(Add(x,U(U(y))))),
            Add(Multiply(D(3),Q(x)),Multiply(D(3),Q(y))))));
        var existence=Call("Nonempty",Call("HilbertRepresentation",u,q));
        var iff=Seq(Paren(balance),Sp,Iff,Sp,existence);
        var converse=Seq(Call("Nonempty",Rep()),Sp,Rightarrow,Sp,Paren(balance));
        var eq=All("x",a,Equal(Call("e",Call("label",V("R"),x)),Call("label",V("S"),x)));
        var unique=All("R",Rep(),All("S",Rep(),Seq(Exists,Bang,Sp,V("e"),Sp,Colon,Sp,
            Call("LinearIsometryEquiv",Complex,Call("H",V("R")),Call("H",V("S"))),Comma,Sp,eq)));
        return All("A",Call("Type"),Seq(OpenBracket,Call("AddCommGroup",a),CloseBracket,Comma,Sp,
            All("U",Call("AddMonoidHom",a,a),All("q",Paren(Seq(a,Sp,To,Sp,Real)),
                Seq(Paren(nonneg),Sp,Rightarrow,Sp,And(iff,converse,unique))))));
    }

    private static Formula ModelConditions()
    {
        var a=V("A");var x=V("x");var r=V("R");
        Formula L(Formula t)=>Call("label",r,t);
        var norm=All("x",a,Equal(Call("q",x),Seq(Call("norm",L(x)),Caret,Grp(D(2)))));
        var phase=All("x",a,Equal(L(Call("U",x)),Multiply(V("omega"),L(x))));
        var dense=Equal(Call("topologicalClosure",Call("span",Complex,Call("range",Call("label",r)))),V("top"));
        return All("A",Call("Type"),Seq(OpenBracket,Call("AddCommGroup",a),CloseBracket,Comma,Sp,
            All("U",Call("AddMonoidHom",a,a),All("q",Paren(Seq(a,Sp,To,Sp,Real)),
                All("R",Call("HilbertRepresentation",V("U"),V("q")),And(
                    Call("CompleteSpace",Call("H",r)),
                    Call("NormedAddCommGroup",Call("H",r)),
                    Call("InnerProductSpace",Complex,Call("H",r)),
                    All("x",a,All("y",a,Equal(L(Add(x,V("y"))),Add(L(x),L(V("y")))))),norm,phase,dense))))));
    }

    private static Formula KernelFormula()
    {
        var a=V("A");var x=V("x");var y=V("y");
        Formula B(Formula s,Formula t)=>Seq(Frac,Grp(Seq(Call("q",Add(s,t)),Sp,Minus,Sp,Call("q",Seq(s,Sp,Minus,Sp,t)))),Grp(D(4)));
        var imaginary=Seq(Frac,Grp(Add(B(x,y),Multiply(D(2),B(Call("U",x),y)))),Grp(Call("sqrt",D(3))));
        var value=Add(B(x,y),Multiply(V("i"),imaginary));
        return All("A",Call("Type"),Seq(OpenBracket,Call("AddCommGroup",a),CloseBracket,Comma,Sp,
            All("U",Call("AddMonoidHom",a,a),All("q",Paren(Seq(a,Sp,To,Sp,Real)),
                All("x",a,All("y",a,Equal(Call("complexGram",V("U"),V("q"),x,y),value)))))));
    }

    private static Formula V(string name)=>F.Id(name);
    private static Formula Complex=>Seq(Mathbb,Grp(V("C")));
    private static Formula Real=>Seq(Mathbb,Grp(V("R")));
    private static Formula Add(Formula a,Formula b)=>Seq(a,Sp,Plus,Sp,b);
    private static Formula Paren(Formula a)=>Seq(Open,a,Close);
    private static Formula All(string name,Formula type,Formula body)=>
        Seq(Forall,Sp,Paren(Seq(V(name),Sp,Colon,Sp,type)),Comma,Sp,body);
    private static Formula And(params Formula[] terms)=>Seq(
        [.. terms.SelectMany((term,i)=>i==0?new[]{Paren(term)}:new[]{Sp,Land,Sp,Paren(term)})]);
}
