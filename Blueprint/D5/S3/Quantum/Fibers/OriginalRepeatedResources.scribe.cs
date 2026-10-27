using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class OriginalRepeatedResourcesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal repeated excursions have finite affine partitions and resources computed from their derivatives.",
        H("Resources of the Original Repeated Controls"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-c1"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalRepeatedResources.early_late_finite_c1"),
                H("Finite piecewise continuous rates"),
                StatementSource.FromAuthor(Finite()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Band B consists of real 0<a<b<c<1/2. For n>=1, E(B,n) and L(B,n) are exactly Band.early and Band.late. Their common prefix performs n affine excursions from a to b and back on [0,1], with half-step 1/(2*n). E has its additional excursion on [1,3/2] and then waits; L waits on [1,3/2] and performs the excursion on [3/2,2]. J(f,g,T) is f up to T and f(T)+g(t-T)-g(0) thereafter. The phase is the arbitrary real constant chi.")),
                    Paragraph(Text("FC1(T,k,h) is FiniteC1Control: there exist a natural N and a monotone sequence time with time(0)=0 and time(N)=T; on every closed consecutive interval both rate functions are continuous, and on its open interior they are the actual derivatives of k and h. Each affine leg supplies its rate. Concatenation joins the finite partitions and translates the second partition and its rates. Repeating this construction gives certificates for the actual height functions, including the waiting interval. It asserts no uniform bound on the number of pieces."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integral-resources"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalRepeatedResources.early_late_integral_resources"),
                H("Exact length and quadratic height energy"),
                StatementSource.FromAuthor(Resources()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either actual height k, length is the interval integral of |deriv(k)|, and quadratic height energy is the interval integral of deriv(k)^2, on [0,2]. Both integrands are interval integrable. These resources are computed from the actual piecewise functions, rather than prescribed as coefficients of a control record.")),
                    Paragraph(Text("On either open side of a concatenation, its derivative is the corresponding original derivative, with the second clock translated by T. The joining singleton is Lebesgue null. Splitting interval integrals therefore adds the two actual resources. More generally the calculation applies to any real function F of the derivative, since each affine piece has constant derivative. Each prefix excursion has rates plus and minus 2*n*(b-a), each for 1/(2*n). The suffix rates are plus and minus 4*(b-a), each for 1/4, and zero for 1/2. Substituting absolute value and square gives the displayed formulas, independent of the suffix order.")),
                    Paragraph(Text("The two values agree within each pair and grow with n. Constant phase contributes zero derivative energy. The statement concerns these derivative integrals; equality with metric total variation and the essential speed formula are separate assertions. It does not establish arbitrary-reference quantum instrument distance or its operational supremum."))),DescribeRole.Theorem))));

    private static Formula C(string n,params Formula[] xs)
    {
        var p=new List<Formula>{Operatorname,Grp(F.Id(n)),Open};
        for(int i=0;i<xs.Length;i++){if(i>0)p.Add(Comma);p.Add(xs[i]);}
        p.Add(Close);return Seq([..p]);
    }
    private static Formula R()=>Seq(Mathbb,Grp(F.Id("R")));
    private static Formula N()=>Seq(Mathbb,Grp(F.Id("N")));
    private static Formula P(Formula x,Formula e)=>new Formula.Power(x,e);
    private static Formula Finite()
    {
        Formula b=F.Id("B"),n=F.Id("n"),h=F.Id("chi");
        return Disp(Seq(Forall,Sp,b,Colon,F.Id("Band"),Comma,n,Colon,N(),Comma,h,Colon,R(),Comma,
            D(1),Leq,Sp,n,Rightarrow,Sp,C("FC1",D(2),C("E",b,n),C("const",h)),Land,Sp,
            C("FC1",D(2),C("L",b,n),C("const",h))));
    }
    private static Formula Resources()
    {
        Formula b=F.Id("B"),n=F.Id("n"),e=F.Id("e"),d=Seq(C("b",b),Minus,C("a",b));
        Formula k=C("If",e,C("E",b,n),C("L",b,n)),r=C("deriv",k);
        return Disp(Seq(Forall,Sp,b,Colon,F.Id("Band"),Comma,n,Colon,N(),Comma,e,Colon,F.Id("Bool"),Comma,
            D(1),Leq,Sp,n,Rightarrow,Sp,
            C("IntervalIntegrable",C("abs",r),D(0),D(2)),Land,Sp,
            C("IntervalIntegrable",C("square",r),D(0),D(2)),Land,Sp,
            C("integral",D(0),D(2),C("abs",r)),Eq,D(2),Cdot,Sp,Open,n,Plus,D(1),Close,Cdot,Sp,d,Land,Sp,
            C("integral",D(0),D(2),C("square",r)),Eq,Open,D(4),P(n,D(2)),Plus,D(8),Close,Cdot,Sp,P(Grp(d),D(2))));
    }
}
