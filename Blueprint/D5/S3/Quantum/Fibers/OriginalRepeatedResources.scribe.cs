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
                    Paragraph(Text("FC1(T,k,h) is FiniteC1Control: there exist a natural N and a monotone sequence time with time(0)=0 and time(N)=T; on every closed consecutive interval both rate functions are continuous, and on its open interior they are the actual derivatives of k and h. Each affine leg supplies its rate. Concatenation joins the finite partitions and translates the second partition and its rates. Repeating this construction gives certificates for the actual height functions, including the waiting interval. It asserts no uniform bound on the number of pieces. The support margin is also exact: ProbRange(B,n,e) is the set of all p_i(k(t)) for t in [0,2] and i in Fin5. Its least member is min(a,c-b,1-2*c), which is positive. The range bound a<=k<=b proves the lower bound. The value a occurs at t=2 in mode 0; c-b occurs at the excursion peak in mode 1; and the middle mode is always 1-2*c. The early peak is 5/4 and the late peak is 7/4."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integral-resources"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalRepeatedResources.early_late_integral_resources"),
                H("Exact coordinate length and quadratic energy"),
                StatementSource.FromAuthor(Resources()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either actual height k and arbitrary constant real phase chi, coordinate length L is the interval integral of sqrt(deriv(k)^2+deriv(const(chi))^2), and coordinate energy Q is the interval integral of deriv(k)^2+deriv(const(chi))^2, on [0,2]. Since the phase derivative is zero these are the integrals of |deriv(k)| and deriv(k)^2. Both height integrands are interval integrable. These resources are computed from the actual piecewise functions, rather than prescribed as coefficients of a control record.")),
                    Paragraph(Text("On either open side of a concatenation, its derivative is the corresponding original derivative, with the second clock translated by T. The joining singleton is Lebesgue null. Splitting interval integrals therefore adds the two actual resources. More generally the calculation applies to any real function F of the derivative, since each affine piece has constant derivative. Each prefix excursion has rates plus and minus 2*n*(b-a), each for 1/(2*n). The suffix rates are plus and minus 4*(b-a), each for 1/4, and zero for 1/2. Substituting absolute value and square gives the displayed formulas, independent of the suffix order.")),
                    Paragraph(Text("The two values agree within each pair and grow with n. Constant phase contributes zero derivative energy. Metric total variation and essential speed are given below for the same functions and clock. It does not establish arbitrary-reference quantum instrument distance or its operational supremum."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("total-variation"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalRepeatedResources.early_late_total_variation"),
                H("Metric total variation equals length"),
                StatementSource.FromAuthor(Variation()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("V(k) is eVariationOn(k,[0,2]), the supremum over ordered finite partitions of the sum of successive absolute increments, with values in the extended nonnegative reals. ofReal embeds a nonnegative real in that space. Variation adds across a joined endpoint. On each monotone affine leg it equals the absolute endpoint increment; translating the second clock preserves it. Hence each excursion contributes 2*(b-a), a waiting segment contributes zero, and the complete control has exactly n+1 excursions. Its total variation therefore equals the coordinate length computed above."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("essential-speed"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalRepeatedResources.early_late_essential_speed"),
                H("Essential speeds and constant phase"),
                StatementSource.FromAuthor(Speed()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("S(k) is the real essential supremum of |deriv(k)| for Lebesgue measure restricted to (0,2]. The derivative exists except at finitely many joining points; those points do not affect the essential supremum. The exact integral formula for an arbitrary function F of the derivative also applies to the indicator that |deriv(k)| exceeds a proposed bound. At max(2*n,4)*(b-a) its integral is zero, proving the almost-everywhere upper bound. If the essential supremum were smaller, that indicator would have positive integral on either the prefix or suffix affine pieces, contradicting its almost-everywhere vanishing. Constant phase has zero metric variation and zero essential derivative speed.")),
                    Paragraph(Text("All formulas retain the original duration 2 and quantify over every n>=1. Since every resource formula is independent of the Boolean branch, the listed aggregate resources are equal within each early/late pair. Together with OriginalRepeatedMarkedLaw.marked_inverse_nonuniformity, these same pairs rule out a uniform marked-law inverse modulus even when each compared pair must have equal aggregate resources. Their common variation, length, energy and speed grow with n, so this consequence supplies no common finite speed or variation cap. The arbitrary-reference operational distance requires its own quantum-output argument."))),DescribeRole.Theorem))));

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
            C("FC1",D(2),C("L",b,n),C("const",h)),Land,Sp,Open,Forall,Sp,F.Id("e"),Colon,F.Id("Bool"),Comma,
            C("IsLeast",C("ProbRange",b,n,F.Id("e")),C("min",C("a",b),C("min",Seq(C("c",b),Minus,C("b",b)),Seq(D(1),Minus,D(2),C("c",b))))),Close));
    }
    private static Formula Resources()
    {
        Formula b=F.Id("B"),n=F.Id("n"),e=F.Id("e"),chi=F.Id("chi"),d=Seq(Open,C("b",b),Minus,C("a",b),Close);
        Formula k=C("If",e,C("E",b,n),C("L",b,n)),r=C("deriv",k);
        return Disp(Seq(Forall,Sp,b,Colon,F.Id("Band"),Comma,n,Colon,N(),Comma,e,Colon,F.Id("Bool"),Comma,
            chi,Colon,R(),Comma,D(1),Leq,Sp,n,Rightarrow,Sp,
            C("IntervalIntegrable",C("abs",r),D(0),D(2)),Land,Sp,
            C("IntervalIntegrable",C("square",r),D(0),D(2)),Land,Sp,
            C("L",k,C("const",chi),D(2)),Eq,D(2),Cdot,Sp,Open,n,Plus,D(1),Close,Cdot,Sp,d,Land,Sp,
            C("Q",k,C("const",chi),D(2)),Eq,Open,D(4),P(n,D(2)),Plus,D(8),Close,Cdot,Sp,P(Grp(d),D(2))));
    }
    private static Formula Variation()
    {
        Formula b=F.Id("B"),n=F.Id("n"),e=F.Id("e"),k=C("If",e,C("E",b,n),C("L",b,n));
        return Disp(Seq(Forall,Sp,b,Colon,F.Id("Band"),Comma,n,Colon,N(),Comma,e,Colon,F.Id("Bool"),Comma,
            D(1),Leq,Sp,n,Rightarrow,Sp,C("V",k),Eq,C("ofReal",Seq(D(2),Open,n,Plus,D(1),Close,Cdot,Sp,Open,C("b",b),Minus,C("a",b),Close))));
    }
    private static Formula Speed()
    {
        Formula b=F.Id("B"),n=F.Id("n"),e=F.Id("e"),chi=F.Id("chi"),k=C("If",e,C("E",b,n),C("L",b,n));
        return Disp(Seq(Forall,Sp,b,Colon,F.Id("Band"),Comma,n,Colon,N(),Comma,e,Colon,F.Id("Bool"),Comma,chi,Colon,R(),Comma,
            D(1),Leq,Sp,n,Rightarrow,Sp,C("S",k),Eq,C("max",Seq(D(2),n),D(4)),Cdot,Sp,Open,C("b",b),Minus,C("a",b),Close,
            Land,Sp,C("V",C("const",chi)),Eq,D(0),Land,Sp,C("S",C("const",chi)),Eq,D(0)));
    }

}
