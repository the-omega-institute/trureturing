using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class OriginalRepeatedMarkedLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original marked measures retain the common prefix and the exact failure clock.",
        H("Repeated Native Marked Laws"),
        Blocks(
            Describe.Lean(DescribeId.Create("failure-join"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw.failure_join"),
                H("Native failure composition on Borel events"),
                StatementSource.FromAuthor(Join()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Record is Unit plus Fin5 times the real clock. Success is inl(()); failures are inr(i,t). OC(c,T,k,chi) is OriginalControl((c,c,1-2*c),T,k,const(chi)). S(c,k,t) is the exponential of minus the interval integral of the derivative hazard max(k prime,0)/k+max(-k prime,0)/(c-k). The join J(k,K,T) equals k before the join and k(T)+K(t-T)-K(0) after it.")),
                    Paragraph(Text("F(c,a,beta,T,m,theta,k,A) is the sum over the five modes of the nonnegative integrals on (0,T] intersect {t:inr(i,t) in A} of the squared absorbing amplitude. That amplitude is jumpKraus(c,a,k(t),S(c,k,t),jumpRate(c,k,t),i) applied to the original source(c,a,beta,m,theta), where jumpRate is the derivative hazard minus the derivative of log p_i(k). The shift(T,A) is the pullback of A by the clock map sending inr(i,s) to inr(i,s+T), preserving success. All measures and integrals use the original Lebesgue clock.")),
                    Paragraph(Text("The parameter b may be any interior preparation height for the second integral. The original source diagonal cancels its positive reference probabilities in the absorbing squared norm. Thus the weighted density identity follows directly from the native matrices; it introduces no normalization or independent reset. The actual first successful output remains unnormalized in chronological Kraus composition. At the join the derivative may change, but its singleton has zero Lebesgue measure. Splitting the integrals and translating the second interval proves the event identity for every measurable A."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("early-late-marked-probability"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw.early_late_marked_probability"),
                H("All repeated native measures are probabilities"),
                StatementSource.FromAuthor(Laws()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("B is an arbitrary Band with 0<a<b<c<1/2, and q=(a/b)*((c-b)/(c-a)). For every n>=1, P(B,n) is the existing repeated height with n complete affine up-and-down loops on [0,1]. E(B,n) and L(B,n) are the existing early and late heights on [0,2], and HE(B), HL(B) are their actual suffix heights on their local clock [0,1]. The Boolean e chooses E,HE when true and L,HL when false. The measure mu(B,n,beta,m,theta,e) is exactly OriginalMarkedConcatenation.markedLaw(c,a,beta,2,m,theta,k), with that chosen existing height k.")),
                    Paragraph(Text("Each affine leg has native loss equal to the decrease of its surviving probability. For a concatenation, terminal survival multiplies, and the preceding failure-composition identity adds first losses to survival-weighted second losses. Induction over the actual repeated prefix therefore preserves total mass one. The same argument applies to the two suffixes and their join to the prefix. The success weight is q^(n+1), the identical prefix failure term is F(P,1,A), and the remaining term is q^n F(H,1,shift(1,A)). The arbitrary real beta, signed integer m and five initial phases are the same in all terms. Chrono(B,n,e) asserts that for every actual time 1<t<=2 and every vector psi on the five live modes, the successful action at t equals the suffix successful action at t-1 after successfulKraus(c,a,a,q^n) on psi. For every mode i the same equality holds for the absorbing action, with the actual suffix jumpRate at t-1 and the full actual jumpRate at t. The vector is arbitrary and may be unnormalized. FailureNoAtoms(B,n,beta,m,theta,e) states that each native failureMeasure(c,a,beta,2,m,theta,k,i) assigns zero to every real singleton, for every i. Thus no failure atom is placed at either suffix endpoint or at any join."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-tv"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw.native_marked_tv"),
                H("An attained supremum over all measurable events"),
                StatementSource.FromAuthor(Tv()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("TV(mu,nu) means the real supremum of |mu(A).toReal-nu(A).toReal| over every measurable record event A. It is the probability convention, without replacing the distance by a prescribed expression. AE is the actual early failure event inr '' (Fin5 times (1,3/2]). It includes all original modes and excludes terminal success.")),
                    Paragraph(Text("The common prefix and terminal success cancel on every event. Each suffix failure integral is nonnegative and at most its total mass 1-q, so their difference has absolute value at most 1-q. The native prefix survival supplies the factor q^n. The early suffix is a loop followed by a constant wait, and the late suffix is that wait followed by the loop. A wait has zero native jump density. Translation of AE therefore captures the full early suffix failure mass and none of the late suffix failure mass. Endpoints carry no failure atoms because the mode measures have densities with respect to Lebesgue measure. This proves both the all-event bound and attainment, hence the supremum equality. An L1 representation of the same probability distance would include the factor one half."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("marked-inverse-nonuniformity"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw.marked_inverse_nonuniformity"),
                H("The actual marked laws defeat every modulus at zero"),
                StatementSource.FromAuthor(Inverse()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("omega is any real function tending to zero from the positive side at zero. The statement gives the exact common height band [a,b], the full supremum height distance b-a on [0,2] for every n>=1, and the failure of every displayed uniform inverse estimate for these actual pairs. heightDistance(k,K,T) is the supremum of |k(t)-K(t)| for t in [0,T]. Recursive concatenation preserves [a,b]. The actual values at 5/4 are b and a, so this point attains the full supremum. Their positive native marked distances q^n*(1-q) tend to zero, which contradicts b-a>0 if the displayed estimates all held.")),
                    Paragraph(Text("These statements concern the original source-family marked probability laws. They do not establish arbitrary-reference quantum distance, an operational supremum, or the six-dimensional absorbing extension. Exact resource totals and full repeated finite-piecewise-C1 certificates are further assertions. In particular no common speed or variation cap is asserted."))),DescribeRole.Theorem))));

    private static Formula C(string n, params Formula[] xs)
    {
        var p=new List<Formula>{Operatorname,Grp(F.Id(n)),Open};
        for(int j=0;j<xs.Length;j++){if(j>0)p.Add(Comma);p.Add(xs[j]);}
        p.Add(Close);return Seq([..p]);
    }
    private static Formula R()=>Seq(Mathbb,Grp(F.Id("R")));
    private static Formula N()=>Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Z()=>Seq(Mathbb,Grp(F.Id("Z")));
    private static Formula Fin()=>C("Fin",D(5));
    private static Formula P(Formula x,Formula n)=>new Formula.Power(x,n);
    private static Formula Abs(Formula x)=>Seq(Lvert,Sp,x,Rvert);
    private static Formula Quant(Formula body,params Formula[] bs)
    {
        var p=new List<Formula>{Forall,Sp};
        for(int j=0;j<bs.Length;j++){if(j>0)p.Add(Comma);p.Add(bs[j]);}
        p.Add(Comma);p.Add(body);return Seq([..p]);
    }
    private static Formula Join()
    {
        Formula c=F.Id("c"),a=F.Id("a"),b=F.Id("b"),beta=F.Id("beta"),t=F.Id("T"),u=F.Id("U"),chi=F.Id("chi"),m=F.Id("m"),theta=F.Id("theta"),k=F.Id("k"),h=F.Id("K"),e=F.Id("A");
        Formula hyp=Seq(c,Lt,Sp,Seq(Frac,Grp(D(1)),Grp(D(2))),Land,Sp,a,InMacro,Sp,C("Ioo",D(0),c),Land,Sp,b,InMacro,Sp,C("Ioo",D(0),c),Land,Sp,D(0),Leq,Sp,t,Land,Sp,D(0),Leq,Sp,u,Land,Sp,C("eval",k,t),Eq,C("eval",h,D(0)),Land,Sp,C("OC",c,t,k,chi),Land,Sp,C("OC",c,u,h,chi),Land,Sp,C("MeasurableSet",e));
        Formula eq=Seq(C("F",c,a,beta,Seq(t,Plus,u),m,theta,C("J",k,h,t),e),Eq,C("F",c,a,beta,t,m,theta,k,e),Plus,C("ofReal",C("S",c,k,t)),Cdot,Sp,C("F",c,b,beta,u,m,theta,h,C("shift",t,e)));
        return Disp(Quant(Seq(hyp,Rightarrow,Sp,eq),Seq(c,Comma,a,Comma,b,Comma,beta,Comma,t,Comma,u,Comma,chi,Colon,R()),Seq(m,Colon,Z()),Seq(theta,Colon,Fin(),To,Sp,R()),Seq(k,Comma,h,Colon,R(),To,Sp,R()),Seq(e,Colon,C("Set",F.Id("Record")))));
    }
    private static Formula Laws()
    {
        Formula b=F.Id("B"),n=F.Id("n"),beta=F.Id("beta"),m=F.Id("m"),theta=F.Id("theta"),e=F.Id("e"),a=F.Id("A"),q=C("q",b),mu=C("mu",b,n,beta,m,theta,e);
        Formula f(Formula k,Formula ev)=>C("F",C("c",b),C("a",b),beta,D(1),m,theta,k,ev);
        Formula eq=Seq(C("eval",mu,a),Eq,C("If",Seq(C("success"),InMacro,Sp,a),C("ofReal",P(q,Seq(n,Plus,D(1)))),D(0)),Plus,f(C("P",b,n),a),Plus,C("ofReal",P(q,n)),Cdot,Sp,f(C("H",b,e),C("shift",D(1),a)));
        return Disp(Quant(Seq(D(1),Leq,Sp,n,Rightarrow,Sp,C("IsProbabilityMeasure",mu),Land,Sp,Open,Quant(Seq(C("MeasurableSet",a),Rightarrow,Sp,eq),Seq(a,Colon,C("Set",F.Id("Record")))),Close,Land,Sp,C("Chrono",b,n,e),Land,Sp,C("FailureNoAtoms",b,n,beta,m,theta,e)),Seq(b,Colon,F.Id("Band")),Seq(n,Colon,N()),Seq(beta,Colon,R()),Seq(m,Colon,Z()),Seq(theta,Colon,Fin(),To,Sp,R()),Seq(e,Colon,F.Id("Bool"))));
    }
    private static Formula Tv()
    {
        Formula b=F.Id("B"),n=F.Id("n"),beta=F.Id("beta"),m=F.Id("m"),theta=F.Id("theta"),a=F.Id("A"),q=C("q",b),delta=Seq(P(q,n),Cdot,Sp,Open,D(1),Minus,q,Close);
        Formula mu(Formula e)=>C("mu",b,n,beta,m,theta,e);
        Formula gap(Formula x)=>Abs(Seq(C("toReal",C("eval",mu(C("true")),x)),Minus,C("toReal",C("eval",mu(C("false")),x))));
        Formula ae=C("AE");
        return Disp(Quant(Seq(D(1),Leq,Sp,n,Rightarrow,Sp,Open,Quant(Seq(C("MeasurableSet",a),Rightarrow,Sp,gap(a),Leq,Sp,delta),Seq(a,Colon,C("Set",F.Id("Record")))),Close,Land,Sp,C("MeasurableSet",ae),Land,Sp,gap(ae),Eq,delta,Land,Sp,C("TV",mu(C("true")),mu(C("false"))),Eq,delta),Seq(b,Colon,F.Id("Band")),Seq(n,Colon,N()),Seq(beta,Colon,R()),Seq(m,Colon,Z()),Seq(theta,Colon,Fin(),To,Sp,R())));
    }
    private static Formula Inverse()
    {
        Formula b=F.Id("B"),beta=F.Id("beta"),m=F.Id("m"),theta=F.Id("theta"),o=F.Id("omega"),n=F.Id("n"),t=F.Id("t");
        Formula mu(Formula e)=>C("mu",b,n,beta,m,theta,e);
        Formula k=C("E",b,n),l=C("L",b,n),gap=C("heightDistance",k,l,D(2));
        Formula band=Quant(Seq(D(1),Leq,Sp,n,Rightarrow,Sp,Quant(Seq(t,InMacro,Sp,C("Icc",D(0),D(2)),Rightarrow,Sp,C("eval",k,t),InMacro,Sp,C("Icc",C("a",b),C("b",b)),Land,Sp,C("eval",l,t),InMacro,Sp,C("Icc",C("a",b),C("b",b))),Seq(t,Colon,R()))),Seq(n,Colon,N()));
        Formula distance=Quant(Seq(D(1),Leq,Sp,n,Rightarrow,Sp,gap,Eq,C("b",b),Minus,C("a",b)),Seq(n,Colon,N()));
        Formula noModulus=Seq(Neg,Sp,Open,Quant(Seq(D(1),Leq,Sp,n,Rightarrow,Sp,gap,Leq,Sp,C("eval",o,C("TV",mu(C("true")),mu(C("false"))))),Seq(n,Colon,N())),Close);
        return Disp(Quant(Seq(C("Tendsto",o,C("nhdsWithin",D(0),C("Ioi",D(0))),C("nhds",D(0))),Rightarrow,Sp,Open,band,Close,Land,Sp,Open,distance,Close,Land,Sp,noModulus),Seq(b,Colon,F.Id("Band")),Seq(beta,Colon,R()),Seq(m,Colon,Z()),Seq(theta,Colon,Fin(),To,Sp,R()),Seq(o,Colon,R(),To,Sp,R())));
    }
}
