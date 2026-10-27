using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class OriginalMarkedConcatenationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native double-wall hazard and original Kraus outputs compose chronologically.",
        H("Native Marked Concatenation"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-concatenation"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalMarkedConcatenation.native_concatenation"),
                H("Hazard, survival and the unchanged input"),
                StatementSource.FromAuthor(Composition()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The superscript ae(Lebesgue) on the first quantifier means Lebesgue almost everywhere. For a real height k, lambda(c,k,t) is max(k prime(t),0)/k(t)+max(-k prime(t),0)/(c-k(t)). Here k prime is the derivative of the actual function, including for the concatenated height. S(c,k,t) is exp of minus the interval integral from zero to t of lambda(c,k,u). The join J(k,K,T) equals k(t) for t<=T and k(T)+K(t-T)-K(0) otherwise. The height match k(T)=K(0) makes the latter expression exactly K(t-T).")),
                    Paragraph(Text("OC(c,T,k,chi) abbreviates OriginalControl((c,c,1-2*c),T,k,const(chi)). It includes both original regularity alternatives, continuity, strict support and finite phase variation. A finite piecewise C1 original coordinate is absolutely continuous. Its derivative is integrable, and its reciprocal and opposite-wall reciprocal are continuous on the compact interval. Multiplying these reciprocals by the positive and negative derivative parts proves integrability of the native hazard. No separate integrability certificate is assumed.")),
                    Paragraph(Text("Write P(c,a,k,S)=successfulKraus(c,a,k,S) and A(c,a,k,S,g,i)=jumpKraus(c,a,k,S,g,i). These are exactly the original diagonal successful matrix and absorbing row followed by that matrix. Act denotes ordinary matrix-vector multiplication.")),
                    Paragraph(Text("At every time other than the join, a neighborhood identifies the actual concatenated height with the first height or the translated second height. Equality of derivatives follows on those neighborhoods. The exceptional singleton has zero Lebesgue measure. Splitting the actual hazard integral and translating its second interval proves the exponential product formula. In the successful matrices, the intermediate positive probabilities cancel under their square roots. This is an equality of matrices before choosing an input. The absorbing row then preserves that equality.")),
                    Paragraph(Text("The vector psi is arbitrary and need not be normalized. In particular it may be the original preparation source(c,a,beta,m,theta) with any beta, integer m and initial phase vector. The second action takes the first successful output as its input, preserving that vector and its unnormalized weight."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-join"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalMarkedConcatenation.native_marked_join"),
                H("All measurable events of two actual affine pieces"),
                StatementSource.FromAuthor(JoinedLaw()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("L and R are actual positive-duration affine Leg objects from OriginalControlMarkedJump. Their heights join and their double-wall parameter c agrees. Let T=duration(L), U=duration(R), J=J(height(L),height(R),T), SL=survival(L,T), and SR=survival(R,U). The phase chi is constant on the full concatenation. The source is exactly source(c(L),x(L),beta,m,theta); beta is any real number, m any signed integer, and theta any real phase vector on the five original modes.")),
                    Paragraph(Text("The measure mu(L,R,beta,m,theta) is markedLaw(c(L),x(L),beta,T+U,m,theta,J). Its success atom has weight equal to the sum of the squared successful Kraus amplitudes on that source. Its mode i failure measure is Lebesgue measure on (0,T+U], weighted by the squared absorbing Kraus amplitude of the same source, using the native hazard, exponential survival and logarithmic jump rates of J. The record space is Unit plus Fin5 times the real line, with success() denoting Sum.inl(()). No law or probability adapter is supplied as a premise.")),
                    Paragraph(Text("Write B(E,i)={t: Sum.inr(i,t) is in E}. F(L,E,i) is the nonnegative integral on (0,T] intersect B(E,i) of ofReal(density(L,t,i)). G(L,R,E,i) is the nonnegative integral on (T,T+U] intersect B(E,i) of ofReal(density(R,t-T,i)). The latter integrand and interval retain the exact shifted second clock. All integrals use Lebesgue measure. ofReal denotes ENNReal.ofReal. The formula quantifies over every measurable set of records.")),
                    Paragraph(Text("On the first open piece, the native rates and survival agree with those of L. On the second piece they agree with the shifted rates of R, and native survival equals SL times the shifted survival of R. Acting on the original source gives the second failure density SL*density(R,t-T,i). This uses the known source diagonal and the actual successful and absorbing matrices; it does not replace the first successful vector by a normalized preparation. The singleton at the join contributes zero. Splitting each mode integral and summing gives the displayed event identity.")),
                    Paragraph(Text("These two-piece statements supply chronological composition. They do not assert properties of a complete repeated early/late family. The full-family finite-piecewise-C1 certificate, exact resource totals, event-supremum total variation formula and inverse obstruction require further results. Arbitrary-reference quantum distance, operational suprema and the six-dimensional absorbing extension are also outside the statement."))),
                DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int j=0; j<args.Length; j++) { if(j>0) items.Add(Comma); items.Add(args[j]); }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula A(Formula f, Formula x) => Seq(f,Open,x,Close);
    private static Formula Composition()
    {
        Formula c=F.Id("c"), t=F.Id("T"), s=F.Id("s"), a=F.Id("a"), chi=F.Id("chi");
        Formula k=F.Id("k"), z=F.Id("K"), u=F.Id("u"), psi=F.Id("psi"), g=F.Id("g"), i=F.Id("i");
        Formula r=Seq(Mathbb,Grp(F.Id("R"))), complex=Seq(Mathbb,Grp(F.Id("C")));
        Formula fin=C("Fin",D(5)), j=C("J",k,z,t), end=Seq(t,Plus,s);
        Formula h=Seq(c,Lt,Sp,Q(D(1),D(2)),Land,Sp,D(0),Leq,Sp,t,Land,Sp,D(0),Leq,Sp,s,Land,Sp,
            A(k,t),Eq,A(z,D(0)),Land,Sp,a,InMacro,Sp,C("Ioo",D(0),c),Land,Sp,
            A(k,t),InMacro,Sp,C("Ioo",D(0),c),Land,Sp,A(z,s),InMacro,Sp,C("Ioo",D(0),c),Land,Sp,
            C("OC",c,t,k,chi),Land,Sp,C("OC",c,s,z,chi));
        Formula po=C("P",c,a,A(k,t),C("S",c,k,t));
        Formula pt=C("P",c,A(k,t),A(z,s),C("S",c,z,s));
        Formula pj=C("P",c,a,A(z,s),C("S",c,j,end));
        Formula at=C("A",c,A(k,t),A(z,s),C("S",c,z,s),g,i);
        Formula aj=C("A",c,a,A(z,s),C("S",c,j,end),g,i);
        Formula action=Seq(C("Act",pt,C("Act",po,psi)),Eq,C("Act",pj,psi));
        Formula jump=Seq(C("Act",at,C("Act",po,psi)),Eq,C("Act",aj,psi));
        return Disp(Seq(Begin,Grp(F.Id("gathered")),Forall,Sp,c,Comma,t,Comma,s,Comma,a,Comma,chi,Colon,r,Comma,
            Sp,k,Comma,z,Colon,Seq(r,To,Sp,r),Comma,RowBreak,Grp(),h,Rightarrow,Sp,RowBreak,Grp(),
            Open,new Formula.Power(Forall,C("ae",C("Lebesgue"))),Sp,u,Colon,r,Comma,C("lambda",c,j,u),Eq,
            C("If",Seq(u,Leq,Sp,t),C("lambda",c,k,u),C("lambda",c,z,Seq(u,Minus,t))),Close,Land,Sp,RowBreak,Grp(),
            C("S",c,j,end),Eq,C("S",c,k,t),Cdot,Sp,C("S",c,z,s),Land,Sp,RowBreak,Grp(),
            Open,Forall,Sp,psi,Colon,Seq(fin,To,Sp,complex),Comma,action,Close,Land,Sp,RowBreak,Grp(),
            Open,Forall,Sp,g,Colon,Seq(fin,To,Sp,r),Comma,i,Colon,fin,Comma,psi,Colon,Seq(fin,To,Sp,complex),Comma,jump,Close,
            End,Grp(F.Id("gathered"))));
    }
    private static Formula Q(Formula n, Formula d) => Seq(Frac,Grp(n),Grp(d));
    private static Formula JoinedLaw()
    {
        Formula l=F.Id("L"), r=F.Id("R"), chi=F.Id("chi"), beta=F.Id("beta"), m=F.Id("m"), theta=F.Id("theta");
        Formula re=Seq(Mathbb,Grp(F.Id("R"))), zi=Seq(Mathbb,Grp(F.Id("Z"))), fin=C("Fin",D(5));
        Formula e=F.Id("E"), i=F.Id("i"), t=C("duration",l), u=C("duration",r);
        Formula sl=C("survival",l,t), sr=C("survival",r,u), j=C("J",C("height",l),C("height",r),t);
        Formula mu=C("mu",l,r,beta,m,theta);
        Formula f=Seq(new Formula.Subscript(Sum,Seq(i,Colon,Sp,fin)),Sp,C("F",l,e,i));
        Formula h=Seq(new Formula.Subscript(Sum,Seq(i,Colon,Sp,fin)),Sp,C("G",l,r,e,i));
        return Disp(Seq(Begin,Grp(F.Id("gathered")),Forall,Sp,l,Comma,r,Colon,F.Id("Leg"),Comma,
            chi,Comma,beta,Colon,re,Comma,m,Colon,zi,Comma,theta,Colon,Seq(fin,To,Sp,re),Comma,RowBreak,Grp(),
            C("c",r),Eq,C("c",l),Rightarrow,Sp,C("y",l),Eq,C("x",r),Rightarrow,Sp,RowBreak,Grp(),
            C("OC",C("c",l),Seq(t,Plus,u),j,chi),Land,Sp,RowBreak,Grp(),
            Open,Forall,Sp,e,Colon,C("Set",F.Id("Record")),Comma,C("MeasurableSet",e),Rightarrow,Sp,RowBreak,Grp(),
            A(mu,e),Eq,C("If",Seq(C("success"),InMacro,Sp,e),C("ofReal",Seq(sl,Cdot,Sp,sr)),D(0)),Plus,f,
            Plus,C("ofReal",sl),Cdot,Sp,h,Close,End,Grp(F.Id("gathered"))));
    }
}
