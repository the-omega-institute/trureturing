using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class OriginalRepeatedPrefixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal repeated original heights and their native exponential survival.",
        H("Original Repeated Prefix"),
        Blocks(Describe.Lean(DescribeId.Create("early-late-native-survival"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalRepeatedPrefix.early_late_native_survival"),
            H("Every positive cycle count with the fixed early clock"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("A Band B consists of real numbers a,b,c with 0<a<b<c<1/2. Its q is (a/b)*((c-b)/(c-a)). For d>0, up(B,d) and down(B,d) are the original affine Leg objects a to b and b to a, both of duration d. Their loop is the actual concatenate of those height functions at time d. No law or survival certificate is stored in the construction.")),
                Paragraph(Text("The prefix P(B,d,0) is the constant height a. Recursively P(B,d,j+1)=concatenate(P(B,d,j),loop(B,d),2*j*d). The prefix P(B,d,j) has duration 2*j*d. For n>=1 set d=1/(2*n), so P(B,d,n) has duration one and consists of n literal a-b-a cycles.")),
                Paragraph(Text("The early suffix concatenates the duration-1/2 loop with d=1/4 and the constant height a for duration 1/2. The late suffix concatenates that wait with the same loop. E(B,n) and L(B,n) concatenate P(B,d,n) with the respective suffix at time one. Thus their actual affine suffix joins are at 1,5/4,3/2,7/4,2. The real phase chi is constant in every original control.")),
                Paragraph(Text("OC(B,T,k,chi) denotes OriginalControl((c,c,1-2*c),T,k,const(chi)); AC(k,0,T) denotes absolute continuity on that interval. S(c,k,t) is the exponential of minus the interval integral of the native derivative hazard max(k prime,0)/k+max(-k prime,0)/(c-k). In the formula a=a(B), b=b(B), c=c(B), q=q(B), E=E(B,n), L=L(B,n), and P=P(B,1/(2*n),n).")),
                Paragraph(Text("The original affine survival formula gives a/b on each rising leg and (c-b)/(c-a) on each falling leg. At every recursive join, concatenate_original supplies the original-control certificate and native_concatenation splits the actual exponential hazard integral. Induction therefore gives S(c,P,1)=q^n. Each actual suffix contributes one more q, giving the two terminal equalities. The same recursive heights return to a. At time 5/4 they are b and a, so their height separation there is b-a independently of n.")),
                Paragraph(Text("The theorem proves absolute continuity and the original-control alternative. A separate finite-piecewise-C1 certificate for the full repeated heights, exact support-band bounds and a supremum height-distance equality require further conclusions. It does not yet prove normalization or an event identity for the full marked laws, their total variation, inverse nonuniformity or exact resource totals. Arbitrary-reference quantum outputs, operational suprema and absorbing extensions are outside its statement."))),
            DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int j=0; j<args.Length; j++) { if (j>0) parts.Add(Comma); parts.Add(args[j]); }
        parts.Add(Close);
        return Seq([.. parts]);
    }
    private static Formula V(Formula f, Formula x) => Seq(f,Open,x,Close);
    private static Formula Statement()
    {
        Formula b=F.Id("B"), n=F.Id("n"), chi=F.Id("chi"), t=F.Id("t");
        Formula a=C("a",b), high=C("b",b), c=C("c",b), q=C("q",b);
        Formula e=C("E",b,n), l=C("L",b,n), p=C("P",b,n);
        Formula re=Seq(Mathbb,Grp(F.Id("R"))), nat=Seq(Mathbb,Grp(F.Id("N")));
        Formula exponent=new Formula.Power(q,Seq(n,Plus,D(1)));
        Formula prefix=Seq(Open,Forall,Sp,t,Colon,re,Comma,t,InMacro,Sp,C("Icc",D(0),D(1)),Rightarrow,Sp,
            V(e,t),Eq,V(p,t),Land,Sp,V(l,t),Eq,V(p,t),Close);
        return Disp(Seq(Begin,Grp(F.Id("gathered")),Forall,Sp,b,Colon,F.Id("Band"),Comma,
            n,Colon,nat,Comma,chi,Colon,re,Comma,D(1),Leq,Sp,n,Rightarrow,Sp,RowBreak,Grp(),
            D(0),Lt,Sp,q,Land,Sp,q,Lt,Sp,D(1),Land,Sp,RowBreak,Grp(),
            C("OC",b,D(2),e,chi),Land,Sp,C("OC",b,D(2),l,chi),Land,Sp,RowBreak,Grp(),
            C("AC",e,D(0),D(2)),Land,Sp,C("AC",l,D(0),D(2)),Land,Sp,RowBreak,Grp(),
            prefix,Land,Sp,RowBreak,Grp(),V(e,D(2)),Eq,a,Land,Sp,V(l,D(2)),Eq,a,Land,Sp,RowBreak,Grp(),
            C("S",c,e,D(2)),Eq,exponent,Land,Sp,C("S",c,l,D(2)),Eq,exponent,Land,Sp,RowBreak,Grp(),
            V(e,Seq(Frac,Grp(D(5)),Grp(D(4)))),Eq,high,Land,Sp,
            V(l,Seq(Frac,Grp(D(5)),Grp(D(4)))),Eq,a,End,Grp(F.Id("gathered"))));
    }
}
