using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.OriginalFullCellFiniteTransfer;

internal sealed class DyadicLowPaymentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer/DyadicLowPayment.";
    private static DocumentBlock Definition(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("dyadic-low-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("dyadic-low-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Disjoint actual Mobius dyadic pairs reduce the complete finite low payment and enter the full positive transfer with every original mean and high term.",
        H("Actual Dyadic Low Payment"),
        Blocks(
            Paragraph(Text("All logarithms are natural. Let N>=3 and 0<=q<=N-2 be natural, "
                + "put h=q+1, L=log N, and use the actual Mobius function mu with "
                + "M(q)=sum(1<=d<=q,mu(d)). Write S(d)=sum(N<=m<2*N,b(m)*centered(d,m)) "
                + "and T(d)=log(N/d)*S(d). The original low error is "
                + "[sum(1<=d<=q,mu(d)*T(d))-(M(q)+2)*T(h)]/L. "
                + "The source-bound log_bounds audit remains declared_unresolved under "
                + "IE-C050/source.unsafe_or_external (Nat.add), tracked at "
                + "https://github.com/the-omega-institute/trureturing/issues/17873.")),
            Definition("pairs", "Internal odd dyadic pairs",
                "For every natural q, D(q)={d in Ioc(0,q): d odd, 3<=d and 2*d<=q}. "
                + "The sets D(q) and {2*d:d in D(q)} are disjoint."),
            Definition("unpaired", "The exact complementary singleton set",
                "For every natural q, U(q)=Ioc(0,q) minus the union of D(q) and its doubled image. "
                + "Scale one, scale two and every unpaired upper index remain in this literal finite complement."),
            Definition("singlePrice", "The original single-scale price with exact scale-one zero",
                "For all natural N,d, p(N,d)=0 if d=1; otherwise p(N,d)=log(N/d)*d/16. "
                + "On the legal range the logarithm is nonnegative. No positive cost is charged for centered(1,m)=0."),
            Definition("jointPrice", "The actual joint primitive price",
                "For all natural N,d, j(N,d)=R(d,log(N/d),log(N/(2*d))), where R is the "
                + "all-real-coefficient radius of the two original primitives. For an internal legal pair "
                + "the parameters satisfy 0<B<A and j=d*A^2/(8*(2*A-B))."),
            Definition("boundaryPrice", "The unchanged complete boundary price",
                "For every natural N,q, t(N,q)=abs(M(q)+2)*p(N,q+1). Thus the low error keeps "
                + "the exact signed coefficient (M(q)+2)*log(N/(q+1)) before taking its absolute value."),
            Definition("pairedCoefficient", "The complete dyadic allowance coefficient",
                "For every natural N,q, Cpair(N,q)=sum(d in D(q),abs(mu(d))*j(N,d))"
                + "+sum(k in U(q),abs(mu(k))*p(N,k))+t(N,q). "
                + "Actual magnitudes are retained, including zero Mobius values."),
            Definition("termwiseCoefficient", "The same actual termwise benchmark",
                "For every natural N,q, Csep(N,q)=sum(1<=k<=q,abs(mu(k))*p(N,k))+t(N,q). "
                + "It has the same exact scale-one zero, all actual Mobius indices, d/16 prices "
                + "and unchanged boundary as the paired coefficient."),
            Theorem("coefficient_saving", "Strict saving of the actual coefficient", SavingFormula(),
                "For every N>=3 and 6<=q<=N-2, Cpair(N,q)<Csep(N,q). For each internal pair, "
                + "with A=log(N/d), B=log(N/(2*d)), its exact price gap is "
                + "d*B*(3*A-2*B)/(16*(2*A-B))>0. The d=3 pair is present throughout this range "
                + "and abs(mu(3))=1, so the total coefficient saving is strict. "
                + "No strict residual inequality is asserted at zero variation, and no uniform "
                + "whole-error factor is inferred."),
            Theorem("full_positive_transfer", "Signed low payment and its full-positive transfer", TransferFormula(),
                "For every legal N,q and arbitrary signed real sequence b, "
                + "abs(lowError(N,q,b))<=Cpair(N,q)*V(N,b)/log N. Actual arithmetic gives "
                + "mu(2*d)=-mu(d) on each selected odd pair, whose exact contribution is "
                + "mu(d)*(T(d)-T(2*d)). The joint original primitive range bounds that bracket, "
                + "while the literal finite complement retains every other index. The signed "
                + "summation by parts keeps both endpoint jumps without either moment condition. "
                + "In the same theorem, for every real sequence F and real e,c>=0, assume "
                + "b(m)>=0 on N<=m<2*N and abs(F(k)-M(k))<=e*k+c for h<=k<N. "
                + "Set A=sum(b(m)), B=sum(m*b(m)), u=log(N/h), v=log(2*N/h), L=log N. "
                + "The original response pairing E, PLUS high replacement Z and complete mean C "
                + "satisfy abs(E-Z-C)<=((e+c/h)/L)*N*A*(1+2*u^2+2*u*(1+v))"
                + "+Cpair(N,q)*V(N,b)/L. The mean is exactly "
                + "C=A/(2*L)*(R(q)-U(N,q)+(M(q)+2)*u/h), where "
                + "R(q)=sum(1<=d<=q,mu(d)*log(h/d))+2*log h and "
                + "U(N,q)=sum(1<=d<=q,mu(d)*log(N/d)/d). The full first moment B remains "
                + "in the underlying fractional-kernel decomposition, without moment cancellation. "
                + "Every Mobius index, the literal +2 and the exact -2*K(h)/L payment remain. "
                + "At q=0 the low error and Cpair are exactly zero and C=A; q=1,2,5 have "
                + "no internal pairs, the formula reaches q=N-2, and e=0 or c=0 remain allowed. "
                + "The full-positive clause consumes the same signed low estimate through the "
                + "original transfer_of_low_bound supplier. Full RH, signed MAIN "
                + "and strict Robin for every n>5040 remain open."))));

    private static Formula Naturals => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb,Grp(F.Id("R")));
    private static Formula SavingFormula()
    {
        var n=F.Id("N"); var q=F.Id("q");
        return Disp(Seq(Forall,Sp,n,Comma,q,InMacro,Sp,Naturals,Comma,
            D(3),Le,Sp,n,Land,Sp,D(6),Le,Sp,q,Land,Sp,q,Le,Sp,n,Minus,D(2),Rightarrow,Sp,
            Call("Cpair",n,q),Lt,Sp,Call("Csep",n,q)));
    }
    private static Formula TransferFormula()
    {
        var n=F.Id("N"); var q=F.Id("q"); var b=F.Id("b"); var f=F.Id("F");
        var e=F.Id("e"); var c=F.Id("c"); var m=F.Id("m"); var k=F.Id("k");
        Formula h=Seq(Open,q,Plus,D(1),Close);
        Formula u=Call("log",new Formula.Fraction(n,h));
        Formula v=Call("log",new Formula.Fraction(Seq(D(2),Cdot,Sp,n),h));
        Formula budget=Seq(new Formula.Fraction(Seq(e,Plus,new Formula.Fraction(c,h)),Call("log",n)),
            Cdot,Sp,n,Cdot,Sp,Call("A",n,b),Cdot,Sp,Open,D(1),Plus,
            D(2),Cdot,Sp,new Formula.Power(u,D(2)),Plus,D(2),Cdot,Sp,u,Cdot,Sp,
            Open,D(1),Plus,v,Close,Close,Plus,
            new Formula.Fraction(Seq(Call("Cpair",n,q),Cdot,Sp,Call("V",n,b)),Call("log",n)));
        Formula low=Seq(Lvert,Sp,Call("lowError",n,q,b),Rvert,Sp,Le,Sp,
            new Formula.Fraction(Seq(Call("Cpair",n,q),Cdot,Sp,Call("V",n,b)),Call("log",n)));
        Formula high=Seq(Forall,Sp,f,InMacro,Sp,new Formula.Power(Reals,Naturals),Comma,
            Forall,Sp,e,Comma,c,InMacro,Sp,Reals,Comma,
            D(0),Le,Sp,e,Land,Sp,D(0),Le,Sp,c,Land,Sp,
            Open,Forall,Sp,m,InMacro,Sp,Naturals,Comma,n,Le,Sp,m,Lt,Sp,
            D(2),Cdot,Sp,n,Rightarrow,Sp,D(0),Le,Sp,Call("b",m),Close,Land,Sp,
            Open,Forall,Sp,k,InMacro,Sp,Naturals,Comma,h,Le,Sp,k,Lt,Sp,n,
            Rightarrow,Sp,Lvert,Sp,Call("F",k),Minus,Call("M",k),Rvert,Sp,
            Le,Sp,e,Cdot,Sp,k,Plus,c,Close,Rightarrow,Sp,
            Lvert,Sp,Call("E",n,b),Minus,Call("Z",n,q,b,f),Minus,Call("C",n,q,b),Rvert,Sp,Le,Sp,budget);
        return Disp(Seq(Forall,Sp,n,Comma,q,InMacro,Sp,Naturals,Comma,
            Forall,Sp,b,InMacro,Sp,new Formula.Power(Reals,Naturals),Comma,
            D(3),Le,Sp,n,Land,Sp,q,Le,Sp,n,Minus,D(2),Rightarrow,Sp,
            Open,low,Close,Land,Sp,Open,high,Close));
    }
}
