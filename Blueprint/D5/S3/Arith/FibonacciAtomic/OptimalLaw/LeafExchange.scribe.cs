using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.OptimalLaw;

internal sealed class LeafExchangeDocument : IScribeDocumentDefinition
{
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, InMacro, Sp, type, Comma, Sp, body);

    public DocumentDefinition Create()
    {
        var real = Seq(Mathbb, Grp(F.Id("R"))); var nat = Seq(Mathbb, Grp(F.Id("N")));
        var x = F.Id("x"); var d = F.Id("d"); var depth = F.Id("D");
        var m = F.Id("m"); var p = F.Id("p"); var q = F.Id("q");
        var j = F.Id("j"); var s = F.Id("S"); var t = F.Id("t"); var u = F.Id("u");
        var args = Seq(m, Comma, depth, Comma, p, Comma, q, Comma, j, Comma, s, Comma, t, Comma, u);
        var bit = Call("b", Seq(x, Comma, depth));
        var delta = new Formula.Fraction(D(1), new Formula.Power(D(2), depth));
        var prefix = All("x", real, All("D", nat, Seq(Open, D(1), Sp, Le, Sp, depth, Sp, Land, Sp, Equal(bit, D(1)), Close, Sp, To, Sp, All("d", nat, Seq(Open, d, Sp, Lt, Sp, depth, Close, Sp, To, Sp, Equal(Call("F", Seq(Seq(x, Sp, Minus, Sp, delta), Comma, d)), Call("F", Seq(x, Comma, d))))))));
        var impossible = All("m", nat, All("D", nat, All("p", Call("RealVector", m), All("q", Call("RealVector", m), All("j", Call("Fin", m), All("S", Call("Finset", Call("Fin", m)), All("t", real, All("u", real, Seq(Call("ExchangeHyp", args), Sp, To, Sp, Call("b", Seq(Call("p", j), Comma, depth)), Sp, Neq, Sp, D(1))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "A dyadic donor and a cheaper receiver produce one common law with controlled residuals.",
            H("Dyadic Leaf Exchange"), Blocks(
                Paragraph(Text("RealVector(m) is the space of real functions on Fin m. For real x and natural d, F(x,d) is the integer floor of 2^d x. The binary digit b(x,D) is F(x,D)-2F(x,D-1). All vectors below are indexed by Fin m. Write delta=2^(-D), R(p,d)=2^d-sum_i F(p(i),d), and L(p)=sum_d R(p,d)/2^d.")),
                Describe.Lean(DescribeId.Create("donor-prefix"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/LeafExchange.donor_prefix"),
                    H("Coarser prefixes survive a donor debit"), StatementSource.FromAuthor(Disp(prefix)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("If the depth-D digit is one, subtracting one depth-D cylinder leaves every earlier floor prefix unchanged. Division of the depth-(D-1) floor by an integer power of two transports this equality to every coarser depth.")))),
                Paragraph(Text("ExchangeHyp(m,D,p,q,j,S,t,u) means: m>=2 and D>=1; p and q are nonnegative vectors of total mass one; q(j)=0; t>0 and u>0; for i in S both t<=p(i) and u<=q(i); for i outside S other than j, t+delta*u<=p(i); the donor satisfies t+delta*(1+u)<=p(j); L(p)=alpha(m)*t and L(q)<alpha(m)*u. Here alpha is the infimum of L divided by the smallest coordinate over all positive normalized real laws.")),
                Describe.Lean(DescribeId.Create("profitable-leaf-impossible"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/LeafExchange.profitable_leaf_impossible"),
                    H("An optimal law has no profitable donor leaf"), StatementSource.FromAuthor(Disp(impossible)),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg")), Blocks(
                        Paragraph(Text("Form P(i)=p(i)+delta*q(i)-delta times the indicator of i=j. Coarser residuals do not increase. At depth D+n the residual is at most R(p,D+n)+R(q,n). Splitting the convergent series into its head and shifted tail gives L(P)<=L(p)+delta*L(q). Simultaneously every coordinate of P is at least t+delta*u. The defining lower bound for alpha(m) then contradicts the strict improvement of the same modified law. The classical dyadic cost expression is recalled by Lumbroso; the common-law comparison is the stated additional relation.")))))));
    }
}
