using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.OptimalLaw;

internal sealed class StrictRoundingDocument : IScribeDocumentDefinition
{
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, InMacro, Sp, type, Comma, Sp, body);

    public DocumentDefinition Create()
    {
        var real = Seq(Mathbb, Grp(F.Id("R"))); var nat = Seq(Mathbb, Grp(F.Id("N")));
        var x=F.Id("x"); var t=F.Id("t"); var d=F.Id("d"); var depth=F.Id("D"); var e=F.Id("E");
        var m=F.Id("m"); var p=F.Id("p"); var k=F.Id("k"); var i=F.Id("i");
        var grid=Call("OnGrid", Seq(x,Comma,depth));
        var floor=Call("F", Seq(t,Comma,depth));
        var rounded=new Formula.Fraction(Seq(floor,Sp,Plus,Sp,D(1)),new Formula.Power(D(2),depth));
        var strict=Seq(Exists,Sp,depth,Sp,InMacro,Sp,nat,Comma,Sp,D(1),Sp,Le,Sp,depth,Sp,Land,Sp,grid,Sp,Land,Sp,
            Open,Forall,Sp,d,Sp,Lt,Sp,depth,Comma,Sp,Neg,Sp,Call("OnGrid",Seq(x,Comma,d)),Close,
            Sp,Land,Sp,Equal(x,rounded));
        var gridUp=All("x", real, All("D", nat, All("E", nat, Seq(Open,depth,Sp,Le,Sp,e,Sp,Land,Sp,grid,Close,Sp,To,Sp,Call("OnGrid",Seq(x,Comma,e))))));
        var leastBit=All("x", real, All("D", nat, Seq(Call("LeastGrid",Seq(x,Comma,depth)),Sp,To,Sp,Equal(Call("b",Seq(x,Comma,depth)),D(1)))));
        var target=All("m", nat, All("p", Call("RealVector", m), All("k", Call("Fin", m), Seq(Call("Optimizer",Seq(m,Comma,p,Comma,k)),Sp,To,Sp,Call("StrictlyRoundedLaw",Seq(m,Comma,p,Comma,k))))));
        var q = F.Id("q"); var j = F.Id("j"); var s = F.Id("S"); var u = F.Id("u");
        var args = Seq(m, Comma, depth, Comma, p, Comma, q, Comma, j, Comma, s, Comma, t, Comma, u);
        var bit = Call("b", Seq(x, Comma, depth));
        var delta = new Formula.Fraction(D(1), new Formula.Power(D(2), depth));
        var prefix = All("x", real, All("D", nat, Seq(Open, D(1), Sp, Le, Sp, depth, Sp, Land, Sp, Equal(bit, D(1)), Close, Sp, To, Sp, All("d", nat, Seq(Open, d, Sp, Lt, Sp, depth, Close, Sp, To, Sp, Equal(Call("F", Seq(Seq(x, Sp, Minus, Sp, delta), Comma, d)), Call("F", Seq(x, Comma, d))))))));
        var impossible = All("m", nat, All("D", nat, All("p", Call("RealVector", m), All("q", Call("RealVector", m), All("j", Call("Fin", m), All("S", Call("Finset", Call("Fin", m)), All("t", real, All("u", real, Seq(Call("ExchangeHyp", args), Sp, To, Sp, Call("b", Seq(Call("p", j), Comma, depth)), Sp, Neq, Sp, D(1))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every atom above the minimum of an attaining real law has a least dyadic depth and strict rounding.",
            H("Strict Dyadic Rounding of Optimal Laws"), Blocks(
                Paragraph(Text("RealVector(m) denotes the real functions on Fin m. The parameter m is natural; p is a real vector on Fin m and k is an index of its least mass. Optimizer(m,p,k) means m>=2, every coordinate is positive, their sum is one, p(k)<=p(i) for every i, and L(p)/p(k)=alpha(m). The optimization domain includes every such real law. F(x,d) is floor(2^d x), L is its dyadic residual cost, and b(x,D)=F(x,D)-2F(x,D-1).")),
                Paragraph(Text("RealVector(m) is the space of real functions on Fin m. For real x and natural d, F(x,d) is the integer floor of 2^d x. The binary digit b(x,D) is F(x,D)-2F(x,D-1). All vectors below are indexed by Fin m. Write delta=2^(-D), R(p,d)=2^d-sum_i F(p(i),d), and L(p)=sum_d R(p,d)/2^d.")),
                Describe.Lean(DescribeId.Create("donor-prefix"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.donor_prefix"),
                    H("Coarser prefixes survive a donor debit"), StatementSource.FromAuthor(Disp(prefix)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("If the depth-D digit is one, subtracting one depth-D cylinder leaves every earlier floor prefix unchanged. Division of the depth-(D-1) floor by an integer power of two transports this equality to every coarser depth.")))),
                Paragraph(Text("ExchangeHyp(m,D,p,q,j,S,t,u) means: m>=2 and D>=1; p and q are nonnegative vectors of total mass one; q(j)=0; t>0 and u>0; for i in S both t<=p(i) and u<=q(i); for i outside S other than j, t+delta*u<=p(i); the donor satisfies t+delta*(1+u)<=p(j); L(p)=alpha(m)*t and L(q)<alpha(m)*u. Here alpha is the infimum of L divided by the smallest coordinate over all positive normalized real laws.")),
                H("An optimal law has no profitable donor leaf"), Disp(impossible),
                Paragraph(Text("Form P(i)=p(i)+delta*q(i)-delta times the indicator of i=j. Coarser residuals do not increase. At depth D+n the residual is at most R(p,D+n)+R(q,n). Splitting the convergent series into its head and shifted tail gives L(P)<=L(p)+delta*L(q). Simultaneously every coordinate of P is at least t+delta*u. The defining lower bound for alpha(m) then contradicts the strict improvement of the same modified law. The classical dyadic cost expression is recalled by Lumbroso; the common-law comparison is the stated additional relation.")),
                Describe.Lean(DescribeId.Create("dyadic-strict-round"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.DyadicStrictRound"),
                    H("The least terminating strict round"), StatementSource.FromAuthor(Disp(
                        All("x", real, All("t", real, Seq(Call("DyadicStrictRound",Seq(x,Comma,t)),Sp,Iff,Sp,strict))))),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("OnGrid(x,D) means that 2^D x is an integer. The displayed depth is positive, is the least depth with this property, and rounds t strictly upward by one integer unit at that depth."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("strictly-rounded-law"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.StrictlyRoundedLaw"),
                    H("Every larger coordinate has this form"), StatementSource.FromAuthor(Disp(
                        All("m", nat, All("p", Call("RealVector", m), All("k", Call("Fin", m),
                        Seq(Call("StrictlyRoundedLaw",Seq(m,Comma,p,Comma,k)),Sp,Iff,Sp,
                            All("i", Call("Fin", m), Seq(Call("p",k),Sp,Lt,Sp,Call("p",i),Sp,To,Sp,
                            Call("DyadicStrictRound",Seq(Call("p",i),Comma,Call("p",k))))))))))),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The requirement applies to every coordinate strictly above the least mass."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("round"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.round"),
                    H("Strict upper dyadic round"), StatementSource.FromAuthor(Disp(All("t", real, All("D", nat, Equal(Call("round",Seq(t,Comma,depth)),rounded))))),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("One is added even when the scaled argument is already integral."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("on-grid"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.OnGrid"),
                    H("Dyadic grid membership"), StatementSource.FromAuthor(Disp(
                        All("x", real, All("D", nat, Seq(grid,Sp,Iff,Sp,Exists,Sp,F.Id("z"),Sp,InMacro,Sp,Mathbb,Grp(F.Id("Z")),Comma,Sp,
                            Equal(Seq(new Formula.Power(D(2),depth),Sp,x),F.Id("z"))))))),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("This predicate allows any real x and natural depth, including depth zero."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("grid-up"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.grid_up"),
                    H("Grid membership at finer depths"), StatementSource.FromAuthor(Disp(gridUp)),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Multiplying the integer numerator by 2^(E-D) preserves grid membership.")))),
                Paragraph(Text("LeastGrid(x,D) means D>=1, OnGrid(x,D), and not OnGrid(x,d) for every natural d<D.")),
                Describe.Lean(DescribeId.Create("least-grid-bit"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.least_grid_bit"),
                    H("The final terminating digit is one"), StatementSource.FromAuthor(Disp(leastBit)),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The floor carry is zero or one. A zero carry at the least terminating depth would place x on the preceding grid.")))),
                Describe.Lean(DescribeId.Create("result"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.result"),
                    H("Strict rounding for every attaining real law"), StatementSource.FromAuthor(Disp(target)),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg")), Blocks(
                        Paragraph(Text("A nonterminating larger coordinate has arbitrarily deep one digits. A smaller-label optimal receiver, extended by zero to the other labels, can exploit such a digit through a profitable leaf exchange. This contradicts optimality, so every larger coordinate terminates.")),
                        Paragraph(Text("Choose a putative failure of strict rounding with greatest least terminating depth. The integer residual and the common floor prefixes on the receiver set leave enough fractional margin for another profitable exchange. This rules out the failure. All comparisons concern one actual law and its modified receiver law.")))))));
    }
}
