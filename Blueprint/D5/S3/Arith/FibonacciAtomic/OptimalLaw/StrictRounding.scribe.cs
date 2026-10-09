using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.OptimalLaw;

internal sealed class StrictRoundingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var x=F.Id("x"); var t=F.Id("t"); var d=F.Id("d"); var depth=F.Id("D"); var e=F.Id("E");
        var m=F.Id("m"); var p=F.Id("p"); var k=F.Id("k"); var i=F.Id("i");
        var grid=Call("OnGrid", Seq(x,Comma,depth));
        var floor=Call("F", Seq(t,Comma,depth));
        var rounded=new Formula.Fraction(Seq(floor,Sp,Plus,Sp,D(1)),new Formula.Power(D(2),depth));
        var strict=Seq(Exists,Sp,depth,Comma,Sp,D(1),Sp,Le,Sp,depth,Sp,Land,Sp,grid,Sp,Land,Sp,
            Open,Forall,Sp,d,Sp,Lt,Sp,depth,Comma,Sp,Neg,Call("OnGrid",Seq(x,Comma,d)),Close,
            Sp,Land,Sp,Equal(x,rounded));
        var gridUp=Seq(Forall,Sp,x,Comma,Sp,depth,Comma,Sp,e,Comma,Sp,
            Open,depth,Sp,Le,Sp,e,Sp,Land,Sp,grid,Close,Sp,To,Sp,Call("OnGrid",Seq(x,Comma,e)));
        var leastBit=Seq(Forall,Sp,x,Comma,Sp,depth,Comma,Sp,
            Call("LeastGrid",Seq(x,Comma,depth)),Sp,To,Sp,Equal(Call("b",Seq(x,Comma,depth)),D(1)));
        var target=Seq(Forall,Sp,m,Comma,Sp,p,Comma,Sp,k,Comma,Sp,
            Call("Optimizer",Seq(m,Comma,p,Comma,k)),Sp,To,Sp,
            Call("StrictlyRoundedLaw",Seq(m,Comma,p,Comma,k)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every atom above the minimum of an attaining real law has a least dyadic depth and strict rounding.",
            H("Strict Dyadic Rounding of Optimal Laws"), Blocks(
                Paragraph(Text("The parameter m is natural; p is a real vector on Fin m and k is an index of its least mass. Optimizer(m,p,k) means m>=2, every coordinate is positive, their sum is one, p(k)<=p(i) for every i, and L(p)/p(k)=alpha(m). The optimization domain includes every such real law. F(x,d) is floor(2^d x), L is its dyadic residual cost, and b(x,D)=F(x,D)-2F(x,D-1).")),
                Describe.Lean(DescribeId.Create("dyadic-strict-round"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.DyadicStrictRound"),
                    H("The least terminating strict round"), StatementSource.FromAuthor(Disp(
                        Seq(Call("DyadicStrictRound",Seq(x,Comma,t)),Sp,Iff,Sp,strict))),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("OnGrid(x,D) means that 2^D x is an integer. The displayed depth is positive, is the least depth with this property, and rounds t strictly upward by one integer unit at that depth."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("strictly-rounded-law"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.StrictlyRoundedLaw"),
                    H("Every larger coordinate has this form"), StatementSource.FromAuthor(Disp(
                        Seq(Call("StrictlyRoundedLaw",Seq(m,Comma,p,Comma,k)),Sp,Iff,Sp,Forall,Sp,i,Comma,Sp,
                            Call("p",k),Sp,Lt,Sp,Call("p",i),Sp,To,Sp,
                            Call("DyadicStrictRound",Seq(Call("p",i),Comma,Call("p",k)))))),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The requirement applies to every coordinate strictly above the least mass."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("round"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.round"),
                    H("Strict upper dyadic round"), StatementSource.FromAuthor(Disp(Equal(Call("round",Seq(t,Comma,depth)),rounded))),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("One is added even when the scaled argument is already integral."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("on-grid"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/StrictRounding.OnGrid"),
                    H("Dyadic grid membership"), StatementSource.FromAuthor(Disp(
                        Seq(grid,Sp,Iff,Sp,Exists,Sp,F.Id("z"),Sp,InMacro,Sp,Mathbb,Grp(F.Id("Z")),Comma,Sp,
                            Equal(Seq(new Formula.Power(D(2),depth),Sp,x),F.Id("z"))))),
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
