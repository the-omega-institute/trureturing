using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.OptimalLaw;

internal sealed class RationalPriceDocument : IScribeDocumentDefinition
{
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, InMacro, Sp, type, Comma, Sp, body);

    public DocumentDefinition Create()
    {
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var m=F.Id("m"); var p=F.Id("p"); var a=F.Id("A"); var x=F.Id("x"); var v=F.Id("v");
        var rational=Seq(Mathbb,Grp(F.Id("Q"))); var real=Seq(Mathbb,Grp(F.Id("R")));
        var alpha=Call("alpha",m); var value=Call("W",Seq(x,Comma,m,Comma,D(1)));
        var cost=All("m", nat, All("p", Call("RealVector", m), Seq(
            Call("NonnegativeRationalLaw",Seq(m,Comma,p)),Sp,To,Sp,
            Exists,Sp,v,Sp,InMacro,Sp,rational,Comma,Sp,Equal(Call("realCast",v),Call("L",p)))));
        var price=All("m", nat, Seq(Open,D(2),Sp,Le,Sp,m,Close,Sp,To,Sp,
            Exists,Sp,a,Sp,InMacro,Sp,rational,Comma,Sp,D(0),Sp,Lt,Sp,a,Sp,Land,Sp,
            Equal(Call("realCast",a),alpha)));
        var zero=All("m", nat, Seq(Open,D(2),Sp,Le,Sp,m,Close,Sp,To,Sp,
            All("x", real, Seq(Open,Equal(value,D(0)),Sp,Iff,Sp,Equal(x,alpha),Close))));
        var full=All("m", nat, Seq(Open,D(2),Sp,Le,Sp,m,Close,Sp,To,Sp,
            Exists,Sp,a,Sp,InMacro,Sp,rational,Comma,Sp,D(0),Sp,Lt,Sp,a,Sp,Land,Sp,
            Equal(Call("realCast",a),alpha),Sp,Land,Sp,Open,
            All("x", real, Seq(Open,Equal(value,D(0)),Sp,Iff,Sp,Equal(x,Call("realCast",a)),Close)),Close));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The unrestricted real-law optimum is positive rational and is the unique real zero of the triangular root value.",
            H("The Unique Positive Rational Price"), Blocks(
                Paragraph(Text("RealVector(m) is the space of real functions on Fin m. For natural m, L(p) is the sum over natural d of (2^d-sum_i floor(2^d p(i)))/2^d. The quantity alpha(m) is the infimum of L(p)/p(k) over all strictly positive normalized real vectors p on Fin m and every index k of a least coordinate. W(x,m,1) is the infimum of C-x*t over all legal triangular paths starting at residual one with m retained labels. Here C is the sum of the path residuals divided by 2^d and t is the anchor-digit mass. realCast denotes the canonical inclusion of rational numbers into the reals.")),
                Paragraph(Text("NonnegativeRationalLaw(m,p) means p has real coordinates indexed by Fin m, every coordinate is nonnegative, their sum is one, and for every i there exists a rational q whose real cast equals p(i).")),
                Describe.Lean(DescribeId.Create("rational-law-cost"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.rational_law_cost"),
                    H("Rational coordinates give rational dyadic cost"), StatementSource.FromAuthor(Disp(cost)),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg")), Blocks(
                        Paragraph(Text("For one rational coordinate, denominator residues take only finitely many values. A collision gives equal complete residue tails. Two prefix-plus-discounted-tail identities solve the common discounted series as a rational number. Summing these coordinate costs and using normalization gives the rational law cost. The denominator-residue method is classical; the displayed finite-law statement combines it with the floor cost expression.")))),
                Describe.Lean(DescribeId.Create("rational-alpha"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.rational_alpha"),
                    H("A positive rational representative of the full-real optimum"), StatementSource.FromAuthor(Disp(price)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Choose an attaining law in the full real domain. Strict rounding makes every coordinate above its minimum dyadic. Normalization expresses the common minimum as one minus the sum of the larger rational coordinates, divided by the number of minimum coordinates. Thus this same attaining law has rational cost and rational positive minimum. Their quotient equals alpha(m), which is positive by the label-count lower bound.")))),
                Describe.Lean(DescribeId.Create("zero-iff-alpha"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.zero_iff_alpha"),
                    H("The zero over every real price"), StatementSource.FromAuthor(Disp(zero)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Every triangular path satisfies C>=alpha(m)*t, and its root cost is at least one. The reverse embedding of an attaining law supplies a positive-anchor path with equality. Hence W vanishes at alpha. If a smaller price had value zero, a path attaining that value would contradict either the positive-anchor lower bound or the root cost bound. At a larger price the embedded optimizer has strictly negative value. These arguments quantify over every real x.")))),
                Describe.Lean(DescribeId.Create("result"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.result"),
                    H("Positive rational price and exact unrestricted equality"), StatementSource.FromAuthor(Disp(full)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("The same rational A is positive, has real value alpha(m), and is the unique zero of W(x,m,1). Rationality is derived from an attaining law, while uniqueness uses its cost-preserving triangular embedding. This does not assert a finite rational affine family for the entire price function, a finite maximal stopping depth, or any computational restriction on the optimization domain.")))))));
    }
}
