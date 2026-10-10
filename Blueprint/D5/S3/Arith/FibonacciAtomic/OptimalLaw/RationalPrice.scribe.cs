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
        var k=F.Id("k"); var i=F.Id("i");
        var sigma=F.Id("sigma"); var gamma=F.Id("gamma");
        var args=Seq(m,Comma,p,Comma,k);
        var embedding=Seq(Exists,Sp,sigma,Sp,InMacro,Sp,Call("Perm",Call("Fin",m)),Comma,Sp,
            Exists,Sp,gamma,Sp,InMacro,Sp,Call("RootPath",m),Comma,Sp,
            Open,Forall,Sp,i,Sp,InMacro,Sp,Call("Fin",m),Comma,Sp,
                Equal(Call("probability",Seq(gamma,Comma,i)),Call("p",Call("sigma",i))),Close,
            Sp,Land,Sp,Equal(Call("anchorMass",gamma),Call("p",k)),Sp,Land,Sp,
            Equal(Call("pathCost",gamma),Call("L",p)));
        var embeddingStatement=All("m", nat, All("p", Call("RealVector", m), All("k", Call("Fin", m), Seq(Call("Optimizer",args),Sp,To,Sp,Call("HasOptimalEmbedding",args)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The unrestricted real-law optimum is positive rational and is the unique real zero of the triangular root value.",
            H("The Unique Positive Rational Price"), Blocks(
                Paragraph(Text("RealVector(m) is the space of real functions on Fin m. For natural m, L(p) is the sum over natural d of (2^d-sum_i floor(2^d p(i)))/2^d. The quantity alpha(m) is the infimum of L(p)/p(k) over all strictly positive normalized real vectors p on Fin m and every index k of a least coordinate. W(x,m,1) is the infimum of C-x*t over all legal triangular paths starting at residual one with m retained labels. Here C is the sum of the path residuals divided by 2^d and t is the anchor-digit mass. realCast denotes the canonical inclusion of rational numbers into the reals.")),
                Paragraph(Text("NonnegativeRationalLaw(m,p) means p has real coordinates indexed by Fin m, every coordinate is nonnegative, their sum is one, and for every i there exists a rational q whose real cast equals p(i).")),
                Paragraph(Text("RealVector(m) denotes the real functions on Fin m. The natural label count m is at least two. A law p is a strictly positive real vector on Fin m with total mass one. Optimizer(m,p,k) additionally requires p(k)<=p(i) for every i and L(p)/p(k)=alpha(m), where L is the convergent dyadic floor-residual cost and alpha is the full-real infimum. A triangular state (r,e) has 0<e, r<e, and e<=m. A one action requires e<=2r and has successor (2r-e,e). A zero action with h departures requires 2r<e and h<=2r, and has successor (2r-h,e-h). RootPath(m) starts at (1,m) and satisfies these bounds and successor conditions at every natural depth.")),
                Describe.Lean(DescribeId.Create("has-optimal-embedding"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.HasOptimalEmbedding"),
                    H("Joint probability, anchor and cost preservation"), StatementSource.FromAuthor(Disp(
                        All("m", nat, All("p", Call("RealVector", m), All("k", Call("Fin", m), Seq(Call("HasOptimalEmbedding",args),Sp,Iff,Sp,embedding)))))),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("The permutation is fixed for all depths. The path's label digits define probability by the sum of digit(i,d)/2^(d+1). Its anchor mass uses the permanent anchor digit in the same series. Its path cost is the sum of r(d)/2^d. All three equalities refer to this single path."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("embedding-result"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice.embedding_result"),
                    H("Every attaining real law has this embedding"), StatementSource.FromAuthor(Disp(embeddingStatement)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Strict rounding identifies the departure depth of each larger coordinate. Minimum coordinates are retained forever; every other coordinate remains until its least terminating depth. The floor residual is the sum of the retained fractional tails. A common anchor one digit forces e<=2r. A zero anchor digit forces 2r<e, because the anchor itself supplies one strict half-tail inequality. The retained-label count and residual recurrence jointly give every legal successor.")),
                        Paragraph(Text("Sort the departure depths in descending order once, treating permanent labels as having infinite departure time. Permanent labels come first, and every retained set becomes an initial interval. The resulting legal path has precisely the original floor digits in that fixed order. Equality of all dyadic floor prefixes recovers the real probabilities. The minimum and cost identities then follow from the same path and the triangular normalization theorem. No rationality or computability restriction is placed on the input law.")))),
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
