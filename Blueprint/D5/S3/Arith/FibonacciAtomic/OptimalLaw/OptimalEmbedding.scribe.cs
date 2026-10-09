using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.OptimalLaw;

internal sealed class OptimalEmbeddingDocument : IScribeDocumentDefinition
{
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, InMacro, Sp, type, Comma, Sp, body);

    public DocumentDefinition Create()
    {
        var real = Seq(Mathbb, Grp(F.Id("R"))); var nat = Seq(Mathbb, Grp(F.Id("N")));
        var m=F.Id("m"); var p=F.Id("p"); var k=F.Id("k"); var i=F.Id("i");
        var sigma=F.Id("sigma"); var gamma=F.Id("gamma");
        var args=Seq(m,Comma,p,Comma,k);
        var embedding=Seq(Exists,Sp,sigma,Sp,InMacro,Sp,Call("Perm",Call("Fin",m)),Comma,Sp,
            Exists,Sp,gamma,Sp,InMacro,Sp,Call("RootPath",m),Comma,Sp,
            Open,Forall,Sp,i,Sp,InMacro,Sp,Call("Fin",m),Comma,Sp,
                Equal(Call("probability",Seq(gamma,Comma,i)),Call("p",Call("sigma",i))),Close,
            Sp,Land,Sp,Equal(Call("anchorMass",gamma),Call("p",k)),Sp,Land,Sp,
            Equal(Call("pathCost",gamma),Call("L",p)));
        var statement=All("m", nat, All("p", Call("RealVector", m), All("k", Call("Fin", m), Seq(Call("Optimizer",args),Sp,To,Sp,Call("HasOptimalEmbedding",args)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "One fixed permutation represents every attaining real law by a legal triangular path with exact mass and cost.",
            H("Optimal Laws Embed in the Triangular Graph"), Blocks(
                Paragraph(Text("RealVector(m) denotes the real functions on Fin m. The natural label count m is at least two. A law p is a strictly positive real vector on Fin m with total mass one. Optimizer(m,p,k) additionally requires p(k)<=p(i) for every i and L(p)/p(k)=alpha(m), where L is the convergent dyadic floor-residual cost and alpha is the full-real infimum. A triangular state (r,e) has 0<e, r<e, and e<=m. A one action requires e<=2r and has successor (2r-e,e). A zero action with h departures requires 2r<e and h<=2r, and has successor (2r-h,e-h). RootPath(m) starts at (1,m) and satisfies these bounds and successor conditions at every natural depth.")),
                Describe.Lean(DescribeId.Create("has-optimal-embedding"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/OptimalEmbedding.HasOptimalEmbedding"),
                    H("Joint probability, anchor and cost preservation"), StatementSource.FromAuthor(Disp(
                        All("m", nat, All("p", Call("RealVector", m), All("k", Call("Fin", m), Seq(Call("HasOptimalEmbedding",args),Sp,Iff,Sp,embedding)))))),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("The permutation is fixed for all depths. The path's label digits define probability by the sum of digit(i,d)/2^(d+1). Its anchor mass uses the permanent anchor digit in the same series. Its path cost is the sum of r(d)/2^d. All three equalities refer to this single path."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("result"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLaw/OptimalEmbedding.result"),
                    H("Every attaining real law has this embedding"), StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Strict rounding identifies the departure depth of each larger coordinate. Minimum coordinates are retained forever; every other coordinate remains until its least terminating depth. The floor residual is the sum of the retained fractional tails. A common anchor one digit forces e<=2r. A zero anchor digit forces 2r<e, because the anchor itself supplies one strict half-tail inequality. The retained-label count and residual recurrence jointly give every legal successor.")),
                        Paragraph(Text("Sort the departure depths in descending order once, treating permanent labels as having infinite departure time. Permanent labels come first, and every retained set becomes an initial interval. The resulting legal path has precisely the original floor digits in that fixed order. Equality of all dyadic floor prefixes recovers the real probabilities. The minimum and cost identities then follow from the same path and the triangular normalization theorem. No rationality or computability restriction is placed on the input law.")))))));
    }
}
