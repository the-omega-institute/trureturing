using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class NativeBorelFiniteProductsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula f=F.Id("F"), g=F.Id("G"), q=F.Id("Q"), n=F.Id("n"), sub=F.Id("hsub");
        Formula m=Call("doob",f,g);
        Formula finiteLaw=Call("finiteProduct",Call("nuP",f),m,n);
        Formula finitePrefix=Call("finitePrefix",Call("killedTrajectory",f,m,sub),n);
        Formula originalPrefix=Call("finitePrefix",Call("originalTrajectory",f),n);
        Formula finiteStatement=Seq(Forall,Sp,f,Colon,Sp,F.Id("CommonFlow"),Comma,Sp,
            Exists,Sp,g,Subset,Sp,F.Id("PDescriptor"),Comma,Sp,
            Exists,Sp,sub,Colon,Sp,Call("Subprobability",m),Comma,Sp,
            Call("MeasurableSet",g),Land,Sp,Call("AE",Call("nuP",f),q,Seq(q,InMacro,Sp,g)),
            Land,Sp,Forall,Sp,n,Colon,Sp,F.Id("Nat"),Comma,Sp,
            Call("restrict",finitePrefix,Call("allLive",n)),Eq,
                Call("map",finiteLaw,Call("includePrefix",n)),Land,Sp,
            finiteLaw,Eq,Call("withDensity",originalPrefix,Call("finiteDensity",f,m,n)),Land,Sp,
            Call("AbsolutelyContinuous",finiteLaw,originalPrefix));
        return DocumentDefinition.Create(ScribeNode.Create("Finite killed products on the original flow",
            H("The unweighted finite product"),Blocks(
                Describe.Lean(DescribeId.Create("common-flow-finite-product"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.common_flow_finite_product"),
                    H("Surviving prefixes and row densities"),StatementSource.FromAuthor(Disp(finiteStatement)),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("finiteProduct(mu,K,n) is the actual unnormalized kernel product on the complete finite history of n+1 states. It starts with mu at time zero, and each extension appends the actual K row at the last state by a composition-product. finitePrefix(mu,n) maps a full path measure to its coordinates indexed by Fin(n+1). allLive(n) requires every one of those coordinates to differ from the cemetery state; includePrefix(n) applies the live inclusion to every original coordinate.")),
                    Paragraph(Text("For the original Doob kernel M, restricting its lawful cemetery prefix to allLive gives the included finiteProduct(nuP,M,n). There is no terminal survival weight in this equality. The same finite M measure equals the original C prefix weighted by finiteDensity(F,M,n), the product over i=0,...,n-1 of the jointly measurable row Radon-Nikodym derivative M/C at the actual adjacent states. The extension proof uses the same preceding history at each step. This earns absolute continuity on each finite prefix; the complete immortal-law absolute continuity is supplied by the separate full-path identity."))),DescribeRole.Theorem))));
    }
}
