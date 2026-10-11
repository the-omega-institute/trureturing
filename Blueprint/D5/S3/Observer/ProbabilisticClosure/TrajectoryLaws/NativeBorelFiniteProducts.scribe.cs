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
        Formula finiteC=Call("finiteProduct",Call("nuP",f),Call("C",f),n);
        Formula finiteM=Call("finiteProduct",Call("nuP",f),m,n);
        Formula w=F.Id("w"), i=F.Id("i");
        Formula h0=Call("threeStepAverage",f,Call("at",w,D(0)));
        Formula hn=Call("threeStepAverage",f,Call("at",w,Call("last",n)));
        Formula factor=Call("ofReal",Seq(D(1),Plus,
            Div(Multiply(D(2,5),Call("excess",Call("at",w,Call("castSucc",i)))),D(9))));
        Formula r=F.Id("R");
        Formula rowDerivative=Call("rowDerivative",m,Call("C",f),q,r);
        Formula rowDistortion=Multiply(Multiply(Call("inv",Call("threeStepAverage",f,q)),
            Call("threeStepAverage",f,r)),Call("ofReal",Seq(D(1),Plus,
                Div(Multiply(D(2,5),Call("excess",q)),D(9)))));
        Formula distortion=Multiply(Multiply(Call("inv",h0),hn),
            Call("prod",i,Call("Fin",n),factor));
        Formula finiteStatement=Seq(Forall,Sp,f,Colon,Sp,F.Id("CommonFlow"),Comma,Sp,
            Exists,Sp,g,Subset,Sp,F.Id("PDescriptor"),Comma,Sp,
            Exists,Sp,sub,Colon,Sp,Call("Subprobability",m),Comma,Sp,
            Call("MeasurableSet",g),Land,Sp,Call("AE",Call("nuP",f),q,Seq(q,InMacro,Sp,g)),
            Land,Sp,Call("AE",Call("nuP",f),q,Call("AE",Call("CRow",f,q),F.Id("R"),
                Le(rowDerivative,rowDistortion))),
            Land,Sp,Forall,Sp,n,Colon,Sp,F.Id("Nat"),Comma,Sp,
            Call("restrict",finitePrefix,Call("allLive",n)),Eq,
                Call("map",finiteLaw,Call("includePrefix",n)),Land,Sp,
            finiteLaw,Eq,Call("withDensity",originalPrefix,Call("finiteDensity",f,m,n)),Land,Sp,
            Call("AbsolutelyContinuous",finiteLaw,originalPrefix));
        Formula rnStatement=Seq(Forall,Sp,f,Colon,Sp,F.Id("CommonFlow"),Comma,Sp,
            Exists,Sp,g,Subset,Sp,F.Id("PDescriptor"),Comma,Sp,
            Exists,Sp,sub,Colon,Sp,Call("Subprobability",m),Comma,Sp,
            Call("MeasurableSet",g),Land,Sp,Call("AE",Call("nuP",f),q,Seq(q,InMacro,Sp,g)),Land,Sp,
            Call("AE",Call("nuP",f),q,Call("AE",Call("CRow",f,q),F.Id("R"),
                Le(rowDerivative,rowDistortion))),Land,Sp,
            Forall,Sp,n,Colon,Sp,F.Id("Nat"),Comma,Sp,
            Call("AE",finiteC,w,Le(Call("rnDeriv",finiteM,finiteC,w),distortion)));
        return DocumentDefinition.Create(ScribeNode.Create("Finite killed products on the original flow",
            H("The unweighted finite product"),Blocks(
                Describe.Lean(DescribeId.Create("snoc-measurable"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.snoc_measurable"),
                    H("Measurable finite-history extension"),StatementSource.FromAuthor(Disp(
                        All(Call("Measurable",Call("snocMap",F.Id("S"),F.Id("n"))),("S","MeasurableType"),("n","Nat")))),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("For every type S with its arbitrary measurable space and every natural n, snocMap(S,n) sends a pair (w,y) with w:Fin(n+1)->S and y:S to Fin.snoc(w,y):Fin(n+2)->S. Measurability is checked coordinatewise. This supplier is consumed in the actual finite product extension and trajectory shift proof."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("homogeneous-prefix-product"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.homogeneous_prefix_product"),
                    H("The actual homogeneous finite history"),StatementSource.FromAuthor(Disp(
                        All(Eqn(Call("finitePrefix",Call("homogeneousLaw",F.Id("mu"),F.Id("K")),F.Id("n")),
                                Call("finiteProduct",F.Id("mu"),F.Id("K"),F.Id("n"))),("S","MeasurableType"),("mu","ProbabilityMeasureS"),("K","MarkovKernelS"),("n","Nat")))),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("For every measurable type S, probability measure mu, Markov kernel K:S->S and n:Nat, the prefix pushforward of homogeneousLaw(mu,K) to Fin(n+1) equals finiteProduct(mu,K,n). The proof uses the original trajectory partial products and the exact measurable index equivalence. The same supplier identifies started and shifted original C histories."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("common-flow-finite-product"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.common_flow_finite_product"),
                    H("Surviving prefixes and row densities"),StatementSource.FromAuthor(Disp(finiteStatement)),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("finiteProduct(mu,K,n) is the actual unnormalized kernel product on the complete finite history of n+1 states. It starts with mu at time zero, and each extension appends the actual K row at the last state by a composition-product. finitePrefix(mu,n) maps a full path measure to its coordinates indexed by Fin(n+1). allLive(n) requires every one of those coordinates to differ from the cemetery state; includePrefix(n) applies the live inclusion to every original coordinate.")),
                    Paragraph(Text("For the original Doob kernel M, restricting its lawful cemetery prefix to allLive gives the included finiteProduct(nuP,M,n). There is no terminal survival weight in this equality. The same finite M measure equals the original C prefix weighted by finiteDensity(F,M,n), the product over i=0,...,n-1 of the jointly measurable row Radon-Nikodym derivative M/C at the actual adjacent states. The extension proof uses the same preceding history at each step. This earns absolute continuity on each finite prefix; the complete immortal-law absolute continuity is supplied by the separate full-path identity."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("common-flow-finite-history-rn-bound"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts.common_flow_finite_history_rn_bound"),
                    H("Finite-history h-ratio and excess bound"),StatementSource.FromAuthor(Disp(rnStatement)),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The row comparison is transported along the same stationary original C history. The product density is the exact Radon-Nikodym derivative of the all-live Doob product against the original finite C product, and telescoping the intermediate three-step averages yields h(X_n)/h(X_0) times the product of the original excess factors. Every horizon is retained, and terminal cancellation is made only on the transported conull carrier where h is finite and positive."))),DescribeRole.Theorem))));
    }
    private static Formula All(Formula body, params (string Name,string Type)[] xs) {
        for(int k=xs.Length-1;k>=0;k--) body=Seq(Forall,Sp,F.Id(xs[k].Name),Colon,Sp,F.Id(xs[k].Type),Comma,Sp,body);
        return body;
    }
    private static Formula Eqn(Formula a, Formula b) => Seq(a,Eq,b);
    private static Formula Le(Formula a, Formula b) => Seq(a,Leq,b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
}
