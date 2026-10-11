using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class NativeBorelEndpointIdentificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula f=F.Id("F"), q=F.Id("Q"), r=F.Id("R"), g=F.Id("G"), n=F.Id("n");
        Formula core=Seq(Call("CoreAt",f,q),Land,Sp,
            Call("AE",Call("CRow",f,q),r,Seq(r,InMacro,Sp,g,Land,Sp,
                Call("sixthFunctional",f,r),Eq,Call("sixthFunctional",f,q))));
        Formula baseCore=Seq(Call("MeasurableSet",g),Land,Sp,
            Call("AE",Call("nuP",f),q,Seq(q,InMacro,Sp,g)),Land,Sp,
            Forall,Sp,q,InMacro,Sp,g,Comma,Sp,core);
        Formula native=Call("nativeEndpoint",F.Id("p"),F.Id("true"));
        Formula target=Call("ite",Seq(q,Eq,native),Call("endpointCompletion"),D(0));
        Formula survival=Seq(Exists,Sp,g,Subset,Sp,F.Id("PDescriptor"),Comma,Sp,
            Call("MeasurableSet",g),Land,Sp,Call("AE",Call("nuP",f),q,Seq(q,InMacro,Sp,g)),
            Land,Sp,Open,Forall,Sp,q,InMacro,Sp,g,Comma,Sp,core,Close,Land,Sp,
            Forall,Sp,q,InMacro,Sp,g,Comma,Sp,Open,Call("q",f,q),Neq,Sp,D(0),Close,
            Iff,Sp,q,Eq,native);
        Formula density=Seq(Call("q",f,q),Eq,target,Land,Sp,
            Fraction(Call("q",f,q),Call("threeStepAverage",f,q)),Eq,
            Call("ite",Seq(q,Eq,native),D(1),D(0)));
        Formula ratio=Fraction(Call("coordinate",n,D(1),q),Pow(Call("endpointRate"),n));
        Formula pointwise=Call("AE",Call("nuP",f),q,
            Call("Tendsto",Call("sequence",n,ratio),F.Id("atTop"),Call("nhds",target)));
        Formula averaged=Call("Tendsto",Call("sequence",n,
            Fraction(Call("lintegral",Call("nuP",f),q,Call("coordinate",n,D(1),q)),
                Pow(Call("endpointRate"),n))),F.Id("atTop"),
            Call("nhds",Multiply(Call("endpointCompletion"),
                Call("measure",Call("nuP",f),Call("singleton",native)))));
        Formula w=F.Id("W");
        Formula returnStep=Call("AE",Call("ARow",f,w),r,Seq(r,Eq,native));
        Formula betaStep=Call("AE",Call("BRow",f,q),w,Seq(w,Eq,
            Call("nativeEndpoint",F.Id("beta"),F.Id("true")),Land,Sp,returnStep));
        Formula pStep=Seq(Open,Call("q",f,q),Neq,Sp,D(0),Close,Rightarrow,
            Call("u",q),Eq,Call("upper"),Land,Sp,Call("LRow",f,q),Eq,
            Call("smul",Call("endpointRate"),Call("CRow",f,q)),Land,Sp,betaStep);
        Formula transitions=Seq(Forall,Sp,f,Colon,Sp,F.Id("CommonFlow"),Comma,Sp,
            Call("AE",Call("nuP",f),q,pStep));
        return DocumentDefinition.Create(ScribeNode.Create("Identification of the surviving native law",
            H("Full coordinates and the original stationary class"),Blocks(
                Paragraph(Text("F is an arbitrary original boxed Borel CommonFlow. All probability descriptors retain every finite legal tail and the infinite noncompletion coordinate. CRow(F,Q) is the original unweighted acquired return row, T=L/(6/25), and q is the decreasing limit of T to the power n applied to threeStepAverage. CoreAt asserts the original goodP conditions, h>=3/25, Th<=h, Tq=q, nonzero q implies zero excess, almost every B successor satisfies goodB, and almost every C edge preserves sixthFunctional. GoodP retains the full normalized B residual, its endpoint box, every coordinate recursion, the completion identity and bounds, and the third-step box; goodB retains the full normalized A residual and its endpoint box. AE denotes almost everywhere, sequence(n,x) the sequence with index n, nhds the neighborhood filter, and ite the indicated conditional value.")),
                Describe.Lean(DescribeId.Create("common-flow-absorbing-core"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_absorbing_core"),
                    H("An absorbing conull core"),StatementSource.FromAuthor(Disp(Seq(
                        Forall,Sp,f,Colon,Sp,F.Id("CommonFlow"),Comma,Sp,
                        Exists,Sp,g,Subset,Sp,F.Id("PDescriptor"),Comma,Sp,baseCore))),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("Enclose the exceptional set in a measurable null set. Repeatedly intersect its complement with the states whose C row assigns zero mass to the previous complement. Stationarity makes every finite stage conull. Their countable intersection is conull and absorbing under the same C. The original full residuals and both endpoint boxes remain available there."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("common-flow-surviving-native"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_surviving_native"),
                    H("Survival identifies the actual upper law"),StatementSource.FromAuthor(Disp(Seq(
                        Forall,Sp,f,Colon,Sp,F.Id("CommonFlow"),Comma,Sp,survival))),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("On the positive sixth-functional class, acquired edge constancy makes the class absorbing and stationary localization gives g=9/25. In g=(1-u)*B(1-v), both factors are at least 3/5, so equality forces u=2/5 and v=2/5 on almost every actual B successor. Hence L=(6/25)C there. Induction identifies both letter coordinates at every depth; the original regular tail bound gives zero infinite-coordinate mass. Equality of all singleton masses on the complete countable legal-tail carrier identifies the full upper native probability measure. Conversely, at an actual upper native input every normalized g coordinate equals 9/25. The inequality g<=3*threeStepAverage forces a positive harmonic limit."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("common-flow-upper-endpoint-limits"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_upper_endpoint_limits"),
                    H("The original pointwise and averaged limits"),StatementSource.FromAuthor(Disp(Seq(
                        Forall,Sp,f,Colon,Sp,F.Id("CommonFlow"),Comma,Sp,
                        Call("AE",Call("nuP",f),q,density),Land,Sp,pointwise,Land,Sp,averaged))),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("On the surviving class h=q=9/25. Elsewhere q=0 and 0<=T^n g<=3*T^n h tends to zero. The full coordinate recursion converts this into the original singleton ratio limit. The common bound 30 on all normalized iterates permits dominated convergence on the unchanged original margin. The integral of the native singleton indicator is its actual original marginal mass. These conclusions require neither finite support, mixing, reversibility nor deterministic successors."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("common-flow-surviving-transitions"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.common_flow_surviving_transitions"),
                    H("Actual beta and return successors"),StatementSource.FromAuthor(Disp(transitions)),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The actual C row remains in the positive class, so almost every actual A successor on almost every B edge is the full upper p descriptor. The original normalized A residual is therefore exactly that native p law. Reconstruct the full suspended law from its stop mass and the image of its entire residual, including infinity. With v=2/5 this is the upper beta native descriptor. This identifies the given B/A successors rather than replacing their barycentres by sampled laws."))),DescribeRole.Theorem))));
    }
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
}
