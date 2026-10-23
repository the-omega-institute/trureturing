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
                NativeSection(),
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
    private const string NativePrefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification.";
    private static DocumentBlock NativeSection()
    {
        Formula s=F.Id("s"), r=F.Id("r"), t=F.Id("t"), d=F.Id("D"), n=F.Id("n"), j=F.Id("j"), i=F.Id("i"), b=F.Id("b"), q=F.Id("Q"), w=F.Id("W"), theta=F.Id("theta"), flow=F.Id("F"), nu=F.Id("nu"), kernel=F.Id("K");
        Formula z=Multiply(Call("alphaMass",r),Call("betaMass",r));
        Formula coeff=Call("markerCoefficient",r,i);
        Formula atoms=And(All(Eqn(Mass(Call("native",Call("p"),r),Call("pAtom",n,i)),Multiply(coeff,Pow(z,n))),("n","Nat"),("i","Letter")),And(Eqn(Mass(Call("native",Call("beta"),r),Call("betaStop")),Call("betaMass",r)),And(All(Eqn(Mass(Call("native",Call("beta"),r),Call("betaAtom",n,i)),Multiply(Multiply(Call("alphaMass",r),coeff),Pow(z,n))),("n","Nat"),("i","Letter")),All(Eqn(Mass(Call("native",s,r),Call("infinity",s)),Num(0)),("s","ActivePhase")))));
        return new DocumentBlock.Section(H("Actual native laws on the full legal carriers"),Blocks(
            Node("inclusion_embedding",All(Call("MeasurableEmbedding",Call("legalSubtypeInclusion",s)),("s","ActivePhase")),"legalSubtypeInclusion(s) is Subtype.val from ValidTail(s) to RawTail. Its injectivity and the countable measurable image give the exact comap interface used by complete continuous laws."),
            Node("stopped_legal",All(Call("Valid",s,Call("stoppedReadWord",s,F.Id("omega"))),("s","ActivePhase"),("omega","Stream")),"The original stopped parser lands in the complete legal carrier, including the noncompletion outcome."),
            Node("geometric_tail",All(Eqn(Call("tsumRestrictedGeometric",F.Id("z"),d,j),Multiply(Pow(F.Id("z"),j),Call("tsumGeometric",F.Id("z"),d))),
                ("z","ENNReal"),("D","ENNReal"),("j","Nat")),"tsumRestrictedGeometric(z,D,j) is the sum over n:Nat of D*z^n when j<=n and zero otherwise. tsumGeometric(z,D) is the sum over all n:Nat of D*z^n. The identity holds for all extended nonnegative parameters, including infinity. It is consumed by every continuous source tail."),
            Node("p_atom_tail",All(Seq(Call("member",Call("pAtom",n,i),Call("tailSet",Call("p"),j)),Leftrightarrow,Sp,Le(j,n)),("j","Nat"),("n","Nat"),("i","Letter")),"All p completion atoms have their original tail depth."),
            Node("beta_atom_tail",All(Seq(Call("member",Call("betaAtom",n,i),Call("tailSet",Call("beta"),j)),Leftrightarrow,Sp,Le(j,n)),("j","Nat"),("n","Nat"),("i","Letter")),"The same complete suspended atoms retain their original tail depth."),
            Node("beta_stop_not_tail",All(Call("notMember",Call("betaStop"),Call("tailSet",Call("beta"),j)),("j","Nat")),"The immediate suspended stop is outside each return tail."),
            Paragraph(Text("native(s,r) is the comap of the actual explicitStoppedWordLaw(s,r) along legal subtype inclusion. The actual stopped-word map always lands in the legal range; that range has mass one. Thus native is a probability law, rather than an unnormalized comap. endpoint(false)=1/3 and endpoint(true)=2/5. nativeEndpoint(s,b) bundles this actual law with the exact Regular predicate.")),
            Node("native_coordinate",All(Eqn(Mass(Call("native",s,r),t),Mass(Call("explicitStoppedWordLaw",s,r),Call("val",t))),("s","ActivePhase"),("r","UnitInterval"),("t","ValidTail")),"The atom t ranges over ValidTail(s), including infinity. Measurable subtype inclusion is injective and comap evaluates its singleton image exactly."),
            Node("native_atoms",All(atoms,("r","UnitInterval")),"markerCoefficient(r,i) means alphaMass(r) when i=0 and betaMass(r)^2 otherwise. alphaMass(r)=r and betaMass(r)=1-r as ENNReal masses. The complete list is pAtom(n,0): r z^n; pAtom(n,1): (1-r)^2 z^n; betaStop: 1-r; betaAtom(n,0): r^2 z^n; betaAtom(n,1): r(1-r)^2 z^n; infinity in either phase: zero."),
            Node("native_tails",All(And(Eqn(Mass(Call("native",Call("p"),r),Call("tailSet",Call("p"),j)),Pow(z,j)),Eqn(Mass(Call("native",Call("beta"),r),Call("tailSet",Call("beta"),j)),Multiply(Call("alphaMass",r),Pow(z,j)))),("r","UnitInterval"),("j","Nat")),"Countable legal atom reconstruction, word injectivity and shifted geometric sums give every exact tail. The p normalization fixes the full series sum. At j=0 the suspended tail is r, not one."),
            NativeResidualA(),
            Paragraph(Text("For every theta in [0,1], the endpoint application uses unweighted marginals (1-theta) Dirac(native_a)+theta Dirac(native_b) and joint edge measures on the corresponding endpoint pairs. Deterministic Borel acquired kernels select the matching opposite endpoint. Singleton comap identities, including infinity, normalize both B and A residuals; each coordinate is one of the two comparison endpoints and hence satisfies the full min/max boxes. The upper native singleton has mass theta, including theta=0 and theta=1. This finite boundary application does not restrict the arbitrary Borel margins in the singleton-limit theorem."))));
    }
    private static DocumentBlock NativeResidualA() {
        Formula b=F.Id("b");
        return Node("native_endpoint_residualA",All(Eqn(Call("residualA",Call("nativeEndpoint",Call("beta"),b)),Call("law",Call("nativeEndpoint",Call("p"),b))),("b","Bool")),"prependA sends every p completion atom to the corresponding beta atom and preserves infinity. Native atom evaluation gives its full comap law; the original nonzero alpha mass normalizes the entire residual.");
    }
    private static DocumentBlock.Describe Node(string declaration, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create(declaration.Replace('_','-').ToLowerInvariant()), DeclarationHandle.Create(NativePrefix+declaration),
        H(declaration.Replace('_',' ')), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Le(Formula a, Formula b) => Seq(a,Leq,Sp,b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula And(Formula a, Formula b) => Seq(Open,a,Close,Land,Open,b,Close);
    private static Formula All(Formula body, params (string Name,string Type)[] xs) {
        for(int k=xs.Length-1;k>=0;k--) body=Seq(Forall,Sp,F.Id(xs[k].Name),Colon,Sp,F.Id(xs[k].Type),Comma,Sp,body);
        return body;
    }
    private static Formula Mass(Formula law, Formula atom) => Call("mass",law,atom);
}
