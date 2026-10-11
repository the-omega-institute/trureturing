using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class NativeBorelNativeLawsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNativeLaws.";
    public DocumentDefinition Create()
    {
        Formula s=F.Id("s"), r=F.Id("r"), t=F.Id("t"), d=F.Id("D"), n=F.Id("n"), j=F.Id("j"), i=F.Id("i"), b=F.Id("b"), q=F.Id("Q"), w=F.Id("W"), theta=F.Id("theta"), flow=F.Id("F"), nu=F.Id("nu"), kernel=F.Id("K");
        Formula z=Multiply(Call("alphaMass",r),Call("betaMass",r));
        Formula coeff=Call("markerCoefficient",r,i);
        Formula atoms=And(All(Eqn(Mass(Call("native",Call("p"),r),Call("pAtom",n,i)),Multiply(coeff,Pow(z,n))),("n","Nat"),("i","Letter")),And(Eqn(Mass(Call("native",Call("beta"),r),Call("betaStop")),Call("betaMass",r)),And(All(Eqn(Mass(Call("native",Call("beta"),r),Call("betaAtom",n,i)),Multiply(Multiply(Call("alphaMass",r),coeff),Pow(z,n))),("n","Nat"),("i","Letter")),All(Eqn(Mass(Call("native",s,r),Call("infinity",s)),Num(0)),("s","ActivePhase")))));
        return DocumentDefinition.Create(ScribeNode.Create("Actual native endpoints on full legal carriers",H("Native laws and endpoint flows"),Blocks(
            Paragraph(Text("native(s,r) is the comap of the actual explicitStoppedWordLaw(s,r) along legal subtype inclusion. The actual stopped-word map always lands in the legal range; that range has mass one. Thus native is a probability law, rather than an unnormalized comap. endpoint(false)=1/3 and endpoint(true)=2/5. nativeEndpoint(s,b) bundles this actual law with the exact Regular predicate.")),
            Node("native_coordinate",All(Eqn(Mass(Call("native",s,r),t),Mass(Call("explicitStoppedWordLaw",s,r),Call("val",t))),("s","ActivePhase"),("r","UnitInterval"),("t","ValidTail")),"The atom t ranges over ValidTail(s), including infinity. Measurable subtype inclusion is injective and comap evaluates its singleton image exactly."),
            Node("native_map",All(Eqn(Call("map",Call("native",s,r),Call("SubtypeVal")),Call("explicitStoppedWordLaw",s,r)),("s","ActivePhase"),("r","UnitInterval")),"The transported law maps back to the actual stopped-word law. Invalid finite words have zero explicit mass, and legal words are reconstructed by the inclusion. This is an equality of complete measures."),
            Node("native_atoms",All(atoms,("r","UnitInterval")),"markerCoefficient(r,i) means alphaMass(r) when i=0 and betaMass(r)^2 otherwise. alphaMass(r)=r and betaMass(r)=1-r as ENNReal masses. The complete list is pAtom(n,0): r z^n; pAtom(n,1): (1-r)^2 z^n; betaStop: 1-r; betaAtom(n,0): r^2 z^n; betaAtom(n,1): r(1-r)^2 z^n; infinity in either phase: zero."),
            Node("native_tails",All(And(Eqn(Mass(Call("native",Call("p"),r),Call("tailSet",Call("p"),j)),Pow(z,j)),Eqn(Mass(Call("native",Call("beta"),r),Call("tailSet",Call("beta"),j)),Multiply(Call("alphaMass",r),Pow(z,j)))),("r","UnitInterval"),("j","Nat")),"Countable legal atom reconstruction, word injectivity and shifted geometric sums give every exact tail. The p normalization fixes the full series sum. At j=0 the suspended tail is r, not one."),
            Node("native_endpoint_boxes",All(Call("EndpointBox",Call("nativeEndpoint",s,b)),("s","ActivePhase"),("b","Bool")),"Both native endpoints satisfy every exact regular tail bound and the complete atom boxes. At each atom the law is literally one comparison endpoint, so the proof uses min and max and imposes no global ordering of endpoint probabilities."),
            Node("native_endpoint_residuals",All(And(Eqn(Call("residualB",Call("nativeEndpoint",Call("p"),b)),Call("law",Call("nativeEndpoint",Call("beta"),b))),Eqn(Call("residualA",Call("nativeEndpoint",Call("beta"),b)),Call("law",Call("nativeEndpoint",Call("p"),b)))),("b","Bool")),"Both identities are equalities of the full opposite probability measures. prependB takes betaStop to pAtom(0,1), betaAtom(n,i) to pAtom(n+1,i), and infinity to infinity. prependA takes pAtom(n,i) to betaAtom(n,i) and retains infinity. The complete native atom formulas prove both comap identities; the original nonzero denominators normalize them."),
            Node("endpoint_flow_inhabited",All(Existsn(Eqn(Mass(Call("nuP",flow),Call("nativeEndpoint",Call("p"),Call("true"))),Call("alphaMass",theta)),"F","CommonFlow"),("theta","UnitInterval")),"The witness endpointCommonFlow(theta) has marginals (1-theta) Dirac(native_a)+theta Dirac(native_b) and edge measures with the corresponding endpoint pairs in each orientation. Globally Borel deterministic kernels distinguish the upper native descriptor and choose the matching opposite endpoint. Both disintegrations, all four unweighted margins, both full normalized residuals and both complete boxes are proved. Neither mixture weight is divided out. This proves boundary inhabitance for every weight, including zero and one; it restricts none of the arbitrary Borel flows of the original theorem. A Dirac at a mixed descriptor is a different construction and is not used."))));
    }
    private static DocumentBlock.Describe Node(string declaration, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create(declaration.Replace('_','-').ToLowerInvariant()), DeclarationHandle.Create(Prefix+declaration),
        H(declaration.Replace('_',' ')), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula And(Formula a, Formula b) => Seq(Open,a,Close,Land,Open,b,Close);
    private static Formula All(Formula body, params (string Name,string Type)[] xs) {
        for(int k=xs.Length-1;k>=0;k--) body=Seq(Forall,Sp,F.Id(xs[k].Name),Colon,Sp,F.Id(xs[k].Type),Comma,Sp,body);
        return body;
    }
    private static Formula Existsn(Formula body, string name, string type) => Seq(Exists,Sp,F.Id(name),Colon,Sp,F.Id(type),Comma,Sp,body);
    private static Formula Mass(Formula law, Formula atom) => Call("mass",law,atom);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a),Caret,Grp(b));
}
