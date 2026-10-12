using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeFiniteWordCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFiniteWordCoordinates.";

    public DocumentDefinition Create()
    {
        Formula t=F.Id("t"), n=F.Id("n"), b=F.Id("b"), m=F.Id("M"), e=F.Id("e");
        Formula curve=All(Seq(
            Call("periodicCoord",Call("curveParameters",t),n,b,D(2)),Eq,
            Multiply(Call("if",Seq(b,Eq,D(0)),Call("curveU",t),Call("curveG",t)),Call("pow",t,n))),
            ("t","CurveParameter"),("n","Nat"),("b","Letter"));
        Formula step=Multiply(Call("letterStep",m,e,D(1)),Call("letterStep",m,e,D(0)));
        Formula transfer=All(Seq(Call("cylinderVector",m,e,Call("pWord",n,D(1))),Eq,
            Call("apply",Call("pow",step,n),Call("cylinderVector",m,e,Call("word",D(1),D(1))))),
            ("Z","FiniteMeasurableCarrier"),("M","ObserverZ"),("e","InstalledEmitterM"),("n","Nat"));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite stopped-word coordinates",H("Periodic and installed coordinate suppliers"),Blocks(
                Paragraph(Text("The original declaration namespace remains NativeBorelFiniteCompleteObstruction. This module owns the finite word-coordinate suppliers; the continuous descriptor and moment construction imports them. No observer register or acquired operation is added.")),
                Paragraph(Text("CurveParameter is the closed interval [239/1000,6/25]. The same x sets q=1944/390625, g(x)=q/x^3, u(x)=1-g(x)-x and v(x)=x/(g(x)+x). curveParameters has w=1/4 and uses these same u and v for all three native control labels. scalar_boxes proves the original u,v control boxes and g bounds; curve_algebra identifies the fixed rate with x. These consumed helpers are parameter adaptations of the existing periodic supplier.")),
                Node("curve-coordinate","curve_coord","The periodic coordinate at the same parameter",curve,
                    "periodicCoord(T,n,b,2) denotes NativePeriodicWordLaw.coord(T,n,b,2). The real coercion of t is used in its power. NativePeriodicWordLaw.fixed_coord is applied directly, with curve_algebra identifying its rate. This supplied helper is consumed by curve_atoms in the continuous descriptor construction; it is not new mathematical content."),
                Paragraph(Text("FiniteMeasurableCarrier means any Z with Fintype, MeasurableSpace and MeasurableSingletonClass. M and e retain the full original Observer and lawful InstalledEmitter hypotheses. Marked(Z) is Z times Option(Operation). cylinderVector(M,e,a)(w) is the real marked-law mass of the rawFrom prefix cylinder a, started at w. letterStep(M,e,b) sums the actual markedRow(M,e,w,v).toReal times f(v), retaining only incoming marks whose readSymbol is b.")),
                Node("installed-coordinate","cylinderVector_pWord","The exact finite stopped-word transfer",transfer,
                    "The marked regeneration law gives cylinder_cons. Taking real masses gives cylinderVector_cons. Induction on n, using the original p_word_succ identity, yields the displayed power of the two masked linear maps. This existing content proof is consumed by continuous_no_finite_complete in NativeBorelFiniteCompleteObstruction."),
                Paragraph(Text("tail_coordinate identifies the actual pAtom(n,1) stopped-law singleton with this prefix cylinder at (z,none), using the exact stopped_word_fiber. initialReadout(rho) is the linear functional summing rho(z).toReal times f(z,none). The original finite COMPLETE exclusion consumes these suppliers with the same M, e and rho. Every starting PMF and every natural n remain quantified; no exponential rate or unrestricted positive-jc assertion is introduced.")))));
    }

    private static DocumentBlock.Describe Node(string id,string name,string title,Formula statement,string text) =>
        Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),DescribeRole.Theorem);

    private static Formula All(Formula body,params (string Name,string Type)[] xs)
    {
        for(int k=xs.Length-1;k>=0;k--)
            body=Seq(Forall,Sp,F.Id(xs[k].Name),Colon,Sp,F.Id(xs[k].Type),Comma,Sp,body);
        return body;
    }
}
