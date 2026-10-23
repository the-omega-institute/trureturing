using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class NativeBorelStationaryLocalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula flow=F.Id("F"), q=F.Id("Q"), r=F.Id("R");
        Formula fv=Call("sixthFunctional",flow,q), ev=Call("excess",q);
        Formula statement=Seq(Forall,Sp,flow,Colon,Sp,F.Id("CommonFlow"),Comma,Sp,
            Call("AE",Call("nuP",flow),q,Seq(Open,
                Call("lintegral",Call("CRow",flow,q),r,Call("sixthFunctional",flow,r)),Eq,fv,
                Land,Sp,Multiply(Call("ofReal",ev),fv),Eq,D(0),Land,Sp,
                Open,Call("q",flow,q),Neq,Sp,D(0),Rightarrow,ev,Eq,D(0),Close,Close)));
        return DocumentDefinition.Create(ScribeNode.Create("Stationary completion localization",
            H("Zero gain on the original margin"),Blocks(
                Paragraph(Text("F is an arbitrary original boxed Borel CommonFlow. CRow(F,Q) is its actual unweighted acquired return row. q is the decreasing harmonic limit of T to the power n applied to the positive three-step completion average, with T=L/(6/25). excess(Q)=g(Q).toReal-9/25 and sixthFunctional=q to the sixth power divided by threeStepAverage to the fifth power. AE(mu,Q,P) means P holds for mu-almost every Q.")),
                Describe.Lean(DescribeId.Create("common-flow-stationary-localization"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStationaryLocalization.common_flow_stationary_localization"),
                    H("Stationarity earns zero excess on surviving mass"),StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The original unweighted stationarity identity makes the integral of CF equal the integral of F. The earned bound CF >= F+(9/20)*excess*F and finiteness therefore give CF=F almost everywhere. Additive cancellation gives excess*F=0. When q is nonzero, positive finite h makes F nonzero; excess is nonnegative and hence equals zero. No harmonicity, zero-excess, stationarity-conditioned event, or path localization conclusion is added as a premise."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("common-flow-stationary-edges"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStationaryLocalization.common_flow_stationary_edges"),
                    H("The acquired edges preserve the stationary functional"),
                    StatementSource.FromAuthor(Disp(Seq(Forall,Sp,flow,Colon,Sp,F.Id("CommonFlow"),Comma,Sp,
                        Call("AE",Call("nuP",flow),q,Call("AE",Call("CRow",flow,q),r,
                            Seq(Call("sixthFunctional",flow,r),Eq,fv)))))),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("Cauchy-Schwarz on each actual probability row gives (CF) squared <= C(F squared). The earned fixed point CF=F and original stationarity make the two second moments have the same integral, so equality holds almost everywhere. The real conditional variance is therefore zero. The bounded second moment and the pinned zero-variance theorem force F at the successor to equal F at the input on almost every acquired edge. No reversibility, deterministic successor or mixing condition is used."))),DescribeRole.Theorem))));
    }
}
