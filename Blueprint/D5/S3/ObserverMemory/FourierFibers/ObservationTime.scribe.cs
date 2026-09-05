using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class ObservationTimeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical separation time is the exact boundary at which an eventually separated pair leaves every finite observation fiber.",
        H("Observation Time as a Fiber Boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-future-membership-iff-before-separation"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/FourierFibers/ObservationTime."
                    + "finite_future_membership_iff_before_separation"),
                H("Finite fiber membership ends at the first visible time"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open,
                    Exists, Sp, F.Id("t"), Comma, Sp,
                    Operatorname, Grp(F.Id("observedAt")),
                    Open, F.Id("t"), Comma, Sp, F.Id("left"), Close,
                    Sp, Neq, Sp,
                    Operatorname, Grp(F.Id("observedAt")),
                    Open, F.Id("t"), Comma, Sp, F.Id("right"), Close,
                    Close,
                    Sp, Rightarrow, Sp,
                    Open,
                    Open, F.Id("left"), Comma, Sp, F.Id("right"), Close,
                    Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("finiteFutureRelation")),
                    Open, F.Id("horizon"), Close,
                    Sp, Leftrightarrow, Sp,
                    F.Id("horizon"), Sp, Lt, Sp,
                    Operatorname, Grp(F.Id("separationTime")),
                    Open, F.Id("left"), Comma, Sp, F.Id("right"), Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a pair that is separated at some finite dynamical readout, membership in the canonical finite-future relation holds exactly before the repository separationTime.")),
                    Paragraph(Text(
                        "The module reuses observedAt, finiteFutureRelation, infiniteFutureRelation, and separationTime. It introduces no competing time or observation-window API and makes no identification with physical time."))),
                DescribeRole.Theorem))));
}
