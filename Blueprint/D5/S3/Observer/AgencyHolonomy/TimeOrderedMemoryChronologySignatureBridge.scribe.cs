using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class TimeOrderedMemoryChronologySignatureBridgeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/TimeOrderedMemoryChronologySignatureBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The step-two logarithm of the frozen time-ordered memory matrices recovers the oriented swap curvature and specializes the finite Hopf reversal law.",
        H("Time-Ordered Memory Chronology Signature Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("time-ordered-memory-order-detected"),
                DeclarationHandle.Create(
                    Prefix + "timed_matrix_two_event_order_detected"),
                H("Nonzero swap curvature detects event order"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("primeSwapCurvature")), Sp,
                    Ne, Sp, D(0), Sp, Rightarrow, RowBreak, Grp(),
                    Operatorname, Grp(F.Id("doubledMagnusDegreeTwo")), Sp,
                    Ne, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The matrix-valued step-two chronological signature has commutator logarithm. Its upper-right entry is the negative of the already frozen two-event memory swap curvature, due to the reverse matrix-product convention for earlier-first evolution.")),
                    Paragraph(Text(
                        "The same adapter specializes the chronological Hopf antipode: reverse the timed event word and negate each event matrix. No infinite signature or continuous Magnus convergence is asserted."))),
                DescribeRole.Theorem))));
}
