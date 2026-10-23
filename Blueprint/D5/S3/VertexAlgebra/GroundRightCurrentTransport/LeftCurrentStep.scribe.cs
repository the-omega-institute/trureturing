using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GroundRightCurrentTransport;

internal sealed class LeftCurrentStepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native first-source current compatibility", H("LeftCurrentStep"), Blocks(
            Describe.Lean(DescribeId.Create("left-current-step"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/GroundRightCurrentTransport/LeftCurrentStep.left_current_step"), H("left_current_step"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Assume the original source a at lift gamma is compatible with every second source b at every lift delta. For every signed current mode d, compatibility then holds for neutralMode(i,d,a) at lift gamma+1. The common cutoff dominates actual source locality, finite Laurent extraction and the source-field tail. Smaller compatibility identifies each actual inner Q field; actual changed-source localities provide the independent outer cutoffs. Polynomial-action multiplicativity pads the original Laurent numerator without restricting its exponents. The scalar actual nested-Q iterate is compared with the finite source iterate for every mode, target vector and algebraic dual. Dual separation recovers the complete field; two valid cutoffs identify the native product and hence make the native defect zero. This conditional step preserves the all-state objective. The later graded-carrier assembly still requires four projected-pair laws and signed lift transport; the homogeneous component is not arbitrary unprojected compatibility at independent lifts."))), DescribeRole.Theorem))));
}
