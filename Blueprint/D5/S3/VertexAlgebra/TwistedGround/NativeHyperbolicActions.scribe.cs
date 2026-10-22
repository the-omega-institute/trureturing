using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class NativeHyperbolicActionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hyperbolic coordinates normalize the exact chosen native Leech ground action.",
        H("Native Hyperbolic Actions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nativehyperbolicactions"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/NativeHyperbolicActions.coordinate_action_mul"),
                H("Native Hyperbolic Actions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("NativeGround is literally ActualGround(ExplicitLeechLattice.data,determinantUnit). nativeRho is the original nested Classical.choose representation. Neither is a newly selected existential witness. The chosen rank is twelve and the chosen carrier has complex dimension 4096.")),
                    Paragraph(Text("The hyperbolic frame makes every diagonal entry of squareCorrection zero. Consequently the original actionScalar is a real sign, not an arbitrary fourth root. Evaluating the existing reducedRepresentation multiplication law on the constant-one function at zero establishes the scalar multiplication identity. Multiplication of normalized native operators then has exactly the standard binary cocycle.")),
                    Paragraph(Text("The left and right coordinate subgroups give commuting involutions within each subgroup. Across the two subgroups their commutation sign is complexSign(dot(right,left)). The functions involutionE and involutionF are these original native endomorphisms at the coordinate units."))),
                DescribeRole.Theorem))));
}
