using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class JointRecordTransportDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/JointRecordTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rectangular partial isometry preserves the full set of finite POVM scores.",
        H("Joint POVM transport through the occupied subspace"),
        Blocks(
            Describe.Lean(DescribeId.Create("partial-isometry-success-set"),
                DeclarationHandle.Create(Module + "success_set_partialIsometry"),
                H("Partial-isometry transport preserves all attainable scores"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let the finite label type be nonempty, let p be any real weight function, and let the input and output states be density states on finite complex carriers. For a rectangular matrix V, assume V(V†V) = V, that V†V acts as the identity on each input density matrix by left multiplication, and that each output density matrix is V rho V†.")),
                    Paragraph(Text("Compress each POVM effect and assign the complementary projector to one fixed label. The complement contributes zero to every state trace. Compressing in both directions gives equality of the attainable success sets."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pure-transport-success-set"),
                DeclarationHandle.Create(Module + "success_set_pure_partialIsometry"),
                H("Transport on pure amplitudes preserves the success set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The source and target amplitudes have squared norm one for each label. The same partial-isometry identity is assumed, V†V fixes each source amplitude, and V maps it to the corresponding target amplitude. Rank-one density matrices then satisfy the matrix transport hypotheses. The binary product proof uses this equality to carry an attainable score to the original carrier."))),
                DescribeRole.Theorem))));
}
