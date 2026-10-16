using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform;

internal sealed class RaySoundnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform soundness of original rays.",
        H("Uniform soundness of original rays"), Blocks(
            Describe.Lean(DescribeId.Create("appt-quadbit-raysoundness"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/RaySoundness.original_ray_gram_bound"),
                H("Uniform soundness of original rays"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four disjoint identifier ranges together cover Fin 187. Their validity proofs supply " +
                    "the exact mass and Gram identities and the branch inequalities for every original label. " +
                    "The scalar envelope argument yields the Gram bound for arbitrary natural N at least 67 and " +
                    "every allowed middle position. Explicitly, the sum over a,b of gap(a) times gap(b) times " +
                    "min(position(a),position(b)) is bounded by bulkValue(N,bulkIndex(N)) times the square of " +
                    "the mass sum over a of gap(a) times position(a). This is the estimate used for the " +
                    "synthesized original rays."))), DescribeRole.Theorem),
            Paragraph(Text("These statements concern real scalar spectra and finite cofactor certificates. Connecting " +
                    "the boundary inequalities to a physical APPT model, constructing an attaining state, and " +
                    "determining a purity supremum require additional results.")))));
}
