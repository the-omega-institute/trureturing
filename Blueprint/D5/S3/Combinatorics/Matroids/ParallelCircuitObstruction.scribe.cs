using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class ParallelCircuitObstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/ParallelCircuitObstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational residue correspondence.",
        H("Parallel Circuit Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parallel-rational-residue-comparison"),
                DeclarationHandle.Create(Module + ".parallel_rational_residue_comparison"),
                H("The rational residue correspondence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a surjective block-ordered projection whose vertices map to nonloops, quotient the "
                    + "rational top cycles with integral joint readouts by the integral cycles. The quotient "
                    + "is linearly equivalent over the integers to residue chains on the core with zero "
                    + "weighted boundary and zero circuit readouts. On each face the pullback of the image "
                    + "chain equals the residue of the original coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parallel-lifting-obstruction"),
                DeclarationHandle.Create(Module + ".parallel_lifting_obstruction"),
                H("The weighted lifting obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonempty expanded ground with a surjective block-ordered projection to nonloops "
                    + "of a finite ordered matroid, the saturation of the integral joint restriction image "
                    + "modulo the image is linearly equivalent over the integers to the residue chains on "
                    + "core bases satisfying both families of equations. Boundary insertions carry their "
                    + "fiber sizes. Circuit readouts use the ordinary signed deletion and shuffle signs. "
                    + "When a saturated readout is represented by a rational top cycle, pulling its image "
                    + "chain back along the projection recovers the residue of that cycle in every face coordinate."))),
                DescribeRole.Theorem))));
}
