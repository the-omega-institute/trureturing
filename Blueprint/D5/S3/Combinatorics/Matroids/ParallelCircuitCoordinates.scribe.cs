using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class ParallelCircuitCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/ParallelCircuitCoordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circuits of a parallel expansion.",
        H("Parallel Circuit Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("comap-circuit-cases"),
                DeclarationHandle.Create(Module + ".comap_circuit_cases"),
                H("Circuits of a parallel expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If each vertex projects to a nonloop, a circuit in the pullback is either a pair of "
                    + "distinct vertices in one fiber or an injective lift of a core circuit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("comap-contract-is-base-iff"),
                DeclarationHandle.Create(Module + ".comap_contract_isBase_iff"),
                H("Contracted bases under the projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a surjective label map and a contraction set contained in the expanded ground, a "
                    + "contracted basis is exactly an injective lift of a core basis after contraction by the "
                    + "image of the set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-readout-on-transversal"),
                DeclarationHandle.Create(Module + ".signed_readout_on_transversal"),
                H("Projection of a transverse readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a block-ordered projection, let two finite faces project injectively with disjoint "
                    + "images. The signed deletion sum over the first face on coefficients projected to the "
                    + "core equals the signed deletion sum of the two image faces."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pullback-chain-boundary"),
                DeclarationHandle.Create(Module + ".pullbackChain_boundary"),
                H("Boundary weighted by fiber size"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a block-ordered projection, take a finite face whose vertices project "
                    + "injectively. The augmented boundary of the pulled-back chain is the sum over "
                    + "insertions outside the image face. Each term has its ordered incidence sign "
                    + "and multiplicity equal to the size of the inserted class."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-readout-of-parallel-pair"),
                DeclarationHandle.Create(Module + ".signed_readout_of_parallel_pair"),
                H("A pair circuit compares two coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a block-ordered projection, two distinct vertices with the same label and a "
                    + "transverse face avoiding that label give a signed deletion sum equal to zero exactly "
                    + "when the two single-vertex insertions have equal coefficients."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("transversal-coeff-eq"),
                DeclarationHandle.Create(Module + ".transversal_coeff_eq"),
                H("Constancy along fiber exchanges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two finite faces which project injectively to the same face have equal coefficients "
                    + "when single exchanges of representatives over that image preserve the coefficient. The "
                    + "number of vertices outside the destination decreases at each exchange."))),
                DescribeRole.Theorem))));
}
