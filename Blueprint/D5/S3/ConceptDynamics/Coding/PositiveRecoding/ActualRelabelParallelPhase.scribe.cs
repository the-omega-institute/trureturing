using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PositiveRecoding;

internal sealed class ActualRelabelParallelPhaseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parallel-edge discrepancy on the original primitive path basis.",
        H("Parallel-edge discrepancy on the original primitive path basis"),
        Blocks(
            Paragraph(Text("timed packages the actual history homeomorphism and integer-time equivariance. For r and s with the same vertex equivalence, discrepancy acts on the target graph by r.edge after s.edge.symm and fixes vertices. discrepancy_factor verifies that timed s followed by this discrepancy equals timed r on actual paths.")),
            Paragraph(Text("For all n,m and every nonzero d divisible by three, timed_three_zero reuses parallel_edge_offset_sum_three_zero on the original numbered paths and canonical primitive basis. same_vertex_residue then uses additivity to compare the two reduced gyrations. This asserts vanishing of the total reduced discrepancy, not vanishing of every edge phase, and does not assume nonempty edge or orbit fibers.")),
            Paragraph(Text("These constructions and identities are repository-derived. Their provenance does not assert literature novelty.")),
            Describe.Lean(DescribeId.Create("positive-recoding-actualrelabelparallelphase-timed"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.timed"), H("timed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Package the coordinatewise graph-relabel homeomorphism with its integer-time law. Its periodic transport uses the existing canonical primitive paths."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("positive-recoding-actualrelabelparallelphase-discrepancy"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.discrepancy"), H("discrepancy"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The genuine discrepancy is on B, with edge permutation r after s^{-1}. Its two endpoint identities follow from the SAME actual vertex bijection."))), DescribeRole.Definition),
            Describe.Remark(DescribeId.Create("positive-recoding-actualrelabelparallelphase-timed-three-zero"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.timed_three_zero"), H("timed_three_zero"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Reuse the owning vanishing proof on the same coordinatewise action and canonical primitive basis, without exporting its private implementation types.")))),
            Describe.Remark(DescribeId.Create("positive-recoding-actualrelabelparallelphase-discrepancy-factor"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.discrepancy_factor"), H("discrepancy_factor"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Following s by the target discrepancy gives r on every path when their vertex maps agree. Additivity then isolates the discrepancy contribution to gyration.")))),
            Describe.Remark(DescribeId.Create("positive-recoding-actualrelabelparallelphase-same-vertex-residue"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRelabelParallelPhase.same_vertex_residue"), H("same_vertex_residue"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Arbitrary parallel edges may change phase; their TOTAL reduced phase vanishes by the original T proof. No zero phase rule for r is asserted.")))))));
}
