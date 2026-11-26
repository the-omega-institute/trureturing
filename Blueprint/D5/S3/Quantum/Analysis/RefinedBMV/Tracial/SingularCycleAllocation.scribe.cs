using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.Tracial;

internal sealed class SingularCycleAllocationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-copy refined BMV for singular spectral cycles",
        H("Four-copy refined BMV for singular spectral cycles"),
        Blocks(Describe.Lean(
            DescribeId.Create("refined-bmv-singular-spectral-cycles"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Analysis/RefinedBMV/Tracial/SingularCycleAllocation.product_bound_of_singular_four_cycles"),
            H("The matrix comparison"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv")),
            Blocks(Paragraph(Text(
                "At every positive integer degree, the four-copy word mean bounds the balanced trace " +
                "for a positive semidefinite first factor and a Hermitian second factor when its spectral " +
                "coupling graph has no triangles, each two-edge path has at most one four-cycle completion, " +
                "and each supported simple four-cycle meets the zero spectrum. Cyclic Cauchy–Schwarz and " +
                "the scalar matching inequality allocate each backtracking term at most once."))),
            DescribeRole.Theorem))));
}
