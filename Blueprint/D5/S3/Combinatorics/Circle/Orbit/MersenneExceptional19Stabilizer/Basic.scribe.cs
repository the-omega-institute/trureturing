using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer;

internal sealed class MersenneExceptional19StabilizerBasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared original MersenneExceptional19Stabilizer foundation, extracted without changing the mathematical statements.",
        H("Shared MersenneExceptional19Stabilizer foundation"),
        Blocks(
            Describe.Lean(DescribeId.Create("source-phases"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19Stabilizer/Basic.source_phases"), H("source phases"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The centered-source formulas retain each original physical label and its exact exceptional top-bit correction. The three-slice bijection partitions the original labels; its finite-sum transport works in any additive commutative monoid. These shared originals are consumed by the physical arbitrary-group readout and integer primitive-weight reconstruction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-slices"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19Stabilizer/Basic.sum_slices"), H("sum slices"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The centered-source formulas retain each original physical label and its exact exceptional top-bit correction. The three-slice bijection partitions the original labels; its finite-sum transport works in any additive commutative monoid. These shared originals are consumed by the physical arbitrary-group readout and integer primitive-weight reconstruction."))), DescribeRole.Theorem),
            Paragraph(Text("The original definitions and proofs are the common dependency of the retained mathematical consumers. Shared originals are exposed directly; no forwarding theorem is introduced. Compilation, axiom closure and exact endpoint scope are checked at the consuming modules."))),
        []));
}
