using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV;

internal sealed class DimFourWalkDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV cubic walk in dimension four",
        H("The refined BMV cubic walk in dimension four"),
        Blocks(Describe.Lean(
            DescribeId.Create("refined-bmv-dim-four-walk"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMV/DimFourWalk.walk_nonneg"),
            H("A positive quadratic form bounds the cubic walk"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv")),
            Blocks(Paragraph(Text(
                "A nonnegative symmetric defect that vanishes on the diagonal gives a nonnegative cubic walk on four vertices when its mixed value is between the individual geometric means and their sum. The diagonal part of the columnwise quadratic forms matches the repeated-index walks. The four oriented triples are compared using signs or using the cycle product of the three pairs within a column."))),
            DescribeRole.Theorem))));
}
