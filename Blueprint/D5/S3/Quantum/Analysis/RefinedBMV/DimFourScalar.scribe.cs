using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV;

internal sealed class DimFourScalarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Individual geometric means in the refined BMV pairing",
        H("Individual geometric means in the refined BMV pairing"),
        Blocks(Describe.Lean(
            DescribeId.Create("refined-bmv-dim-four-individual-square"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMV/DimFourScalar.individual_sq"),
            H("The squared geometric mean at one center"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv")),
            Blocks(Paragraph(Text(
                "For five, six, or seven first factors and any three nonnegative cube roots, the product of the two repeated-index defects at a chosen center is bounded by the square of the mixed defect. Sorting the roots and writing them as a nonnegative base and two successive increments gives exact integer coefficient certificates for the three centers."))),
            DescribeRole.Theorem))));
}
