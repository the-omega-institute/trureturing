using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV;

internal sealed class RefinedBMVGroupedFourThreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The grouped trace lower bound for four and three copies",
        H("The grouped trace lower bound for four and three copies"),
        Blocks(Describe.Lean(
            DescribeId.Create("refined-bmv-43-grouped"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMV/GroupedFourThree.grouped43_all"),
            H("Grouped trace comparison"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv")),
            Blocks(Paragraph(Text(
                "For positive semidefinite complex matrices R and C of any common finite size, " +
                "the mean of the real parts of the 35 word traces with three copies of R and four " +
                "of C is at least the real part of the trace of R² C² R C². After diagonalizing C, " +
                "a cyclic identity expresses the difference through kernels indexed by a spectral " +
                "value of C. Each kernel is a sum of a rank-one kernel and a weighted Cauchy " +
                "kernel. The Schur product theorem gives positivity, including at repeated and " +
                "zero spectral values."))),
            DescribeRole.Theorem))));
}
