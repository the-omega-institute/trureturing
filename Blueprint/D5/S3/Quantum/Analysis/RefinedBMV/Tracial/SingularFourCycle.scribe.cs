using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.Tracial;

internal sealed class SingularFourCycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV four-cycle inequality at a zero spectral value",
        H("The refined BMV four-cycle inequality at a zero spectral value"),
        Blocks(Describe.Lean(
            DescribeId.Create("refined-bmv-singular-four-cycle-matching"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Analysis/RefinedBMV/Tracial/SingularFourCycle.gapDefect_one_zero_le"),
            H("Compensation by opposite endpoint matchings"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv")),
            Blocks(Paragraph(Text(
                "At each positive integer degree, the scalar four-cycle deficit with one zero node " +
                "is bounded by the sum of the two geometric means of opposite backtracking deficits. " +
                "The proof uses a reciprocal complete homogeneous identity and a beta-binomial moment " +
                "bound obtained by changing the counting law with a controlled relative entropy."))),
            DescribeRole.Theorem))));
}
