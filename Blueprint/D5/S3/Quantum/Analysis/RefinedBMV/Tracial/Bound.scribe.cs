using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.Tracial;

internal sealed class RefinedBMVTracialBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quantitative refined BMV gap for finite traces",
        H("A quantitative refined BMV gap for finite traces"),
        Blocks(Describe.Lean(
            DescribeId.Create("refined-bmv-tracial-three-copy-gap"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMV/Tracial/Bound.wordMean_three_trace_gap"),
            H("The gap and the commutator"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv")),
            Blocks(Paragraph(Text(
                "For positive elements A and B of any unital C*-algebra with a finite positive trace, the " +
                "gap is the mean trace of the twenty words with three copies of each element minus the trace " +
                "of the cube of AB. Forty times the trace of AB times the gap bounds three times the square of " +
                "the trace of the commutator's adjoint times the commutator. The proof keeps one rank-one term " +
                "of the centered cubic kernel, uses cyclicity and trace Cauchy–Schwarz on finite positive " +
                "partitions, and passes to the norm limit. For a faithful trace, zero gap forces A and B to commute."))),
            DescribeRole.Theorem))));
}
