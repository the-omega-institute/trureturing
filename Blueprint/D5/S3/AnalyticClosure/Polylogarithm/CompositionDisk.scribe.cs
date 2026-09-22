using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class CompositionDiskDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/AnalyticClosure/Polylogarithm/CompositionDisk.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict nested coefficients give the actual depth-normalized analytic series on the unit disk.",
        H("CompositionDisk"), Blocks(
            Describe.Lean(DescribeId.Create("strict-coefficient-control"),
                DeclarationHandle.Create(Prefix + "source_coefficient_control"),
                H("Bounds, vanishing and the minimal strict tuple"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(Paragraph(Text(
                    "For every positive composition ks and bound N, the recursive strict sum H is "
                    + "nonnegative and at most N to the length of ks. It vanishes below that length "
                    + "and is strictly positive at and above it. At the first nonzero index it equals "
                    + "the reciprocal product along the unique minimal tuple (length,...,1). "
                    + "Structural induction proves the bound and the positive surviving summand; "
                    + "the bounds are used in the actual infinite-series estimates."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-series-normalization"),
                DeclarationHandle.Create(Prefix + "source_series"),
                H("Absolute convergence and exact source realization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(Paragraph(Text(
                    "For every positive head and tail, the coefficients H(tail,n+d-1)/(n+d)^head "
                    + "are strictly positive. Their scalar series F is absolutely convergent and "
                    + "analytic at every point of the open unit disk. Its value at zero is the "
                    + "positive minimal-tuple product. The function z^d F equals both the recursive "
                    + "source sum and the independent sum over strict nested indices, and has "
                    + "analytic order exactly d at zero. Polynomial-weighted geometric estimates "
                    + "supply the live convergence premise of the frozen scalar-series supplier. "
                    + "This source normalization is part of the disk consumer; it asserts no "
                    + "boundary multiple-zeta convergence or coefficient-sign conjecture."))), DescribeRole.Theorem))));
}
