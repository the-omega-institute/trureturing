using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalDyadicBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Mechanical/MechanicalDyadicBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lower dyadic slopes miss an exact boundary bit; upper dyadic slopes eventually preserve every fixed finite mechanical observation.",
        H("Mechanical Dyadic Boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mechanical-dyadic-boundary-mismatch"),
                DeclarationHandle.Create(Prefix + "dyadic_lower_boundary_mismatch"),
                H("Lower approximation and boundary bit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an irrational slope strictly between zero and one, the floor dyadic approximation is nonnegative and falls strictly below the slope by less than one binary unit. At phase one minus the exact slope, the first actual mechanical bit is true, while the first bit at every lower dyadic approximation is false. Increasing finite precision cannot remove this specified boundary mismatch."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-dyadic-upper-eventual-word"),
                DeclarationHandle.Create(Prefix + "dyadic_upper_eventually_word_eq"),
                H("Upper approximation preserves a finite observation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real slope, phase, and finite word length, all sufficiently precise upper dyadic approximations have the same actual mechanical bits throughout that word. The precision threshold may depend on the slope, phase, and word length, including at integer-hit phases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-finite-word-off-integer-hits"),
                DeclarationHandle.Create(Prefix + "finite_word_stable_off_integer_hits"),
                H("Finite words away from integer hits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When no positive-time cumulative floor in a fixed finite prefix lands on an integer, one positive slope radius preserves every cumulative floor and every actual mechanical bit in that prefix. The radius is constructed from the finite set of distances to neighboring integers."))),
                DescribeRole.Theorem))));
}
