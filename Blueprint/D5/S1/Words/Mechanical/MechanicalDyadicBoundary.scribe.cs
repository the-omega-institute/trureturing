using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalDyadicBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Mechanical/MechanicalDyadicBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Upper dyadic slopes eventually preserve every fixed finite mechanical observation.",
        H("Mechanical Dyadic Boundary"),
        Blocks(
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
