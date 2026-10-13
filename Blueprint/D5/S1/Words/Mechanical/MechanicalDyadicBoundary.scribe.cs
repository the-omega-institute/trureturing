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
                Blocks(Paragraph(Text("For every real slope, phase, and finite word length, all sufficiently precise upper dyadic approximations have the same actual mechanical bits throughout that word. The precision threshold may depend on the slope, phase, and word length, including at integer-hit phases. For the contrasting lower approximants, let alpha be irrational and strictly between zero and one, beta_p = floor(2^p*alpha)/2^p for every natural precision p, and x = 1-alpha. The floor bound and irrationality give 0 <= beta_p < alpha. Hence x is in (0,1), x+alpha = 1, and 0 < x+beta_p < 1. The cumulative floors at x are zero for both slopes; the next floor is one at alpha and zero at beta_p. Thus the actual first mechanical letter is one at alpha and zero at every lower approximant, and the corresponding Boolean bits disagree for every p. Increasing parameter precision therefore does not guarantee equality of the bit at this exact boundary. This is a direct application of the existing floor and mechanical-word definitions, not an additional theorem or a uniform failure away from integer hits."))),
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
