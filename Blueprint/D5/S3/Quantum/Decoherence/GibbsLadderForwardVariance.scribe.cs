using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class GibbsLadderForwardVarianceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/GibbsLadderForwardVariance.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/basso2026modularfluctuation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite cyclic Gibbs dynamics can have arbitrarily small forward variance at a fixed positive mean.",
        H("Forward energy variance in a finite Gibbs ladder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gibbs-ladder-forward-variance"),
                DeclarationHandle.Create(Module + "exists_gibbs_ladder_forward_variance_lt"),
                H("Arbitrarily small forward variance at fixed positive mean"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every positive inverse temperature, positive target mean and positive tolerance, "
                        + "an equally spaced finite Gibbs ladder and its cyclic shift realize the target "
                        + "forward mean with variance below the tolerance.")),
                    Paragraph(Text(
                        "Only the wraparound transition differs from the common energy increment. "
                        + "Its Gibbs weight decays exponentially in the number of levels. "
                        + "Continuity in the level spacing fixes the mean exactly."))),
                DescribeRole.Theorem))));
}
