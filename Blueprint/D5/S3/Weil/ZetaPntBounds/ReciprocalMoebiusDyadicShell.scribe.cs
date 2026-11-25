using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class ReciprocalMoebiusDyadicShellDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaPntBounds/ReciprocalMoebiusDyadicShell";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform dyadic reciprocal Möbius shell bound at zeta zeros",
        H("A uniform dyadic reciprocal Möbius shell bound at zeta zeros"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-dyadic-shell-lower"),
            DeclarationHandle.Create(Owner + ".dyadicReciprocalMoebiusShell_lower"),
            H("A lower bound at every cutoff"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Write Q(u) for the sum of μ(n)/n over positive integers n ≤ u. "
                    + "Let ρ be a zero of ζ with β = Re ρ strictly between zero and one. "
                    + "At every real cutoff P ≥ 1, one plus the integral of |Q(u) − Q(u/2)| "
                    + "over 1 ≤ u ≤ P is at least β |1 − 2^(1−ρ)|² P^β / |ρ(ρ−1)|.")),
                Paragraph(Text(
                    "The finite floor inverse evaluates the convolution of the dyadic shell "
                    + "with the kernel 2 fract(y/2) − fract(y) as a second difference of "
                    + "truncated linear functions for 0 ≤ x ≤ P. The fractional-part "
                    + "Mellin identity makes the convolution transform vanish at ρ. The "
                    + "target transform therefore equals the error transform, supported "
                    + "on 0 < t < 1/P after the reciprocal substitution. The absolute error "
                    + "is bounded by one plus the shell mass. Integrating the weight "
                    + "t^(β−1) on that support gives P^(−β)/β."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/ZetaPntBounds/ReciprocalMoebiusFloorInverse")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin"))
        ]));
}
