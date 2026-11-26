using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaExplicit;

internal sealed class LandauUniformCutoffDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaExplicit/LandauUniformCutoff.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform Landau control of the positive zeta ordinate sum under RH.",
        H("Uniform bound at actual cutoffs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("landau-uniform-actual-cutoff"),
                DeclarationHandle.Create(Owner + "actual_cutoff_landau_envelope"),
                H("A uniform bound for the inclusive positive zero sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the Riemann hypothesis. For real V>1 and t nonzero, sum "
                        + "exp(i*t*Im(rho)) with analytic multiplicity over the zeros with "
                        + "0<Im(rho)<=V. An absolute positive constant times "
                        + "V+exp(|t|/2)*(1+|t|)^2+log(V)/|t| bounds the norm.")),
                    Paragraph(Text(
                        "At a nearby zero-free height use the rectangle with bottom at 1, "
                        + "left edge at -1/4 and right edge at 1+1/log(3x), where x=exp(|t|). "
                        + "The argument principle counts the zeros with their multiplicities. "
                        + "Reflection extends the square-logarithmic top bound to the full edge. "
                        + "The bottom is bounded on a compact zero-free segment, and the two "
                        + "vertical integrals have uniform bounds.")),
                    Paragraph(Text(
                        "After division by sqrt(x), the top-edge term sqrt(x)*log(V+9)^2 "
                        + "is controlled by V+sqrt(x)*(1+log(x))^2. Split at x=V. "
                        + "The zeros crossed between the chosen height and V lie in a "
                        + "bounded window and their total multiplicity is O(log(V+9)). "
                        + "Conjugation supplies negative frequencies.")),
                    Paragraph(Text(
                        "The resulting bound supplies the uniform Landau premise of the "
                        + "harmonic collision theorem. Its cutoff and resolution assumptions "
                        + "still apply. This bound controls the whole sum; the prime-power "
                        + "main term of the Landau formula is a separate statement."))),
                DescribeRole.Theorem))));
}
