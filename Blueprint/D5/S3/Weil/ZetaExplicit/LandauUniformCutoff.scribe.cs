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
                        "For the harmonic collision theorem, take C from the inclusive cutoff "
                        + "bound and add exp(|t|/2)*(1+log(V)) to the right-hand side inside "
                        + "the factor C. This term is nonnegative for V>1. Both statements "
                        + "use the same positiveCutoff, analytic multiplicity and phase "
                        + "for every t with 0<|t|. Apply harmonic_zeta_collision_limit "
                        + "with that estimate and its stated cutoff and resolution hypotheses. "
                        + "Gonek's prime-power main term concerns the explicit formula."))),
                DescribeRole.Theorem))));
}
