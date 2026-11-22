using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class MobiusBoundaryMixedScaleExclusionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaPntBounds/MobiusBoundaryMixedScaleExclusion";
    private const string Cluster = "D5/S3/Weil/ZetaPntBounds/MobiusBoundaryClusterExclusion";
    private const string Boundary = "D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundary";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite critical Möbius energy excludes pairs of high zeta zeros with separate distance bounds.",
        H("Zero pairs at two scales near the unattained zeta abscissa"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixed-scale-zero-pair-exclusion"),
                DeclarationHandle.Create(
                    Owner + ".no_mixedScaleZeroPair_atHighOrdinate_of_unattainedZeroAbscissa"),
                H("Exclusion for the exponent sum u + 2v"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Theta, F.Minus, F.Operatorname, F.Grp(F.Id("Re")), F.Sp, F.Rho,
                    F.Gt, F.Bar, F.Id("t"), F.Bar, F.Caret, F.Grp(F.Minus, F.Id("u")),
                    F.Quad, F.Lor, F.Sp,
                    F.Operatorname, F.Grp(F.Id("dist")),
                    F.Open, F.Theta, F.Plus, F.Id("i"), F.Id("t"), F.Comma, F.SigmaLower, F.Close,
                    F.Gt, F.Bar, F.Id("t"), F.Bar, F.Caret, F.Grp(F.Minus, F.Id("v"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let θ < 1 be the unattained supremum of the real parts of nontrivial "
                        + "zeta zeros. Let S(x) be the sum of μ(n)/n over positive integers n ≤ x. "
                        + "Assume (S(x) − S(2x))² x^(1−2θ) is integrable over x > 1. "
                        + "Fix real exponents 0 < v ≤ u with u + 2v > 2.")),
                    Paragraph(Text(
                        "There is a positive T such that the following holds for every zero ρ "
                        + "strictly to the left of θ with t = Im ρ and |t| ≥ T. "
                        + "If θ − Re ρ ≤ |t|^(−u), then no distinct zero σ lies at distance "
                        + "at most |t|^(−v) from θ + it.")),
                    Paragraph(Text(
                        "Select one unit of multiplicity at each zero and divide out these "
                        + "two factors. The integral uses the window of radius θ − Re ρ around t. "
                        + "The first factor gives this window a single inverse power of its width. "
                        + "The second gives an inverse square in the distance to σ plus that width. "
                        + "The disk growth estimate and the finite energy bound make a pair "
                        + "with the stated scales impossible at sufficiently large |t|."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Cluster)),
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary))
        ]));
}
