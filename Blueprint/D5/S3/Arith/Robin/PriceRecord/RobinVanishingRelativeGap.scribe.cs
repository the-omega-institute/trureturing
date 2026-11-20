using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class RobinVanishingRelativeGapDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap.";
    private const string Attainment =
        "Assume ρ satisfies ZeroSum.IsNontrivialZero and every z satisfying it has Re(z)≤Re(ρ). ";
    private const string Mesh =
        "Let N be a strictly increasing natural sequence with N(k+1)/N(k) tending to one in ℝ. ";

    private static DocumentBlock.Describe Theorem(string id, string name, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An attained maximal zeta zero gives a Robin lower-bound criterion on ratio-one meshes.",
        H("Canonical Robin records on meshes with vanishing relative gaps"),
        Blocks(
            Paragraph(Text(
                "The sample at index k is the original robinLogMargin at the integer "
                + "m(k)=strictInteger(firstLayerPrice(N(k)+1)). Write W(a,x)=x^a log(x) and "
                + "B for RHSharpArithmeticEnvelope.B. Write P(Θ,u) for "
                + "MaximalRealPartProjection.maximalSeries(actualCoeff,actualZero,Θ,u). The zero sequence "
                + "indexes actual occurrences, so an actual zero occurs according to its analytic multiplicity.")),
            Theorem("actual-canonical-samples-lower-bound-iff", "actual_canonical_samples_lower_bound_iff",
                "Exact lower-bound criterion under attainment",
                Attainment + Mesh + "For each real 0<α≤1/2, there exist real C≥0 and natural K such that "
                + "−C≤W(α,N(k)) robinLogMargin(m(k)) for every k≥K if and only if Re(ρ)≤1−α. "
                + "The attaining zero is a hypothesis. The equivalence includes α=1/2."),
            Paragraph(Text(
                "For N(k)≥2, strictInteger_spec, strict_layer_iff and firstLayerPrice_strictAnti "
                + "give a positive-price strict record whose prime support is precisely the primes up "
                + "to N(k). Its largest prime is P=Pn(N(k)). RHSharpOriginalRecordMargin.margin_identity "
                + "and B_prefix identify robinLogMargin(m(k))−B(N(k)) with the original full arithmetic "
                + "correction. The leading estimate fullC_leading gives eventual nonnegativity and boundedness "
                + "at the scale D(P)=sqrt(P) log(P). The normalization D(P)/D(N(k))→1 gives the same properties "
                + "at D(N(k)). For weights with exponent below 1/2 the scaled correction tends to zero. "
                + "When Re(ρ)≤1−α, the full-strip envelope for B and the nonnegative correction yield the "
                + "lower bound, including at α=1/2. When Re(ρ)>1−α, unboundedness below at weight α "
                + "contradicts any eventual bound.")),
            Theorem("actual-canonical-samples-unbounded-below", "actual_canonical_samples_unbounded_below",
                "Unboundedness below above the critical weight",
                Attainment + "Assume Re(ρ)>1/2. " + Mesh + "For any real α>1−Re(ρ), real M and "
                + "natural K there is k≥K with W(α,N(k)) robinLogMargin(m(k))<M. The factor "
                + "N(k)^(α−(1−Re(ρ))) tends to +∞ and amplifies the fixed negative excursions."),
            Theorem("actual-b-negative-on-vanishing-gap-mesh", "actual_B_negative_on_vanishing_gap_mesh",
                "Negative arithmetic excursions on a logarithmic mesh",
                Attainment + "Assume Re(ρ)>1/2. Let y be a real sequence tending to +∞ whose forward "
                + "increments tend to zero. There is a real c>0 such that every natural K admits k≥K "
                + "with exp((1−Re(ρ)) y(k)) y(k) B(exp(y(k)))<−c. Apply sign transfer to the uniformly "
                + "continuous real part of the maximal-line series."))));
}
