using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class PrescribedRatioFloorSmoothingDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Analytic/SeriesInequalities/PrescribedRatioFloorSmoothing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed geometric smoothing preserves a doubling floor and every prescribed adjacent ratio.",
        H("Prescribed Ratio Floor Smoothing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prescribedratiofloorsmoothing-uniform-smoothing-equivalence"),
                DeclarationHandle.Create(Module + "uniform_smoothing_equivalence"),
                H("Uniform comparison for geometric smoothing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a positive nonincreasing real sequence omega, define z(0)=omega(0) and z(k+1)=q z(k)+(1-q) omega(k+1), with 0<q<1. Assume constants C>=1, c>0 and d>=0 such that omega(j)<=C omega(k) whenever j<=k and k+2<=2(j+2), and c<=omega(k)(k+2)^d for every natural k. There is one B>=1 such that omega(k)<=z(k)<=B omega(k) for every k. No summability assumption is required.")),
                    Paragraph(Text("Split the recurrence at l=floor(k/2). The recent block is bounded by C omega(k), while the initial block is at most q^(k-l) omega(0). Exponential decay bounds q^(k-l)(k+2)^d uniformly, so the power lower bound absorbs the old block into a fixed multiple of omega(k). The constant B precedes the index k."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prescribedratiofloorsmoothing-doubling-iterate"),
                DeclarationHandle.Create(Module + "doubling_iterate"),
                H("Iterating the doubling bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let g be any real-valued function and D>=1. If g(2t)<=D g(t) for every real t>=2, then g(2^j t)<=D^j g(t) for every natural j and every t>=2. Positivity and monotonicity of g are not needed for this iteration.")),
                    Paragraph(Text("Apply the discrete Gronwall product bound to the sequence g(2^j t), with constant multiplier D and zero forcing. Every sampled argument remains at least two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prescribedratiofloorsmoothing-doubling-polynomial"),
                DeclarationHandle.Create(Module + "doubling_polynomial"),
                H("A scalar power envelope from doubling"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume g(t)>=1 on [2,infinity), g is nondecreasing there, D>=1 and g(2t)<=D g(t). Put d=log(D)/log(2). One constant C>=1 bounds g(t)<=C t^d for every t>=2, including D=1 and d=0.")),
                    Paragraph(Text("Choose the ceiling of log(t)/log(2), apply the iterated bound at a dyadic point, and interpolate by monotonicity. The ceiling error contributes a single factor D."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prescribedratiofloorsmoothing-doubling-floor-smoothing"),
                DeclarationHandle.Create(Module + "doubling_floor_smoothing"),
                H("A smoothed doubling floor with exact mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary a>0 and g satisfying the preceding assumptions, put omega(k)=1/((k+2) g(k+2)^(1/a)). For every fixed 0<q<1 its geometric smoothing z has one B>=1 with omega(k)<=z(k)<=B omega(k) for all natural k. The same z is positive and nonincreasing, and q z(k)<=z(k+1).")),
                    Paragraph(Text("Doubling supplies the half-scale comparison, and the scalar power envelope supplies the polynomial lower bound required for uniform smoothing. If omega is summable, then z is summable and its mass is exactly omega(0)/(1-q)+sum over k>=0 of omega(k+1). Summing the recurrence and retaining its initial value gives this identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prescribedratiofloorsmoothing-prescribed-ratio-floor"),
                DeclarationHandle.Create(Module + "prescribed_ratio_floor"),
                H("One rational smoothing parameter before all growth functions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each prescribed real R>1 there is a rational q with 0<q<1 and 1/R<=q. This q is chosen before every g, a>0, D>=1 and positive mass budget K. For every such nondecreasing doubling g with g>=1 on [2,infinity) and summable omega, there is a rational c with 0<c<=1 such that eta(k)=c z(k) is positive, at most one, nonincreasing and summable, with total mass at most K and eta(k)<=R eta(k+1).")),
                    Paragraph(Text("The same eta satisfies c omega(k)<=eta(k)<=B c omega(k) at every index for one B>=1. Choose q by rational density, then choose c below both one and K divided by the positive mass of z. The construction preserves one sequence, its prescribed ratio and its uniform comparison simultaneously.")),
                    Paragraph(Text("These statements concern infinite real sequences and a noncomputable existence construction. They do not provide an effective name for g, a summation modulus, a sampling program, or an estimate for actual task moments."))),
                DescribeRole.Theorem))));
}
