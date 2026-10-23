using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ExplicitLargeHeightZeroCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZeroData/ExplicitLargeHeightZeroCount.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A numerical large-height window bound for actual zeta zeros, derived from the existing explicit zeta-growth and Jensen theorems.",
        H("Explicit Large-Height Zero Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("explicit-large-height-half-count"),
                DeclarationHandle.Create(Prefix + "half_count_large_explicit"),
                H("Retain the actual constants in the Jensen disk proof"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Adapt the existing LocalCount disk argument with its actual growth bound C=20/3 and A=1. The disks retain radii 0.84 and 0.95; their logarithmic ratio is at least 11/95. Bound log(20) by 5. The proof uses actual analytic multiplicities and never obtains an unspecified growth constant or a small-height zero count. The geometric proof follows the Apache-2.0 Zeta23 port identified in the Lean source; no novelty or optimality is claimed for the coefficient 64."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("explicit-large-height-full-count"),
                DeclarationHandle.Create(Prefix + "zetaZeroConfig_large_count_explicit"),
                H("Count the actual full critical-strip window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reuse the existing same-height reflection halving bound. Zeros on the critical line and their analytic multiplicities are treated by that owner. The interval convention is (t,t+1]. No RH hypothesis, numerical root certificate, or bound at small heights is required. This is a Candidate proof source; compilation and axiom closure are separate evidence."))),
                DescribeRole.Theorem),
            Paragraph(Text("A complete exterior-square mass application also uses the existing " +
                "all-height LocalCount.zetaZeroConfig_local_count, so the low-height windows " +
                "remain included; the numerical coefficient 128 above is not assumed there. " +
                "For actual exhaustive ZeroData, write gamma(i) for its complex spectral " +
                "parameter and m(i) for its exact analytic zeta multiplicity. Every source " +
                "square has exactly one positive-ordinate representative with the same " +
                "multiplicity, by the existing nonrealness, reflection and injectivity facts. " +
                "For T>=32, 0<rho<=1/8 and |z-T^2|<=T*rho/4, the full positive-ordinate " +
                "exterior sum m(i)/|z-gamma(i)^2|^2 over |gamma(i)-T|>4*rho is summable " +
                "and at most C*log(T+2)/(T^2*rho^2), with one source-fixed C>0. No RH " +
                "premise, simple-zero assumption or finite tail cutoff occurs.")),
            Paragraph(Text("To obtain this application, set the signed unit-window index " +
                "j=ceil(Re gamma(i)-T). Quadratic factorization and the exterior clearance " +
                "give T*rho*(1+|j|)<=|z-gamma(i)^2|. The actual multiplicity-aware local " +
                "count then bounds each complete bin by A/(T^2*rho^2) times " +
                "[2*log(T+2)+log(1+|j|)]/(1+|j|)^2. The two-sided kernel is summable " +
                "by the existing p-series bounds and log(x)<=2*sqrt(x). Its comparison " +
                "with the fixed T=32 kernel bounds every finite source-index subsum, " +
                "and the existing nonnegative tsum rules yield the full infinite bound. " +
                "This exact application was compiled with standard axioms and independently " +
                "reviewed as reuse of existing results; it introduces no new theorem here.")),
            Paragraph(Text("The indexed mass estimate concerns actual zeta spectral squares. " +
                "It does not itself identify the analytic zero orders or the complete infinite " +
                "canonical product of the descended Xi square source. Even after that " +
                "correspondence, small initial exterior mass and nonvanishing of the " +
                "extracted exterior factor do not supply the selected cluster's joint " +
                "finite-extraction responses. Growing multiplicity, the full same-source " +
                "remainder and every actual-node sign remain separate obligations."))), []));
}
