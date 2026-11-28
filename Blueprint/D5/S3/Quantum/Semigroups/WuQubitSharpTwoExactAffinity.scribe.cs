using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuQubitSharpTwoExactAffinityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp scalar affinity stability for Wu's normalized one-mode two-deficit on the closed qubit spectrum.",
        H("Exact affinity stability at exponent two"),
        Blocks(
            Paragraph(Text("Use the normalized deficit of WuQubitSharpTwoRigidity with h = β/2, spectral polarization v, " +
                "and Gibbs-axis direction z. Put k(h) = thermalBias(h) = tanh(h/2), t = v/(1+spectralRoot(v)), " +
                "and J(u) = affinityJ(u). The scalar affinity defect is 1−(1+t k(h) z)/√((1+t²)(1+k(h)²)). " +
                "The bound includes the repeated spectrum and rank-one endpoint.")),
            Entry("exact-affinity-integral", "affinityJ_eq_integral", "Integral kernel for the exact affinity coefficient",
                "For every real u, affinityJ(u) is the interval integral of (1−x²)/(1−u x²)² on x ∈ [0,1]. " +
                "On the coefficient range u ∈ [0,1), this is the positive radial integral entering the sharp constant."),
            Entry("exact-affinity-coefficient", "exactAffinityCoefficient_eq", "Exact scalar affinity coefficient",
                "For every real h, with k(h) = thermalBias(h) = tanh(h/2), " +
                "exactAffinityCoefficient(h) = (cosh(h) k(h)²/(1+k(h)²) + 1/(4 sharpCoefficient(h) affinityJ(k(h)²)))⁻¹. " +
                "It is the coefficient for the squared loss of the ordinary-trace square-root affinity to the Gibbs point."),
            Entry("exact-affinity-coefficient-positive", "exactAffinityCoefficient_pos", "Positivity at nonnegative temperature",
                "For h ≥ 0, exactAffinityCoefficient(h) is strictly positive."),
            Entry("exact-affinity-coefficient-zero", "exactAffinityCoefficient_zero", "Tracial value of the exact coefficient",
                "At h = 0, exactAffinityCoefficient(0) = 4/3."),
            Entry("exact-affinity-bound", "normalizedDeficit_exactAffinity", "Exact closed-spectrum affinity bound",
                "For h ≥ 0, v ∈ [0,1], and z ∈ [−1,1], let t = v/(1+spectralRoot(v)). " +
                "Then exactAffinityCoefficient(h) times normalizedAffinityDefect(h,t,z)² is at most normalizedDeficit(h,v,z), " +
                "with strictness unless v = tanh(h) and (h = 0 or z = 1). The bound includes the repeated spectrum and rank-one endpoint."),
            Entry("exact-affinity-sharp-limit", "normalizedDeficit_exactAffinity_sharp_limit", "Sharpness along faithful spectra",
                "For h ≥ 0, the normalized deficit divided by the squared affinity defect tends to exactAffinityCoefficient(h) " +
                "as t decreases to thermalBias(h) from above with z = exactAffinitySharpAlignment(h,t). " +
                "The path has 0 < polarizationOfHalf(t) < 1, so its spectral states are faithful."),
            Entry("exact-affinity-coefficient-greatest", "exactAffinityCoefficient_isGreatest", "Greatest scalar affinity coefficient",
                "For h ≥ 0, exactAffinityCoefficient(h) is the greatest c for which " +
                "c times normalizedAffinityDefect(h,t,z)² ≤ normalizedDeficit(h,polarizationOfHalf(t),z) " +
                "for every t ∈ [0,1] and z ∈ [−1,1]. This is the exact scalar one-mode optimality statement."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
