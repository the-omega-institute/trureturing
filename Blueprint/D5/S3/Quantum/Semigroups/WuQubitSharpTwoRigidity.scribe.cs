using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuQubitSharpTwoRigidityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuQubitSharpTwoRigidity.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact equality and a tracial affinity stability bound for Wu's normalized one-mode two-deficit on the closed qubit spectrum.",
        H("Closed-spectrum rigidity at exponent two"),
        Blocks(
            Paragraph(Text("In Wu arXiv:2610.33686v1, (3.6)–(3.10), put p = p' = 2, h = β/2, " +
                "v = tanh u and let z be the Gibbs-axis direction of the larger eigenvalue. " +
                "The closed spectral range is 0 ≤ v ≤ 1. Put S = √(1−v²), b = sinh(h)/(1+cosh(h)), " +
                "c = b/h for h ≠ 0 and c = 1/2 for h = 0. The entropy term is " +
                "P(v) = ((1+v) log(1+v) + (1−v) log(1−v))/2, with 0 log 0 = 0. " +
                "Write N = P(v)+log(cosh h)−hvz and E = 1−(1+S)/(2 cosh h)+(1−S)z²/(2 cosh h)−tanh(h)vz. " +
                "The deficit Δ(h,v,z) = E−cN is defined at the rank-one endpoint and at the repeated spectrum.")),
            Entry("sharp-coefficient-eq-wu", "sharpCoefficient_eq_wu", "Coefficient at positive temperature parameter",
                "For h > 0, c = 2 sinh(h/2) sinh(h/2)/(h sinh h), the coefficient at p = 2 in (3.8)–(3.9)."),
            Entry("radial-add-square", "normalizedDeficit_eq_radial_add_square", "Regular radial and angular decomposition",
                "For any real h,z and v ∈ [0,1], Δ(h,v,z) = R(h,v) + (vz−b(1+S))²/(2 cosh(h)(1+S)), " +
                "where R(h,v) = 1−(1+S)/(1+cosh h)−c(P(v)+log(cosh h)). The square denominator is strictly positive throughout the closed spectrum."),
            Entry("radial-zero-iff", "radialDeficit_eq_zero_iff", "Unique radial minimum",
                "For h ≥ 0 and v ∈ [0,1], R(h,v) = 0 if and only if v = tanh h. " +
                "For positive h, the derivative at v ∈ (0,1) has the sign of sinh(u)/u−sinh(h)/h with u = artanh v. " +
                "Strict increase of sinh(u)/u and continuity on [0,1] give strict decrease up to tanh h and strict increase thereafter. At h = 0 the radial minimum is at zero."),
            Entry("deficit-nonnegative", "normalizedDeficit_nonneg", "Nonnegative normalized deficit",
                "For h ≥ 0, v ∈ [0,1] and every real z, Δ(h,v,z) ≥ 0."),
            Entry("deficit-zero-iff", "normalizedDeficit_eq_zero_iff", "Exact equality",
                "For h ≥ 0, v ∈ [0,1] and every real z, Δ(h,v,z) = 0 if and only if v = tanh h and (h = 0 or z = 1). " +
                "The radial minimum forces v = tanh h, and the nonnegative square then forces alignment whenever h > 0. At h = 0 the spectrum is repeated and the direction is unrestricted."),
            Entry("rank-one-positive", "normalizedDeficit_rankOne_pos", "Strict positivity at rank one",
                "For h ≥ 0 and every real z, Δ(h,1,z) > 0. The radial minimum tanh h stays strictly below one at every finite h."),
            Entry("tracial-stability", "normalizedDeficit_tracial_stability", "Tracial stability on the closed spectrum",
                "For v ∈ [0,1] and every real z, put W = √((1+√(1−v²))/2). Then (4/3)(1−W)² ≤ Δ(0,v,z). " +
                "The derivative comparison for the radial remainder uses t = v/(1+√(1−v²)), the identity artanh v = 2 artanh t, " +
                "and the strict bound (1−t²) artanh t < t−2t³/3 for 0 < t < 1. Continuity extends the estimate to v = 1."),
            Entry("tracial-stability-strict", "normalizedDeficit_tracial_stability_strict", "Strict stability away from the repeated spectrum",
                "For v ∈ [0,1] with v > 0 and every real z, the inequality (4/3)(1−W)² < Δ(0,v,z) is strict, including v = 1. " +
                "The lower bound is attained at v = 0. The physical matrix consumer is WuQubitSharpTwoPhysical."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
