using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicHotInnerMixedDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicHotInnerMixed.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical one-mode mixed derivative and Hermitian trace for the Wu cubic deficit.",
        H("One-mode mixed derivative for the Wu cubic deficit"),
        Blocks(
            Paragraph(Text("For the equal-cap CAR specialization of Wu v1, Remark 3.15, equation (3.54), take exponent " +
                "three and write u = exp(−β/3). The physical Gibbs weights are a = u³b and b(1+u³) = 1. " +
                "The two diagonal entries of the scaled sandwiched input are v = u(1+by) and w = 1−ay, " +
                "and its real coherence entry is √u k. With Gibbs density diag(a,b), the physical sandwiched input " +
                "is b^(1/3) times this matrix V. Set z = k² on the physical locus.")),
            Entry("hot-inner-mixed", "hot_inner_mixed", "Mixed derivative at the scalar ray",
                "Fix 0 < u < 1 and b > 0 with the stated Gibbs relations, and set α = α₃*(β). " +
                "Use the scalar extension of the deficit in real z. Differentiate in z at zero, then differentiate " +
                "that function of y at zero. The derivative is −b(9a/4)(1+u)/(1−u) times " +
                "[2(1−2α)+2(1−u)²/(1+u+u²)]. The gap w−v is positive near the base point, so the inner " +
                "spectral derivatives there are obtained from the two characteristic roots. The cubic mass " +
                "has zero y derivative at the base point, and the Gibbs logarithms retain both diagonal charges."),
            Entry("hot-inner-spectral", "embedded_spectral", "Hermitian cubic logarithm trace",
                "For u ≥ 0 and arbitrary real a, b, k and y, the real part of the ordinary trace of V³ log(V³), " +
                "with log given by continuous functional calculus, equals the sum of 3λ³ log λ over the two roots " +
                "λ = (v+w ± √((w−v)²+4uk²))/2, counted with multiplicity."),
            Entry("hot-inner-deficit", "embedded_deficit", "Scaled ordinary-trace deficit",
                "For u ≥ 0 and arbitrary real a, b, α, k and y, the scalar deficit at z = k² equals " +
                "b[(9/8) E − α(S − T log T − d₀ log a − d₁ log b)]. Here S is the cubic logarithm trace, " +
                "T is the real part of the ordinary trace of V³, and d₀ and d₁ are its real diagonal entries. " +
                "The energy E is the real part of the ordinary trace of V²W, where W has diagonal entries " +
                "2uby and −2ay and the same coherence entry √u k. In the Gibbs normalization the scale logarithm " +
                "cancels between the spectral logarithm and the mass normalization."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
