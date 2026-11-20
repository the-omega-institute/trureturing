using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records;

internal sealed class PrimitiveHiddenLabelEntropyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy";
    private const string Title = "The Umegaki information lost by a two-site observer";
    private static LibraryNoteRef EntropySource => LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities");
    private static LibraryNoteRef CollisionSource => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title + ".", H(Title),
        Blocks(
            Claim("entropy", "Von Neumann entropy in nats",
                "On a finite density state P, the repository alias uses S(P) = −Re tr(P log P). "
                + "A zero eigenvalue contributes zero. Watrous gives this entropy in bits and the "
                + "conversion to the natural-log convention multiplies the value by log 2.",
                AssessedProvenance.FromLiterature(EntropySource), DescribeRole.Definition),
            Claim("fairMixture_nonzero_spectrum", "The spectrum of an equal mixture of two pure states",
                "For unit vectors u and v put s = ∑ⱼ uⱼ conj(vⱼ). The nonzero spectral multiset "
                + "of their equal mixture consists of (1+|s|)/2 and (1−|s|)/2 with zeros discarded. "
                + "The weighted two-column Gram matrix gives the same nonzero roots with multiplicity, "
                + "as in Jozsa and Schlienz, Section 2 (G1). Its characteristic polynomial "
                + "also gives the coincident-root and proportional-vector cases.",
                AssessedProvenance.FromRepo(EntropySource)),
            Claim("fairMixture_entropy", "Binary entropy of the pure-state mixture",
                "Writing h(t) = −t log t − (1−t) log(1−t), the entropy of the mixture is h((1+|s|)/2). "
                + "Here h is Real.binEntropy and the endpoint terms use the zero convention.",
                AssessedProvenance.FromRepo(EntropySource)),
            Claim("fairMixture_relativeEntropy", "Each pure label has the same finite divergence",
                "For P = |u⟩⟨u|, Q = |v⟩⟨v| and M = (P+Q)/2, the support of each label is "
                + "contained in the support of M. A phase adjustment and a Gram-preserving unitary "
                + "exchange P and Q while fixing M. The two support-aware Umegaki divergences to M "
                + "are therefore equal and both are S(M).",
                AssessedProvenance.FromRepo(EntropySource)),
            Claim("collisionMixture_nonzero_spectrum", "The two positive weights of the collision mixture",
                "For m ≥ 5 hidden sites and total length n = 2+m, take the fair mixture Mₙ of "
                + "the two normalized primitive periodic states P₀,ₙ and P₁,ₙ. Put "
                + "sₙ = collisionNormalizedOverlap(n). The nonproportional rays give |sₙ| < 1. "
                + "The two positive eigenvalues of Mₙ, counted with multiplicity, are (1±|sₙ|)/2.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource)),
            Claim("collisionMixture_rank", "The primitive collision mixture has rank two",
                "At each n ≥ 7 the nonzero spectral multiset has cardinality two, giving "
                + "rank two on the full ring.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource)),
            Claim("collisionMixture_entropy", "Exact entropy on the full ring",
                "At every n ≥ 7 the fair mixture has entropy h((1+|sₙ|)/2) nats.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource)),
            Claim("collision_partialTrace_pure", "Both labels have the same literal two-site reduction",
                "The trace over the last m sites sends each pure label Pᵦ,ₙ to R, the common "
                + "positive definite trace-one marginal on the first two sites. The four observed eigenvalues are "
                + "1/25, 4/25, 4/25 and 16/25.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource)),
            Claim("collision_partialTrace_mixture", "The two-site reduction of the fair mixture",
                "Taking the literal partial trace of Mₙ gives the same R by linearity.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource)),
            Claim("collision_relativeEntropy", "Global and observed Umegaki divergences",
                "For either label b the extended divergence D(Pᵦ,ₙ ∥ Mₙ) is finite and equals "
                + "h((1+|sₙ|)/2). The observed divergence is D(R ∥ R) = 0.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource)),
            Claim("collisionDefect", "Definition of the two-site information loss",
                "The defect is the finite trace-log Umegaki value D(Pᵦ,ₙ ∥ Mₙ) minus the "
                + "finite trace-log value for their two literal partial traces.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource), DescribeRole.Definition),
            Claim("collision_defect", "Exact loss for either label",
                "The defect equals S(Mₙ) = h((1+|sₙ|)/2) for every n ≥ 7. In the "
                + "classical–quantum ensemble, the Holevo information on the full ring is S(Mₙ) "
                + "because the labels are pure, and the Holevo information on the observed pair "
                + "is zero because their reductions coincide.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource)),
            Claim("collision_defect_limit", "The loss tends to one bit",
                "The overlap bound |sₙ| ≤ 4(19/20)ⁿ gives sₙ → 0, so continuity of binary entropy "
                + "gives the limit log 2 nats for each label as n = 7+k grows.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource)))));

    private static DocumentBlock Claim(string name, string title, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("primitive-hidden-label-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            provenance, Blocks(Paragraph(Text(prose))), role);
}
