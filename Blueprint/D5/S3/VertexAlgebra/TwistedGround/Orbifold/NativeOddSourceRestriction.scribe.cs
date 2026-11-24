using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class NativeOddSourceRestrictionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddSourceRestriction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The charge-zero odd Heisenberg states determine lawful mixed fields on the Leech lattice.",
        H("Charge-Zero Detection for Odd Mixed Fields"),
        Blocks(
            Paragraph(Text("A mixed coefficient family takes an odd untwisted lattice state and a twisted "
                + "state of parity s to a twisted state of parity !s. Its integer mode label n represents "
                + "physical mode n+1/2. A lawful family is pointwise lower truncated, obeys translation "
                + "and satisfies the finite signed Borcherds identity with the actual fixed-algebra actions.")),
            Entry("mixed-agreement-membership", "mem_mixedAgreement", "Agreement at every mode",
                "An odd state belongs to the agreement space precisely when the two coefficient families "
                + "give equal linear operators at every integer mode label on that state."),
            Entry("mixed-agreement-stability", "mixedAgreement_stable", "Agreement under fixed-algebra modes",
                "If two lawful families agree on an odd state, they agree on its image under every mode "
                + "of every fixed state. The signed Borcherds identity at p = 0 expresses the iterate "
                + "through coefficients on the original odd state."),
            Entry("mixed-kernel-stability", "mixedKernel_stable", "Stability of the source kernel",
                "If every coefficient of a lawful family vanishes on an odd state, every coefficient also "
                + "vanishes on its image under any fixed-algebra mode."),
            Entry("mixed-charged-vacuum", "fixedChargedVacuum_zero_chargeCurrent",
                "The odd charged vacuum from a neutral current",
                "Applying mode zero of the fixed exponential sum at charges c and -c to the neutral current "
                + "in direction c gives the odd charged vacuum multiplied by minus the squared charge norm."),
            Entry("mixed-current-pair", "current_pair_mem_map", "Pairs of current modes preserve the source subspace",
                "For an odd subspace stable under all fixed-algebra modes, every pair of neutral current modes "
                + "sends a vector of the subspace into its image in the ambient lattice carrier. The Borcherds "
                + "identity recovers the product from fixed iterates by descending from the inner truncation bound."),
            Entry("mixed-odd-source-generation", "oddSource_eq_top", "Generation from charge zero",
                "For a positive definite Gram matrix, an odd subspace containing all charge-zero odd vectors "
                + "and stable under all fixed-algebra modes is the whole odd carrier. Fixed exponential modes "
                + "supply the odd charged vacua and pairs of current modes supply their polynomial descendants."),
            Entry("mixed-charge-zero-restriction", "restrictChargeZero", "Restriction of the first input",
                "At every mode label, restrict the first input to odd lattice states supported at charge zero.",
                DescribeRole.Definition),
            Entry("mixed-leech-charge-zero-injective", "leech_restrictChargeZero_injective",
                "Faithfulness on both Leech twisted parities",
                "For either twisted input parity of the Leech lattice, two arbitrary lawful mixed fields "
                + "with equal charge-zero restrictions are equal. Their agreement space contains the "
                + "charge-zero source, and stability under the actual fixed modes forces agreement "
                + "on every odd state."))));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
