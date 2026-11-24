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
            Entry("mixed-coefficients", "MixedCoefficients", "Mixed coefficient families",
                "For lattice data D with unit Gram determinant and twisted input parity s, a coefficient "
                + "at integer label n is complex-linear in the odd untwisted state and the twisted input. "
                + "The output has the opposite twisted parity, and n represents physical mode n+1/2.",
                DescribeRole.Definition),
            Entry("mixed-signed-borcherds", "mixedBorcherds", "The signed mixed Borcherds identity",
                "Fix a fixed state a, an odd state b, a twisted input v and integers p, q, r. At offset i, "
                + "the iterate evaluates the coefficient p+q-i on the odd product a_(r+i)b and v, "
                + "weighted by binom(p,i). The first product applies the fixed action of a at mode "
                + "p+r-i on the output parity to the coefficient q+i of b acting on v. The second "
                + "product evaluates the coefficient q+r-i on b after the fixed mode p+i on the "
                + "input parity, with the extra sign epsilon(r). Both products have weight "
                + "(-1)^i binom(r,i). Each of the three families has finite support over i >= 0. "
                + "The iterate sum equals the first product sum minus the second.",
                DescribeRole.Definition),
            Entry("mixed-lawful-field", "LawfulMixedField", "Lawful signed mixed fields",
                "For each odd state b and twisted vector v, all sufficiently large labels have zero "
                + "coefficient on b and v. The coefficient at n on the lattice translate of b is "
                + "-(n+1/2) times the coefficient at n-1 on b. The signed mixed Borcherds identity "
                + "holds for all fixed states, odd states, twisted inputs and integer indices.",
                DescribeRole.Definition),
            Entry("mixed-native-field", "nativeMixedField", "The native lawful family",
                "The actual parity-changing modes give a lawful family by their truncation, "
                + "translation and signed Borcherds identities.", DescribeRole.Definition),
            Entry("mixed-agreement-space", "mixedAgreement", "The agreement space",
                "Intersect, over all integer labels, the kernels of the differences of the two "
                + "coefficient maps in the odd source variable.", DescribeRole.Definition),
            Entry("mixed-agreement-membership", "mem_mixedAgreement", "Agreement at every mode",
                "An odd state belongs to the agreement space precisely when the two coefficient families "
                + "give equal linear operators at every integer mode label on that state."),
            Entry("mixed-agreement-stability", "mixedAgreement_stable", "Agreement under fixed-algebra modes",
                "If two lawful families agree on an odd state, they agree on its image under every mode "
                + "of every fixed state. The signed Borcherds identity at p = 0 expresses the iterate "
                + "through coefficients on the original odd state."),
            Entry("mixed-charge-zero-source", "chargeZeroOdd", "The charge-zero odd space",
                "Take the odd states whose charge support is contained in the singleton zero.",
                DescribeRole.Definition),
            Entry("mixed-odd-charged-polynomial", "oddChargedPolynomial", "Antisymmetrized charged states",
                "Place the oscillator polynomial at charge c and subtract its lattice-involution image.",
                DescribeRole.Definition),
            Entry("mixed-fixed-charged-vacuum", "fixedChargedVacuum", "The fixed exponential sum",
                "Add the vacuum exponentials at charges c and -c to obtain a fixed state.",
                DescribeRole.Definition),
            Entry("mixed-charge-current", "chargeCurrent", "The current of a lattice charge",
                "Take the linear combination of the actual odd basis currents with coefficients given "
                + "by the coordinates of the lattice charge.", DescribeRole.Definition),
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
