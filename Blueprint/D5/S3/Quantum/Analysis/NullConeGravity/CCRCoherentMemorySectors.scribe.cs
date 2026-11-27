using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class CCRCoherentMemorySectorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/CCRCoherentMemorySectors.";
    private static readonly LibraryNoteRef NullLocal =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");
    private static readonly LibraryNoteRef NullCone =
        LibraryNoteRef.Create("D5/L/HilbertOperators/chandrasekaran2026nullcone");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coherent phase shift belongs to the countable Fock folium exactly when its mode profile is square-summable. Dyadic memory gives an uncountable family of pairwise disjoint representations.",
        H("Coherent Fock shifts and dyadic memory sectors"),
        Blocks(
            Paragraph(Text("Satishchandran and Sorce discuss Gaussian-state excitability, and "
                + "Chandrasekaran uses cyclic representations of null-cone observables. "
                + "Ashtekar's asymptotic quantization and the gravitational memory representations of "
                + "Prabhu, Satishchandran and Wald motivate the phase shifts. The representations here "
                + "use the finite-mode Weyl algebra and the dyadic model of the infrared norm.")),
            Entry("characteristic", "coherentShiftChar", "Coherent characteristic function",
                "On a finite mode set F, multiply the vacuum factor exp(−∑|wᵢ|²/2) by "
                + "the phase exp(2i∑ Im(conj(hᵢ)wᵢ)). Each sum uses only coordinates in F, so the shift "
                + "profile h may be arbitrary.",
                DescribeRole.Definition),
            Entry("coherent-vector", "coherentShiftChar_eq_weyl_vacuum_of_summable", "Coherent vector realization",
                "For a square-summable profile h, synthesize the vector η from its Hilbert basis "
                + "coordinates. The displacement of the vacuum by η is a unit vector with the specified "
                + "Weyl coefficient for every finite-mode displacement. Conjugation by the displacement "
                + "gives the phase with a positive factor of 2 in the exponent."),
            Entry("gaussian-average", "coherentShiftChar_gaussian_avg", "Exact finite Gaussian average",
                "Multiply the characteristic function by another vacuum factor and integrate with "
                + "planar Lebesgue measure in each mode. The normalization is π⁻¹ per mode. "
                + "When hᵢ = a + ib and wᵢ = x + iy, the exponent in that mode is "
                + "−x² − y² + 2i(ay − bx). Its normalized integral is exp(−a² − b²), "
                + "so the full integral is ∏ exp(−|hᵢ|²), including the empty product."),
            Entry("folium", "CoherentShiftInFockFolium", "Countable Fock folium",
                "A countable family of Fock vectors has total squared norm one and its "
                + "summed vector coefficients reproduce the coherent characteristic function on every finite mode set.",
                DescribeRole.Definition),
            Entry("folium-criterion", "coherentShift_in_fock_folium_iff", "Exact square-summability criterion",
                "Finite occupation coordinates capture a positive amount of the total squared norm. "
                + "On mode sets outside their combined support, the finite-mode vacuum projection retains "
                + "at least that amount. Gaussian averaging equates this projection mass with "
                + "exp(−∑|hᵢ|²), so taking logarithms bounds the finite squared-norm sums. "
                + "For the converse, the single coherent vector realizes the folium."),
            Entry("outside-folium", "coherentShift_not_in_fock_folium_of_not_summable", "Nonsummable shifts lie outside the Fock folium",
                "A profile whose squared coordinates are nonsummable admits no countable Fock folium representation."),
            Entry("finite-displacement", "finiteModeDisplacement", "Finite-support displacement",
                "Extend the complex tuple by zero outside the indicated finite set.",
                DescribeRole.Definition),
            Entry("finite-synthesis", "finiteModeSynthesis", "Hilbert-basis synthesis",
                "Sum the Hilbert basis vectors weighted by the finitely supported complex coordinates.",
                DescribeRole.Definition),
            Entry("shifted-representation", "shiftedFockRep", "Phase-shifted Fock representation",
                "Multiply the Fock Weyl operator of a finitely supported displacement by the "
                + "character exp(2i∑ Im(conj(hᵢ)wᵢ)). The phase has modulus one for every profile h.",
                DescribeRole.Definition),
            Entry("shifted-cstar-representation", "shiftedFockCStarRep", "Representation of the common C-star algebra",
                "For each displacement, the shifted operators form a norm-bounded family over all "
                + "profiles. These families generate a norm-closed star algebra. Evaluating at h "
                + "gives the unital star algebra representation on the occupation Fock space.",
                DescribeRole.Definition),
            Entry("weyl-relation", "shiftedFockRep_mul", "Weyl product relation",
                "The shift character is multiplicative under addition of displacements. "
                + "The original Weyl multiplier therefore governs the product of the shifted operators."),
            Entry("weyl-identity", "shiftedFockRep_zero", "Zero displacement",
                "The phase at zero is one and the zero Weyl displacement is the identity operator."),
            Entry("weyl-adjoint", "shiftedFockRep_adjoint", "Adjoint of a shifted Weyl operator",
                "Taking the adjoint negates the displacement. The Weyl relation and the zero-displacement "
                + "identity then give unitarity."),
            Entry("vacuum-coefficient", "shiftedFockRep_vacuum_inner", "Vacuum coefficient of the shifted representation",
                "The normalized Fock vacuum gives the coherent characteristic function at every finite-mode displacement."),
            Entry("scalar-commutant", "shiftedFockRep_scalar_commutant", "Scalar commutant",
                "Divide out the nonzero scalar phases. Strong continuity then extends commutation "
                + "from finite displacements to all one-particle vectors, so every commutant operator is scalar."),
            Entry("cyclic-vacuum", "shiftedFockRep_cyclic", "Cyclicity of the Fock vacuum",
                "Finite-mode displacements of the vacuum are nonzero multiples of coherent exponential vectors. "
                + "Density of the finite-mode one-particle space and totality of the exponential vectors "
                + "give a dense orbit span."),
            Entry("shifted-disjointness", "shiftedFockRep_disjoint_of_diff_not_summable", "Strict disjointness of concrete shifts",
                "For profiles with a nonsummable squared difference, every bounded intertwiner "
                + "between their phase-shifted Fock representations vanishes. A nonzero intertwiner "
                + "would give a unitary equivalence and hence a Fock vector for the relative shift, "
                + "contrary to the square-summability criterion."),
            Entry("gns-disjointness", "coherentShift_gns_disjoint_of_diff_not_summable", "Strict disjointness of cyclic Weyl representations",
                "Use a common Weyl system on finitely supported displacements with symplectic form "
                + "twice the imaginary part of the one-particle inner product. Cyclic realizations "
                + "of the two coherent characteristics have zero bounded intertwiners when the profile "
                + "difference has nonsummable squared norm. Products of generators determine the inner "
                + "products between Weyl translates and identify each cyclic representation with its "
                + "concrete Fock model."),
            Entry("memory-representation", "memorySectorRep", "Dyadic memory representation",
                "Evaluate the common algebra generator for the given finite displacement in the "
                + "representation with natural-number modes and constant shift coordinate m√(log 2).",
                DescribeRole.Definition),
            Entry("uncountable-family", "uncountable_pairwise_disjoint_memory_sectors", "Uncountably many disjoint memory sectors",
                "For distinct real memory parameters, every bounded operator intertwining "
                + "the representations on all finite tuples is zero. The real parameterization "
                + "is injective and its range is uncountable."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(NullLocal, NullCone),
            Blocks(Paragraph(Text(statement))), role);
}
