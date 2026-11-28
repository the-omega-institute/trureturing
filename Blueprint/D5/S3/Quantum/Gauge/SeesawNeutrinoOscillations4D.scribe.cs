using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class SeesawNeutrinoOscillations4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/SeesawNeutrinoOscillations4D.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/nunokawa2008leptoniccp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact seesaw diagonalization and vacuum oscillation identities.",
        H("Type-I seesaw masses and neutrino oscillations"),
        Blocks(
            Paragraph(Text("The seesaw calculation gives signed eigenvalues for one real Dirac and Majorana pair and a Schur block for several flavors. Vacuum propagation assigns a unit complex phase to each mass eigenstate. The interference of these phases yields the three-flavor CP difference.")),
            Definition("seesaw-matrix", "seesawMatrix", "Type-I seesaw matrix",
                "The diagonal contains zero and the Majorana mass. Both off-diagonal entries are the Dirac mass."),
            Definition("heavy-mass", "seesawHeavy", "Heavy mass magnitude",
                "Add the Majorana mass to the square root of the discriminant and halve the sum."),
            Definition("light-mass", "seesawLight", "Light mass magnitude",
                "Subtract the Majorana mass from the square root of the discriminant and halve the difference."),
            Entry("det-trace", "seesaw_det_trace", "Determinant and trace",
                "The determinant is minus the squared Dirac mass. The trace is the Majorana mass."),
            Entry("product-difference", "seesaw_mass_product_and_diff", "Mass product and difference",
                "The two magnitudes multiply to the squared Dirac mass. The heavy magnitude minus the light magnitude equals the Majorana mass."),
            Definition("seesaw-rotation", "seesawRotation", "Oriented eigenvector rotation",
                "The eigenvectors use the heavy and Dirac masses as coordinates and are normalized by a common positive length. When the Dirac mass is zero the ordered coordinate axes give the rotation directly."),
            Entry("diagonalization", "seesaw_orthogonal_diagonalization", "Exact orthogonal diagonalization",
                "The rotation has determinant one, its transpose is its inverse, and the diagonal contains the additive inverse of the light magnitude followed by the heavy magnitude."),
            Entry("exact-correction", "seesaw_exact_correction", "Exact hierarchy correction",
                "For nonzero Majorana mass, subtracting the light magnitude from the seesaw estimate gives the squared light magnitude divided by the Majorana mass."),
            Entry("sharp-hierarchy", "seesaw_strict_hierarchy_bounds", "Strict mass hierarchy",
                "For a positive Majorana mass and a nonzero Dirac mass, the light magnitude lies strictly between zero and the seesaw estimate. The heavy magnitude exceeds the Majorana mass, and the positive error is strictly less than the fourth Dirac power divided by the third Majorana power."),
            Entry("large-majorana", "seesaw_asymptotic_limits", "Large Majorana mass limit",
                "At fixed Dirac mass, the light magnitude tends to zero, its product with the Majorana mass tends to the squared Dirac mass, and the heavy-to-Majorana ratio tends to one."),
            Definition("block-seesaw", "blockSeesaw", "Multiflavor mass block",
                "The leading square block is zero. The off-diagonal blocks are the Dirac matrix and its transpose. The remaining block is the Majorana matrix."),
            Entry("block-congruence", "block_seesaw_schur_congruence", "Exact Schur congruence",
                "A triangular shear removes the off-diagonal blocks when the Majorana matrix is symmetric and invertible. The light block is minus the Dirac matrix times the Majorana inverse times the Dirac transpose."),
            Entry("block-determinant", "block_seesaw_det", "Multiflavor determinant",
                "The determinant is the squared Dirac determinant times minus one to the flavor count. The Schur determinant proof uses invertibility of the Majorana block."),
            Definition("oscillation-amplitude", "oscAmp", "Vacuum transition amplitude",
                "Sum the final-flavor mixing entry times the negative-phase propagation factor times the conjugate of the initial-flavor entry over the mass indices."),
            Definition("oscillation-probability", "oscProb", "Vacuum transition probability",
                "Take the squared complex norm of the amplitude."),
            Entry("probability-nonnegative", "oscProb_nonneg", "Nonnegative probability",
                "The squared norm is nonnegative for every mixing matrix and baseline."),
            Entry("zero-baseline", "oscProb_zero_baseline", "Zero baseline",
                "Row unitarity gives probability one for survival and zero for transition at zero baseline."),
            Entry("unitarity-sums", "oscProb_unitarity_sum", "Probability normalization",
                "The propagation matrix is unitary. Each sum over initial or final flavors is one, and each entry lies at most at one."),
            Entry("common-mass-shift", "oscProb_common_shift_invariant", "Common mass-squared shift",
                "A common mass-squared shift contributes the same unit phase to every summand and cancels in the squared norm."),
            Definition("antineutrino-mixing", "antiMatrix", "Antineutrino mixing matrix",
                "Conjugate each entry of the mixing matrix."),
            Entry("cpt-symmetry", "oscProb_cpt_symmetry", "Vacuum CPT identity",
                "The antineutrino transition probability equals the neutrino probability for the reversed flavor pair."),
            Entry("survival-cp", "oscProb_survival_cp_zero", "Survival probability under conjugation",
                "Conjugating the mixing matrix leaves every survival probability unchanged."),
            Definition("two-flavor-rotation", "rot2", "Two-flavor rotation",
                "The two real rotation entries in each row are embedded in the complex numbers."),
            Entry("two-flavor-probability", "two_flavor_oscProb_formula", "Two-flavor vacuum probability",
                "The transition probability is the product of the squared sine of twice the mixing angle and the squared sine of half the relative phase. Survival is one minus this product."),
            Definition("cp-difference", "cpAsymmetry", "CP difference",
                "Subtract the antiparticle probability from the particle probability for the same ordered flavors."),
            Entry("cp-antisymmetry", "cpAsymmetry_antisymm", "Antisymmetry of the CP difference",
                "Reversing flavors negates the CP difference. The survival difference is zero."),
            Entry("three-flavor-factorization", "three_flavor_cp_asymmetry_jarlskog", "Jarlskog sine product",
                "For three unitary flavors, the CP difference is sixteen times the quartet of the ordered flavors and first two mass indices times the three half-phase sines. The pairs zero-one and one-two have the same quartet sign. The pair zero-two has the opposite sign."),
            Entry("cp-bound", "three_flavor_cp_asymmetry_bound", "Magnitude of the CP difference",
                "The magnitude is bounded by sixteen times the magnitude of the quartet because each sine has magnitude at most one."),
            Entry("cp-zero-criterion", "three_flavor_cp_asymmetry_zero_iff", "Exact zero criterion",
                "The CP difference vanishes exactly when the quartet or one of the three half-phase sines vanishes."),
            Entry("cp-mass-degeneracy", "three_flavor_cp_asymmetry_zero_of_degenerate", "Degenerate mass pair",
                "Equality of any two distinct mass-squared entries makes the corresponding half-phase sine zero."))));

    private static DocumentBlock Definition(string id, string declaration, string title, string statement) =>
        Entry(id, declaration, title, statement, DescribeRole.Definition);

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
