using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class BKMLogarithmicMeanInverseDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/hiaikosakipetzruskai2013monotonemetrics");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The matrix power integral and the resolvent logarithmic derivative are inverse "
        + "complex-linear maps, also on every unital star-subalgebra containing the base.",
        H("Inverse of the BKM logarithmic mean"),
        Blocks(
            Entry("inverse-identities", "inverse_identities", "Both inverse identities",
                "In the spectral basis of the positive definite matrix D, the actual power "
                + "integral multiplies entry (i,j) by the logarithmic mean of the corresponding "
                + "eigenvalues. The actual resolvent integral multiplies by its reciprocal. "
                + "The mean equals the common positive eigenvalue when the eigenvalues coincide. "
                + "Cancellation works entrywise for every complex matrix. Hiai, Kosaki, Petz, and Ruskai "
                + "give the inverse pair in equations (1.1)–(1.2) and Appendix C.2.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Entry("ambient-equivalence", "omegaEquiv", "Complex-linear equivalence",
                "The derivative of the matrix exponential at log D acts by the "
                + "actual power integral. The inverse identities make this map bijective.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Entry("ambient-forward", "omegaEquiv_apply", "Power-integral action",
                "The forward map on the full matrix space is the power integral in equation (1.2).",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Entry("ambient-inverse", "omegaEquiv_symm_apply", "Resolvent action",
                "The inverse on the full matrix space is the resolvent integral in equation (1.1).",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Entry("restriction", "omegaRestrict", "Automorphism of a star-subalgebra",
                "The real powers lie in the unital star-subalgebra containing D by "
                + "continuous functional calculus. Its closed complex subspace contains "
                + "the average. Injectivity and finite dimension give surjectivity.",
                DescribeRole.Definition),
            Entry("restricted-forward", "omegaRestrict_apply", "Restriction of the power integral",
                "The restricted forward map agrees with the matrix power integral after inclusion.",
                DescribeRole.Theorem),
            Entry("restricted-inverse", "omegaRestrict_symm_apply", "Restriction of the resolvent integral",
                "Uniqueness of the ambient inverse identifies the restricted inverse with "
                + "the actual resolvent logarithmic derivative on every complex subalgebra element.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string text,
        DescribeRole role, AssessedProvenance? provenance = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
