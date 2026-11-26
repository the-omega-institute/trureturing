using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMRelativeDensityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMRelativeDensity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual BKM integral and its order under a relative density sandwich.",
        H("Relative order of the finite BKM coefficient"),
        Blocks(
            Entry("omega", "omega", "BKM power integral",
                "Integrate a^t X a^(1−t) for t between zero and one using the real spectral powers of a.", DescribeRole.Definition),
            Entry("power-coefficient", "powerCoefficient", "Coefficient of the power integrand",
                "In column vectorization the coefficient at t is the Kronecker product of the transpose of a^(1−t) with a^t.", DescribeRole.Definition),
            Entry("omega-coefficient", "omegaCoefficient", "BKM coefficient",
                "The coefficient is the Bochner integral of the power coefficients from zero to one.", DescribeRole.Definition),
            Entry("omega-coefficient-mul-vec", "omegaCoefficient_mulVec", "Action of the integrated coefficient",
                "For positive definite a, multiplication by the coefficient on vec X gives vec (omega a X). The two linear maps commute with the integral.", DescribeRole.Theorem),
            Entry("omega-coefficient-relative-bounds", "omegaCoefficient_relative_bounds", "Relative Loewner bounds",
                "For positive definite a and b with 0 < ℓ ≤ u and ℓb ≤ a ≤ ub, the BKM coefficients obey the same sandwich. Fractional-power monotonicity bounds both factors of the Kronecker product. The complementary exponents recover the original constants before integration.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
