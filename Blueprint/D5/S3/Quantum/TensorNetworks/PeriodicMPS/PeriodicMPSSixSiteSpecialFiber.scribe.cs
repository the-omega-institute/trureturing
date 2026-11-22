using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteSpecialFiberDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteSpecialFiber";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two actual six-site rays over a specified adjacent marginal",
        H("Two actual six-site rays over a specified adjacent marginal"),
        Blocks(
            Claim("actual_specialFiber", "Exhausting the actual competitors",
                "Every actual periodic bond-two core with the specified marginal up to a real gain has one of two phase-fixed necklace rays."),
            Claim("nilpotentRay_realized", "Actual periodic realizations",
                "Every complex point in the nilpotent chart is realized by a periodic bond-two core."),
            Claim("secondPhase_same_gram", "Coincident observations",
                "The two rays have the same full adjacent two-site matrix."),
            Claim("distinct_specialRays", "Distinct amplitude rays",
                "Both rays have alternating triple amplitude one and differ at the opposite-pair amplitude."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpssixsitespecialfiber-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
