using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteInvariantsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteInvariants";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real invariants of a six-site special marginal",
        H("Real invariants of a six-site special marginal"),
        Blocks(
            Claim("specialEquation_eq_zero", "Elimination equations",
                "The vacuum diagonal, singleton exchange and squared coherence entries give three polynomial constraints after clearing the common gain."),
            Claim("projectedInvariant_eq", "Nonnegative projection",
                "The linear combination used for elimination is the squared modulus of the difference of the two complex coordinates with coefficients one and minus five."),
            Claim("special_chart_of_invariants", "Phase readout",
                "At the physical invariant triple the complex coherence fixes the common phase for each relative orientation."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpssixsiteinvariants-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
