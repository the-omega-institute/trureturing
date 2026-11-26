using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteEliminationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteElimination";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact elimination for the six-site special fiber",
        H("Exact elimination for the six-site special fiber"),
        Blocks(
            Claim("specialFiber_unique", "Unique physical invariant triple",
                "Six polynomial consequences yield a factored degree-24 eliminant in the squared-modulus projection. Its degree-16 factor is positive on the nonnegative axis. The specialization at four has negative second-coordinate squared modulus, and the specialization at twenty-six gives the physical triple."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpssixsiteelimination-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
