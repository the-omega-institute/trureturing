using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSOneSiteAmbiguityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSOneSiteAmbiguity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic one-site ambiguity for periodic binary bond-two states",
        H("Generic one-site ambiguity for periodic binary bond-two states"),
        Blocks(
            Claim("arbitrarily_close_one_site_collisions", "Collective rotations inside a one-site fiber",
                "Rotate every physical leg by the exponential of the same one-site density times an imaginary parameter. The one-site density commutes with the rotation. The derivative of the adjacent pair density is the commutator with the sum of the two local generators, multiplied by the imaginary unit."),
            Claim("actual_locus_open_dense", "Density of the commutator witness",
                "The commutator is continuous in the amplitudes and real analytic in the tensor entries. A common parity presentation gives a nonzero commutator entry at every ring length at least four. The real analytic identity theorem gives density on the parameter space, which maps continuously onto the actual state image."),
            Claim("generic_one_site_ambiguity", "Nearby unit-phase classes in the same fiber",
                "Each state on the relatively open dense locus has arbitrarily close actual competitors with identical one-site density and different adjacent pair density. A unit phase would preserve the adjacent pair density."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-one-site-ambiguity-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
