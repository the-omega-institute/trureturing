using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class LocalEquiconnectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized nonantipodal chords provide coherent local equiconnections on normed unit spheres and transport through homeomorphisms.",
        H("Explicit Sphere Local Equiconnections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-sphere-connector"),
                DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/LocalEquiconnection.sphere"),
                H("Normalized straight interpolation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the subtype sphere of radius one in any real normed space, use the open "
                    + "domain of pairs (p,q) with q≠-p. The connector normalizes (1-s)p+sq for "
                    + "s in [0,1]. Unit norms show that a zero chord would force s=1/2 and q=-p, "
                    + "so normalization is continuous throughout the stated domain. It has both "
                    + "endpoint identities and fixes every diagonal pair for every parameter. "
                    + "Finite dimensionality is unnecessary for this connector data."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("homeomorphism-connector-transport"),
                DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/LocalEquiconnection.transport"),
                H("Transport the domain and connector together"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A homeomorphism e:X→Y pulls back the open pair domain and sends the connector "
                    + "output through e inverse. The continuity and all three identities are "
                    + "transported as data. Applying this to a homeomorphism onto a Euclidean unit "
                    + "sphere supplies genuine topological-sphere data without differentiability "
                    + "or any compatibility between e, the connector and the dynamical map. "
                    + "No compact LEC implies ANR assertion is made."))),
                DescribeRole.Definition))));
}
