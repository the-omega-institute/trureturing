using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class ObjectDomainArenaDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/ObjectDomainArena.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite collection of readout states can refer to a domain of objects without a finiteness assumption.",
        H("ObjectDomainArena"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("object-domain-arena"),
                DeclarationHandle.Create(Prefix + "ObjectDomainArena"),
                H("Source objects and finite readouts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The domain records the type of objects named by the theorem. The inherited "
                    + "finite arena still supplies states, a typed primitive signature, and a law "
                    + "for the selected realization. No enumeration of the object domain is needed."))),
                DescribeRole.Definition))));
}
