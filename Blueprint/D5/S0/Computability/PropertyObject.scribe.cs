using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class PropertyObjectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Property objects are losslessly equivalent to their seven typed components.",
        H("Internal Property Objects"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("property-objects-have-seven-lossless-components"),
                DeclarationHandle.Create("D5/S0/Computability/PropertyObject.property_object_components_bijective"),
                H("Property objects have seven lossless components"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Bijective")), Open,
                    Operatorname, Grp(F.Id("encodePropertyComponents")), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An internal property object stores exactly seven typed components: "
                        + "its generation history, encoding, finite reading, ledger, self-code, "
                        + "dynamic update, and certificate. The formal equivalence forgets only "
                        + "the field names, sending the object to the nested product of those "
                        + "components. Its inverse rebuilds every field, and both round trips are "
                        + "proved. Bijectivity therefore certifies that internalization neither "
                        + "drops information nor adds an untracked component.")),
                    Paragraph(Text(
                        "The strict product stores each component in the same position as the "
                        + "standard tuple. Rebuilding the object gives the left inverse used for "
                        + "injectivity. Rebuilding the tuple gives the right inverse used for "
                        + "surjectivity."))),
                DescribeRole.Theorem))));
}
