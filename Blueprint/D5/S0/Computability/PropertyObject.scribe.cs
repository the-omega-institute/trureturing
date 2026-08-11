using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class PropertyObjectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Computability/PropertyObject",
            "Property objects are losslessly equivalent to their seven typed components."),
        H("Internal Property Objects"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("property-objects-have-seven-lossless-components"),
                H("Property objects have seven lossless components"),
                LeanTheorem(
                    "D5/S0/Computability/PropertyObject."
                    + "property_object_components_bijective"),
                Disp(Seq(
                    Operatorname, Grp(F.Id("Bijective")), Open,
                    Operatorname, Grp(F.Id("propertyObjectEquivComponents")), Close)),
                DescribeProvenance.RepoDerived(),
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
                        "The pinned library was searched before implementation. It provides "
                        + "standard product equivalences such as Equiv.prodAssoc and "
                        + "Equiv.prodCongr, together with bundled bijectivity through "
                        + "Equiv.bijective, but it has no declaration for this source-specific "
                        + "seven-component property object. The Lean module consequently "
                        + "constructs only that local structure equivalence and delegates the "
                        + "final theorem to the library's bijectivity API. The source atom is "
                        + "a structural definition and carries no numerical certificate.")))
            ))));
}
