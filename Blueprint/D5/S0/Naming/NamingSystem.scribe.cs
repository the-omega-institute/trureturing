using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class NamingSystemDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Naming/NamingSystem",
            "Finite height layers make partial naming systems countable, leaving a null named image."),
        H("Countable Naming Systems"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partial-naming-system-with-finite-height-layers"),
                DeclarationHandle.Create("D5/S0/Naming/NamingSystem.NamingSystem"),
                H("Partial naming system with finite height layers"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A naming system over a measured carrier X consists of a name type N, "
                    + "a partial assignment from N to X represented by an Option-valued map, "
                    + "a natural-valued height, and a proof that every bounded height layer "
                    + "is finite. Uncountability and measure hypotheses are theorem "
                    + "assumptions rather than fields tied to a special carrier."))),
                DescribeRole.Definition
            ),
            DocumentBlock.Describe.Lemma(
                DescribeId.Create("finite-height-layers-make-the-name-type-countable"),
                H("Finite height layers make the name type countable"),
                LeanTheorem("D5/S0/Naming/NamingSystem.name_layer_finite"),
                Call("Countable", Id("N")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Every name lies in the layer indexed by its own height. The name type is "
                    + "therefore a countable union of finite sublevels, so it is countable.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("countable-naming-families-have-null-named-image"),
                H("Countable naming families have null named image"),
                LeanTheorem("D5/S0/Naming/NamingSystem.dark_side_conservation"),
                Equal(Call("mu", Call("namedUnion", Id("systems"))), Num(0)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For a countable family of naming systems on an uncountable carrier with "
                    + "an atomless sigma-finite measure, the union of all points reached by "
                    + "their partial assignments has measure zero. Equivalently, the dark "
                    + "side, its complement, has full measure in complement-null form. The "
                    + "repository proof derives countability through the NamingSystem height "
                    + "layers and delegates the final measure step directly to mathlib's "
                    + "Set.Countable.measure_zero theorem.")))
            ))));

}
