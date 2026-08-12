using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class TranslationCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semantically composable approximate translations add error and compose resources.",
        H("Composition of Approximate Translations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partial-resource-controlled-translation"),
                DeclarationHandle.Create("D5/S0/Naming/TranslationComposition.Translation"),
                H("Partial resource-controlled translation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A translation carries a partial name map, an isometric embedding between "
                    + "meaning spaces, a conditional semantic-error bound, and a monotone "
                    + "natural-valued resource modulus. The semantic bound is required exactly "
                    + "when the source and target partial assignments both have values."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("semantic-composability"),
                DeclarationHandle.Create("D5/S0/Naming/TranslationComposition.SemanticallyComposable"),
                H("Semantic composability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every point of the ordinary composite map domain whose two endpoint "
                    + "meanings exist, semantic composability requires the intermediate meaning "
                    + "to exist as well. This makes the source phrase composition is defined "
                    + "precise for partial semantic assignments; without it, both component "
                    + "semantic bounds could hold vacuously while the composite bound fails."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("translation-composition-adds-tolerance"),
                DeclarationHandle.Create("D5/S0/Naming/TranslationComposition.translation_composition"),
                H("Translation composition adds tolerance"),
                StatementSource.FromAuthor(Equal(
                    Call("tolerance", Call("compose", Id("translation2"), Id("translation1"))),
                    Add(Id("epsilon1"), Id("epsilon2")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two semantically composable translations admit a translation on the "
                    + "standard composite domain. Its name map and isometric embedding are the "
                    + "corresponding function composites, its tolerance is epsilon1 plus "
                    + "epsilon2, and its resource modulus is modulus2 composed with modulus1. "
                    + "The semantic estimate is the metric triangle inequality with the second "
                    + "embedding's distance preservation; the resource estimate uses monotonicity."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Naming/NamingSystem")),
        ]));

}
