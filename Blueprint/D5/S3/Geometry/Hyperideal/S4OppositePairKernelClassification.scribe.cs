using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class S4OppositePairKernelClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact kernel of the finite action on the three opposite edge pairs.",
        H("Exact S4 kernel for opposite pairings"),
        Blocks(
            Paragraph(Text("For the displayed action of permutations of four vertices on the three opposite edge pairings, a permutation fixes every pair slot exactly when it is the identity or one of the three double swaps (01)(23), (02)(13), and (03)(12).")),
            Paragraph(Text("This classification supplies the missing exact-kernel step for the finite S4-to-three-pair interface. The existing action module supplies the bijectivity, six-element image, and explicit generator calculations; together they identify the finite quotient interface. No global geometric automorphism or extension to arbitrary face pairings is asserted.")),
            Describe.Lean(
                DescribeId.Create("s4-opposite-pair-kernel-classification"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/S4OppositePairKernelClassification.trivial_pair_action_iff"),
                H("The four displayed permutations are exactly the kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite exhaustive proof classifies every permutation of the four vertices: fixing all three opposite pair slots is equivalent to being the identity or one of the three double swaps."))),
                DescribeRole.Theorem))));
}
