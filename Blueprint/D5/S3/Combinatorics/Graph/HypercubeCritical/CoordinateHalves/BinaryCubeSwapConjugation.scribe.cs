using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class BinaryCubeSwapConjugationDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single cube translation turns independently complemented star swaps into coordinate transpositions.",
        H("Conjugating the swaps of a coordinate star"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("translate"),
                DeclarationHandle.Create(Module + ".translate"),
                H("Translation of a cube vertex"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Translation by t adds t by coordinatewise XOR."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("translation-involutive"),
                DeclarationHandle.Create(Module + ".translate_involutive"),
                H("Cube translations are involutions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Applying the same translation twice adds each bit twice and returns the starting vertex."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chosen-swap"),
                DeclarationHandle.Create(Module + ".chosenSwap"),
                H("A swap with optional complementation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On distinct coordinates r and j, the map exchanges their bits and XORs both with the same " +
                        "chosen bit. It fixes the other coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conjugating-star-swaps"),
                DeclarationHandle.Create(Module + ".exists_translation_conjugating_star_swaps"),
                H("One translation conjugates all the chosen star swaps"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix a coordinate r and choose a complementation bit independently for each transposition of " +
                        "r and j. Set the translation bit at r to false and the bit at j to that choice. Applying the " +
                        "chosen swap after this translation equals applying the ordinary swap before the translation. " +
                        "Since translation is an involution, the identity gives simultaneous conjugation on the whole " +
                        "coordinate star."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translation-permutation-invariance"),
                DeclarationHandle.Create(Module + ".exists_translation_perm_invariant_of_no_split"),
                H("The translated function is invariant under coordinate permutations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each j distinct from r, suppose double flipping r and j preserves the function either on " +
                        "all vertices with unequal bits at r and j or on all vertices with equal bits there. The " +
                        "unequal-bit hypothesis gives invariance under the ordinary swap, and the equal-bit " +
                        "hypothesis gives invariance under the complemented swap. Each choice acts as the identity on " +
                        "the other class.")),
                    Paragraph(Text("Conjugate the chosen swaps by one translation with its r bit false. The ordinary star " +
                        "transpositions generate every coordinate permutation, since a transposition between two " +
                        "leaves is a product of three star transpositions. Thus the translated function is invariant " +
                        "under precomposition by every coordinate permutation. The codomain can be any type."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translation-layer-constancy"),
                DeclarationHandle.Create(Module + ".exists_translation_hamming_layer_constant"),
                H("The translated function is constant on each Hamming layer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the same star hypothesis, there is a translation whose r bit is false and after which " +
                        "the function has equal values at every pair of vertices of the same Hamming weight. A " +
                        "coordinate permutation sends one such vertex to the other by matching their true-coordinate " +
                        "sets and matching their complements."))),
                DescribeRole.Theorem)),
        []));
}
