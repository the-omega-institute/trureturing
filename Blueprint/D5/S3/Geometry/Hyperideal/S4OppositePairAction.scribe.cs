using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class S4OppositePairActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite action on opposite edge pairs",
        H("A concrete S4 action on the three pairings of four vertices"),
        Blocks(
            Paragraph(Text("The six edge slots are 01, 02, 03, 23, 13, and 12. The three pair slots record the opposite edge pairings 01|23, 02|13, and 03|12. For each permutation of the four vertices, inducedPairAction records the resulting permutation of these three pair slots.")),
            Describe.Lean(
                DescribeId.Create("s4-opposite-pair-action-bijective"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/S4OppositePairAction.induced_pair_action_bijective"),
                H("Every induced action is a bijection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A finite kernel computation verifies that the action induced by every permutation of the four vertices is bijective on the three opposite pair slots.")),
                    Paragraph(Text("This is a concrete finite action calculation. It does not assert a global geometric automorphism or a general theorem about all face pairings."))
                ),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("s4-opposite-pair-action-image-card"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/S4OppositePairAction.opposite_pair_action_image_card"),
                H("The induced action has six distinct outputs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The finite image of inducedPairAction has cardinality six. Thus the explicit four-vertex action reaches all six possible permutations of the three pair slots.")),
                    Paragraph(Text("The computation concerns this displayed finite table only. It does not by itself identify a geometric realization or establish an abstract quotient map beyond the enumerated action."))
                ),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("s4-opposite-pair-action-four-kernel-elements"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/S4OppositePairAction.four_named_kernel_elements"),
                H("Four explicit permutations act trivially"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The identity and the three displayed double swaps (01)(23), (02)(13), and (03)(12) all fix the three opposite pair slots. The finite proof also checks that these four vertex permutations are pairwise distinct.")),
                    Paragraph(Text("This supplies four explicit elements of the kernel of the displayed action. A separate exact kernel classification and the associated abstract group identification are outside this module. The faithful source-bound escape audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/19015."))
                ),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("s4-opposite-pair-action-transposition"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/S4OppositePairAction.transposition_generates_pair_swap"),
                H("A vertex transposition swaps two pair slots"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The transposition exchanging vertices 0 and 1 induces the pair-slot permutation [0, 2, 1]."))
                ),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("s4-opposite-pair-action-three-cycle"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/S4OppositePairAction.three_cycle_generates_pair_cycle"),
                H("A vertex three-cycle rotates the pair slots"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The cycle 0 -> 1 -> 2 -> 0 induces the pair-slot permutation [2, 0, 1]. Together with the transposition computation and the six-element image count, this gives the concrete finite S4-to-three-slot interface."))
                ),
                DescribeRole.Theorem)
        )
    ));
}
