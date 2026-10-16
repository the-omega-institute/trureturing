using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class UnitWordGyrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same cochain on a finite unit word and its collapsed edge",
        H("The same cochain on a finite unit word and its collapsed edge"),
        Blocks(
            Paragraph(Text("The dependent Word here explicitly has a matrix unit at every vertex over GyrationDyadic, the localization of the integers at two. It does not redefine an arbitrary original positive Word as a unit word. An application to singular original intermediates needs the actual quotient construction in FiniteKernelLadder.")),
            Describe.Lean(
                DescribeId.Create("unitwordgyration-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/UnitWordGyration.comp"),
                H("The actual lag-one composite edge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A vertex consists of any natural dimension and a square matrix unit. An edge A to B has rectangular R,S with R*S=A.time and S*R=B.time. All dimensions, including zero, are allowed. Its inverse forward matrix is S*A.time inverse. Both inverse laws are derived using the endpoint units.")),
                    Paragraph(Text("For consecutive edges e,f, the composite forward factor is e.R*f.R and its backward factor is f.inverse*e.S. This actual third factor repairs the composite to lag one; using an arbitrary shift-equivalence square would not supply the RS triangle needed for the cochain."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unitwordgyration-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/UnitWordGyration.comp_weight"),
                H("One literal rectangular triangle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural d with NeZero d and three dividing d, comp_weight states that the dyadicGyration weight of e.comp f equals the sum of the weights of e and f. It applies canonicalLocalizedGyration_triangle at the reduction exponent padicValInt 3 of (2*d)!, to e.R,f.R,f.inverse*e.S. The actual inverse and endpoint equations identify the other two backward factors. The same existing dyadicGyration is used in every term.")),
                    Paragraph(Text("The nil edge has R=1 and S=A.time. Its weight vanishes by the identity-edge triangle and cancellation; vanishing is not assumed for an arbitrary change of basis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitwordgyration-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/UnitWordGyration.collapse_weight"),
                H("Collapse an arbitrary dependent finite word"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For the same nonzero d divisible by three, and every finite Word w from A to B, w.collapse.weight d=w.weight d. The proof is induction on the actual word, with identity_weight in the nil branch and comp_weight in each cons branch. The weight is the recursive sum on the original letters, rather than a cochain defined from the desired final expression.")),
                    Paragraph(Text("The companion collapse_forward identifies the collapsed forward factor with the chronological product e0.R*e1.R*... . Arbitrary length and the dependent intermediate dimensions are retained. A one-cell triangle alone does not state this all-word identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitwordgyration-4"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/UnitWordGyration.loop_one_edge"),
                H("The one-edge value of the actual loop product"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a loop w : Word A A, loopUnit uses the collapsed forward map and its explicitly derived inverse. loop_one_edge states that w.weight d is dyadicGyration d w.forward ((w.loopUnit inverse)*A.time). The collapsed forward map commutes with A.time by the edge intertwining equation.")),
                    Paragraph(Text("The backward factor is identified by inverse_source and collapse_forward. No gamma, cochain conservation premise, bounded numerical instance or positive-dimension assumption is introduced. Conversion to an original-h periodic or beam statement requires its separate actual dictionary and induced-unit identification."))),
                DescribeRole.Theorem),
            Paragraph(Text("The strongest original-h root, its finite calibrations, literal FixT6 and minimum6 are outside these finite algebraic statements. Their separate periodic and beam dictionaries and final acceptance obligations are required to close that original goal.")))));
}
