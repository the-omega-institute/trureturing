using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddDifferenceOne;

internal sealed class ActualLeechDifferenceOneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict mode words in finite homogeneous representatives span the actual Leech negative twisted sector.",
        H("Difference-one spanning for the actual Leech sector"),
        Blocks(
            Describe.Lean(DescribeId.Create("leech-odd-difference-one"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/Orbifold/"
                    + "OddDifferenceOne/ActualLeech.leech_odd_difference_one"),
                H("Difference-one spanning from a nonzero seed"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The spanning conclusion of Miyamoto's Lemma 2.4 "
                    + "(arXiv:math/0209101) is specialized to the actual negative twisted sector. "
                    + "Project lifts of a finite generating family of the fixed C2 quotient to homogeneous fixed "
                    + "states, then project the C2 products of arbitrary fixed states to each weight. "
                    + "In each weight, the representatives of that weight and homogeneous minus-two products "
                    + "of that weight span all homogeneous fixed states of that weight. "
                    + "The resulting representative word span contains the seed and is stable under all fixed "
                    + "modes. Irreducibility gives the full sector."))), DescribeRole.Theorem))));
}
