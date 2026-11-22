using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RationalJointCircuitImageDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RationalJointCircuitImage";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational cycle representatives of saturated reads.",
        H("Rational representatives of saturated circuit readouts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rational-joint-restriction-equiv"),
                DeclarationHandle.Create(Module + ".rationalJointRestriction_equiv"),
                H("Rational cycles and the saturation of the joint image"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a nonempty ground, a rational top cycle with integral circuit readouts "
                    + "determines a saturated integral tuple. Clearing a common denominator gives an "
                    + "integral source cycle for a nonzero multiple of the tuple. Conversely, dividing "
                    + "an integral lift by that multiple gives a rational representative. Injectivity of "
                    + "joint restriction makes the representative unique. The comparison identifies the "
                    + "integral cycles with the original image and induces an equivalence on the two "
                    + "quotients."))),
                DescribeRole.Theorem))));
}
