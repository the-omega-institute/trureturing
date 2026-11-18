using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourPointIdentityKDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Original Four-Point Identity from the Actual Channel Germs.",
        H("The Original Four-Point Identity from the Actual Channel Germs"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-channel-a"),
                DeclarationHandle.Create(Prefix + "actualChannelA"),
                H("Actual A germ"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The iterate Laurent series in (1−z)/z is summed over charge sectors with the original quadratic and Fourier signs."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-channel-b"),
                DeclarationHandle.Create(Prefix + "actualChannelB"),
                H("Actual B germ"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the original lowered row at weights K and L with the inputs Q, R, P. "
                    + "The common scalar inserts the prefactor 2¹²z^(m+n+r+2)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-channel-d"),
                DeclarationHandle.Create(Prefix + "actualChannelD"),
                H("Actual D germ"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the lowered row at weights H and L with the inputs P, R, Q in the inverse coordinate. "
                    + "Sum it with the original shifted quadratic signs."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("identity-k-of-common-four-point-germ"),
                DeclarationHandle.Create(Prefix + "identityK_of_common_four_point_germ"),
                H("The residue identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each output sector take the residues of the weighted common germ. "
                    + "At zero it gives 2¹² times channel B. "
                    + "At one it gives the negative of the signed A sum. "
                    + "At infinity it gives the negative of the signed D sum."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("identity-k-of-common-actual-channel-germs"),
                DeclarationHandle.Create(Prefix + "identityK_of_common_actual_channel_germs"),
                H("The original signed-mode identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary integer modes, the exact sewn numerator supplies each coefficient premise, including all lowered B and D rows. "
                    + "A common holomorphic function with the three specified actual germs gives the original charge-coset law."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("identity-k-of-native-chart-germs"),
                DeclarationHandle.Create(Prefix + "identityK_of_native_chart_germs"),
                H("The identity from native chart overlaps"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Holomorphic native continuations with the three specified local germs, an A/B interior equality accumulation and a D interior equality accumulation supply the common function. "
                    + "Identifying the physical chart products with these local germs and proving the occupied-channel overlap equalities remains open."))),
                DescribeRole.Theorem))));
}
