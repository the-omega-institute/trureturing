using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class SL2F5ExplicitPacketDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit matrices for the SL2(F5) center-lift packet",
        H("A finite matrix packet for the binary icosahedral obstruction"),
        Blocks(
            Paragraph(Text("Work in the determinant-one two by two matrices over ZMod 5. The displayed generators are u = [[0,1],[4,1]] and v = [[1,1],[0,1]]. Define lowReturn = v^{-1}u^2, highReturn = v^2u, and centralReturn = vu^3.")),
            Describe.Lean(
                DescribeId.Create("sl2-f5-explicit-relations"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/SL2F5ExplicitPacket.sl2_five_explicit_relations"),
                H("The explicit return-word identities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The finite calculation gives lowReturn^2 = -I, lowReturn^4 = I, and lowReturn != I. It also gives highReturn^3 = I and highReturn != I, so the two displayed return words have orders four and three respectively.")),
                    Paragraph(Text("The same computation verifies u^3 = -I, v^5 = I, u v = lowReturn, centralReturn = -v, and centralReturn^5 = -I. These are exact identities for the supplied matrices over ZMod 5.")),
                    Paragraph(Text("The packet supplies the explicit finite center-lift data used in CFMP section 124. It does not assert a geometric realization, a general covering theorem, or a new identification of the binary icosahedral group. The faithful source-bound escape audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/19034."))
                ),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sl2-f5-cardinality"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/SL2F5ExplicitPacket.sl2_five_cardinality"),
                H("The exact finite group cardinality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The determinant-one matrix group over ZMod 5 has exactly 120 elements, verified by finite computation in the kernel.")),
                    Paragraph(Text("This cardinality is used only as a finite size fact for the explicit packet. It does not by itself supply the group-generation argument or the geometric existence input from the surrounding theory.")),
                    Paragraph(Text("The faithful source-bound escape audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/19034."))
                ),
                DescribeRole.Theorem)
        )
    ));
}
