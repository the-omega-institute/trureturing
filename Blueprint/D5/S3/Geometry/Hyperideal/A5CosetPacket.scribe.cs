using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class A5CosetPacketDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit twelve-point return permutations",
        H("A finite permutation packet for the A5 coset example"),
        Blocks(
            Paragraph(Text("Let Point be the twelve-element set Fin 12. U and V are the two explicit permutations listed in the Lean source. Define lowReturn = U^2 * V^{-1} and highReturn = U * V^2, where multiplication is permutation composition in the library convention.")),
            Describe.Lean(
                DescribeId.Create("a5-coset-return-periods"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/A5CosetPacket.low_return_has_six_two_cycles"),
                H("The two return cycle counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The first theorem computes that every one of the twelve points is fixed by lowReturn^2 and no point is fixed by lowReturn. Therefore the twelve points split into six two-cycles.")),
                    Paragraph(Text("The second theorem computes that every one of the twelve points is fixed by highReturn^3 and no point is fixed by highReturn. Therefore the twelve points split into four three-cycles.")),
                    Paragraph(Text("These statements verify the displayed finite return data only. They do not establish the classical identification of the generated subgroup with A5, the existence of a geometric realization, or the general non-normal-coset construction. The faithful four-slot escape audit for these public theorems remains unfinished under https://github.com/the-omega-institute/trureturing/issues/19015. The issue records missing registration evidence only; it supplies neither a mathematical proof nor a declared_validated registration."))
                ),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a5-coset-high-return-periods"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/A5CosetPacket.high_return_has_four_three_cycles"),
                H("The high return cycle count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The high return computation has twelve points of period dividing three and no fixed points, so its cycle decomposition consists of four three-cycles.")),
                    Paragraph(Text("This is a concrete finite permutation check. It does not claim the A5 subgroup identification, geometric existence, or a general coset theorem. The faithful four-slot escape audit for this public theorem remains unfinished under https://github.com/the-omega-institute/trureturing/issues/19015. The issue records missing registration evidence only; it supplies neither a mathematical proof nor a declared_validated registration."))
                ),
                DescribeRole.Theorem)
        )
    ));
}
