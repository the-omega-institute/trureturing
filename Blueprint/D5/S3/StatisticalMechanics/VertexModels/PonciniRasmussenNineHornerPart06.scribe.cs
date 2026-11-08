using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineHornerPart06Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer Horner recurrence 6", H("Integer Horner recurrence 6"), Blocks(
            Paragraph(Text("The coefficient list and private integer vectors are fixed in the data module. Every displayed step is equality of functions on Fin(8192), checked with kernel reduction.")),
            Describe.Lean(DescribeId.Create("step24"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart06.step24"),
                H("step24"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(24)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(2162620108980042), Num(0))), Call("state", Num(25), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step25"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart06.step25"),
                H("step25"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(25)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(0), Num(0))), Call("state", Num(26), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step26"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart06.step26"),
                H("step26"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(26)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Call("Negate", Num(8462844884056308)), Num(0))), Call("state", Num(27), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step27"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart06.step27"),
                H("step27"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(27)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(0), Num(0))), Call("state", Num(28), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
