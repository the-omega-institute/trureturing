using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineHornerPart05Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer Horner recurrence 5", H("Integer Horner recurrence 5"), Blocks(
            Paragraph(Text("The coefficient list and private integer vectors are fixed in the data module. Every displayed step is equality of functions on Fin(8192), checked with kernel reduction.")),
            Describe.Lean(DescribeId.Create("step20"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step20"),
                H("step20"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(20)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(76659122475479), Num(0))), Call("state", Num(21), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step21"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step21"),
                H("step21"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(21)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(0), Num(0))), Call("state", Num(22), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step22"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step22"),
                H("step22"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(22)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Call("Negate", Num(450854928573687)), Num(0))), Call("state", Num(23), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step23"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart05.step23"),
                H("step23"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(23)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(0), Num(0))), Call("state", Num(24), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
