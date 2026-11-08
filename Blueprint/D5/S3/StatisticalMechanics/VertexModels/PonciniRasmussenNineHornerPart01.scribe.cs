using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineHornerPart01Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer Horner recurrence 1", H("Integer Horner recurrence 1"), Blocks(
            Paragraph(Text("The coefficient list and private integer vectors are fixed in the data module. Every displayed step is equality of functions on Fin(8192), checked with kernel reduction.")),
            Describe.Lean(DescribeId.Create("step4"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart01.step4"),
                H("step4"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(4)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(12285), Num(0))), Call("state", Num(5), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step5"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart01.step5"),
                H("step5"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(5)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(0), Num(0))), Call("state", Num(6), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step6"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart01.step6"),
                H("step6"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(6)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Call("Negate", Num(569445)), Num(0))), Call("state", Num(7), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step7"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart01.step7"),
                H("step7"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(7)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(0), Num(0))), Call("state", Num(8), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
