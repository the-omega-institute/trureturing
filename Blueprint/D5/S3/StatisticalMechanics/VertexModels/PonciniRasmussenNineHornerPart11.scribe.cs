using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineHornerPart11Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer Horner recurrence 11", H("Integer Horner recurrence 11"), Blocks(
            Paragraph(Text("The coefficient list and private integer vectors are fixed in the data module. Every displayed step is equality of functions on Fin(8192), checked with kernel reduction.")),
            Describe.Lean(DescribeId.Create("step44"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart11.step44"),
                H("step44"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(44)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(74962166731413102), Num(0))), Call("state", Num(45), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step45"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart11.step45"),
                H("step45"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(45)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(0), Num(0))), Call("state", Num(46), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step46"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart11.step46"),
                H("step46"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(46)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Call("Negate", Num(24185673946500264)), Num(0))), Call("state", Num(47), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step47"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart11.step47"),
                H("step47"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(47)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(0), Num(0))), Call("state", Num(48), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
