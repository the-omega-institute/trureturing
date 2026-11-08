using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineHornerPart10Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer Horner recurrence 10", H("Integer Horner recurrence 10"), Blocks(
            Paragraph(Text("The coefficient list and private integer vectors are fixed in the data module. Every displayed step is equality of functions on Fin(8192), checked with kernel reduction.")),
            Describe.Lean(DescribeId.Create("step40"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart10.step40"),
                H("step40"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(40)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(272486148975235188), Num(0))), Call("state", Num(41), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step41"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart10.step41"),
                H("step41"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(41)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(0), Num(0))), Call("state", Num(42), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step42"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart10.step42"),
                H("step42"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(42)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Call("Negate", Num(166252500600659604)), Num(0))), Call("state", Num(43), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("step43"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerPart10.step43"),
                H("step43"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(8192)), Equal(Call("Add", Call("sparseHamiltonian", Call("state", Num(43)), Id("i")), Call("If", Equal(Call("val", Id("i")), Num(4861)), Num(0), Num(0))), Call("state", Num(44), Id("i")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Function extensionality combines the split kernel-checked integer coordinate equalities."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
