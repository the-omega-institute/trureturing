using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineHornerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nine-strand integer Horner certificate", H("The nine-strand integer Horner certificate"), Blocks(
            Paragraph(Text("There are 4862 genuine diagram coordinates, padded to 8192 for binary indexing. The unit coordinate is 4861. The fixed incoming table lists every source contributing to each target, with multiplicity and a minus sign. All 58 Horner steps are integer equalities checked by kernel reduction. The certificate asserts only the integer recurrence; its identification with literal diagram multiplication requires the separate action bridge. The coefficient sequence is the monic odd degree-57 integer polynomial from the registered probe.")),
            Describe.Lean(DescribeId.Create("annihilatorcoefficients"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHorner.annihilatorCoefficients"),
                H("annihilatorCoefficients"), StatementSource.FromAuthor(Disp(Equal(Id("annihilatorCoefficients"), Call("CoefficientSequence", Call("Length", Num(58)), Call("MonicOddAnnihilator", Num(9)))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact highest-first list is: 1, 0, -163, 0, 12285, 0, -569445, 0, 18215115, 0, -427662891, 0, 7652877936, 0, -106986874650, 0, 1188246329388, 0, -10605723426434, 0, 76659122475479, 0, -450854928573687, 0, 2162620108980042, 0, -8462844884056308, 0, 26973986982247197, 0, -69786597194594871, 0, 145778728152448221, 0, -244086630072528699, 0, 324477075047489821, 0, -338328989148555271, 0, 272486148975235188, 0, -166252500600659604, 0, 74962166731413102, 0, -24185673946500264, 0, 5347591521504921, 0, -762922848588417, 0, 64282035899880, 0, -2771640702288, 0, 43808164416, 0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sparsehamiltonian"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHorner.sparseHamiltonian"),
                H("sparseHamiltonian"), StatementSource.FromAuthor(Disp(All("v", Call("Function", Call("Fin", Num(8192)), Id("Int")), All("i", Call("Fin", Num(8192)), Equal(Call("sparseHamiltonian", Id("v"), Id("i")), Call("Negate", Call("FoldAdd", Call("Incoming", Id("i")), Call("Compose", Id("v"), Call("Modulo", Num(8192)))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Incoming(i) is the corresponding leaf of the fixed binary row tree, and FoldAdd starts at zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hornervalue"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHorner.hornerValue"),
                H("hornerValue"), StatementSource.FromAuthor(Disp(Equal(Id("hornerValue"), Call("FoldLeft", Id("annihilatorCoefficients"), Call("HornerStep", Id("sparseHamiltonian"), Num(4861)), Id("ZeroVector"))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("HornerStep(v,c)(i) is sparseHamiltonian(v)(i) plus c when i=4861, and plus zero otherwise."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("annihilation"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHorner.annihilation"),
                H("annihilation"), StatementSource.FromAuthor(Disp(Equal(Id("hornerValue"), Id("ZeroVector")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The split chain starts at the zero vector and ends at the zero vector. Each intermediate state is a private binary-tree integer vector."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
