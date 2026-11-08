using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineDiagramsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Checked nine-strand matching coordinates", H("Checked nine-strand matching coordinates"), Blocks(
            Paragraph(Text("There are 4862 indexed literal matchings. Raw partner data are packed as base-18 integers: the digit at position x is the partner of x. The circular boundary lists the top ports left to right and the bottom ports right to left. All involution, no-fixed-point, noncrossing and transition facts are checked by kernel reduction. No completeness or faithful-representation assertion is needed.")),
            Describe.Lean(DescribeId.Create("diagram"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.diagram"),
                H("diagram"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(4862)), Equal(Call("diagram", Id("i")), Call("Subtype", Call("toMatching", Call("matching", Id("i"))), Call("ExistsWitness", Call("matching", Id("i")), Id("rfl"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Matching(i) is the NCMatching with the decoded partner function and the checked validity proofs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transition"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.transition"),
                H("transition"), StatementSource.FromAuthor(Disp(All("g", Call("Fin", Num(8)), All("i", Call("Fin", Num(4862)), Equal(Call("transition", Id("g"), Id("i")), Call("Modulo", Call("Divide", Call("get", Call("get", Id("transitions"), Call("val", Id("i"))), Num(0)), Call("Power", Num(4863), Call("val", Id("g")))), Num(4863))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The code 4862 denotes a loop and hence zero. Other codes denote the reconnected target diagram. IndexBound is the finite-index inequality supplied by the generator type."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transition-check"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.transition_check"),
                H("transition_check"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(4862)), All("g", Call("Fin", Num(8)), new Formula.Logic(new Formula.Logic(Equal(Call("mate", Call("val", Call("diagram", Id("i"))), Call("Pair", Id("False"), Call("val", Id("g")))), Call("Pair", Id("False"), Call("Add", Call("val", Id("g")), Num(1)))), FormulaLogicOperator.Iff, Equal(Call("val", Call("transition", Id("g"), Id("i"))), Num(4862))), FormulaLogicOperator.And, All("ht", Call("Less", Call("val", Call("transition", Id("g"), Id("i"))), Num(4862)), All("x", Call("Boundary", Num(9)), Equal(Call("mate", Call("val", Call("diagram", Call("transition", Id("g"), Id("i")))), Id("x")), Call("reconnected", Call("val", Id("g")), Id("IndexBound"), Call("val", Call("diagram", Id("i"))), Id("x")))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The two generator ports are paired precisely for a zero transition. Each nonzero target has exactly the reconnected partner function."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unit-check"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.unit_check"),
                H("unit_check"), StatementSource.FromAuthor(Disp(All("x", Call("Boundary", Num(9)), Equal(Call("mate", Call("val", Call("diagram", Num(4861))), Id("x")), Call("mate", Call("identityMatching", Num(9)), Id("x")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The last coordinate is the actual through-strand identity matching."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
