using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineDiagramsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal nine-strand diagram coordinates", H("Literal nine-strand diagram coordinates"), Blocks(
            Paragraph(Text("The fixed table has 4862 circular noncrossing matchings. Each partner function is kernel-checked to be a fixed-point-free involution with no interleaving chords. Rectangle boundary conversion gives an element of the full literal diagram algebra. Transition code 4862 denotes zero; a code below 4862 denotes the target diagram. No completeness or faithfulness assertion follows from these definitions alone.")),
            Describe.Lean(DescribeId.Create("diagram"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.diagram"),
                H("diagram"), StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num(4862)), Equal(Call("diagram", Id("i")), Call("DiagramFromMatching", Call("toMatching", Call("CheckedMatching", Call("RawPartnerTable", Id("i"))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("CheckedMatching uses the actual raw partner function, its checked involution law, its no-fixed-point law and its checked noncrossing law."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transition"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams.transition"),
                H("transition"), StatementSource.FromAuthor(Disp(All("g", Call("Fin", Num(8)), All("i", Call("Fin", Num(4862)), Equal(Call("transition", Id("g"), Id("i")), Call("Modulo", Call("Lookup", Call("Lookup", Id("TransitionTree"), Id("i")), Id("g")), Num(4863))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Lookup follows even/odd branches of the binary table. The modulo supplies the finite-index bound."))), DescribeRole.Definition))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
