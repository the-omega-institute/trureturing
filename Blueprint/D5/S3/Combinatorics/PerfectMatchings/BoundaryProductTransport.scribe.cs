using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class BoundaryProductTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transport of the unaffected boundary product.",
        H("Transport of the unaffected boundary product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("product"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/BoundaryProductTransport.unaffected_opening_product"),
                H("Transport of the unaffected boundary product"), StatementSource.FromAuthor(new Formula.Layout(FormulaLayoutMode.Display, All("L", V("Type"), All("m", V("Natural"), All("M", Call("NCMatching", Add(V("m"), Num(2))), All("j", Call("Fin", Add(V("m"), Num(1))), All("q", Call("Function", V("L"), V("Real")), All("y", Call("Function", Call("Fin", Add(V("m"), Num(1))), V("L")), All("b", V("L"), Equal(Call("UnchangedOpeningProduct", V("q"), V("M"), V("j"), Call("DetourLabels", V("j"), V("y"), V("b"))), Call("ShortUnchangedOpeningProduct", V("q"), V("M"), V("j"), V("y")))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("OpeningProduct is the product over all endpoints of the opening factor, which is q(x(a+1))/q(x(a)) when a is smaller than its partner and is 1 otherwise. UnchangedOpeningProduct restricts this product to the original Unchanged predicate; ShortUnchangedOpeningProduct restricts the shorter product to ShortUnchanged. ChangedOpeningProduct and ShortChangedOpeningProduct use the respective complementary predicates. Every arc whose endpoints survive without rewiring has the same opening factor before and after insertion. The increasing survivor equivalence transports the full product over these unaffected arcs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("split"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/BoundaryProductTransport.opening_products_split"),
                H("Transport of the unaffected boundary product"), StatementSource.FromAuthor(new Formula.Layout(FormulaLayoutMode.Display, All("L", V("Type"), All("m", V("Natural"), All("M", Call("NCMatching", Add(V("m"), Num(2))), All("j", Call("Fin", Add(V("m"), Num(1))), All("q", Call("Function", V("L"), V("Real")), All("y", Call("Function", Call("Fin", Add(V("m"), Num(1))), V("L")), All("b", V("L"), Both(Equal(Call("OpeningProduct", V("q"), V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), Multiply(Call("ChangedOpeningProduct", V("q"), V("M"), V("j"), Call("DetourLabels", V("j"), V("y"), V("b"))), Call("ShortUnchangedOpeningProduct", V("q"), V("M"), V("j"), V("y")))), Equal(Call("OpeningProduct", V("q"), Call("CapSurgery", V("M"), V("j")), V("y")), Multiply(Call("ShortChangedOpeningProduct", V("q"), V("M"), V("j"), V("y")), Call("ShortUnchangedOpeningProduct", V("q"), V("M"), V("j"), V("y")))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original and shorter boundary products split into their affected factors and the common unaffected product. This keeps all other components and imposes no relation on their weights."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
}
