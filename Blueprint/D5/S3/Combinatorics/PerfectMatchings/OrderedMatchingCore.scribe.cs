using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class OrderedMatchingCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered noncrossing matchings and boundary labels.",
        H("Ordered noncrossing matchings and boundary labels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("matching"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore.Compatible"),
                H("Ordered noncrossing matchings and boundary labels"), StatementSource.FromAuthor(new Formula.Layout(FormulaLayoutMode.Display, All("L", V("Type"), All("m", V("Natural"), All("M", Call("NCMatching", V("m")), All("y", Call("Function", Call("Fin", Add(V("m"), Num(1))), V("L")), Equivalent(Call("Compatible", V("M"), V("y")), All("a", Call("Fin", V("m")), Both(Equal(Call("Apply", V("y"), Call("CastSucc", V("a"))), Call("Apply", V("y"), Call("Succ", Call("Partner", V("M"), V("a"))))), Equal(Call("Apply", V("y"), Call("Succ", V("a"))), Call("Apply", V("y"), Call("CastSucc", Call("Partner", V("M"), V("a")))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A matching is a fixed-point-free involution of the ordered endpoints with no strictly alternating arcs. The label compatibility equations identify opposite sides of every pair. The boundary potential is zero for incompatible labels and otherwise is the product of the prescribed real weight ratios over opening endpoints."))),
                DescribeRole.Definition))));

    private static Formula V(string name) => Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
