using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class AdjacentCapSurgeryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent cap removal in a noncrossing matching.",
        H("Adjacent cap removal in a noncrossing matching"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reconnect"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery.capSurgery_reconnect"),
                H("Adjacent cap removal in a noncrossing matching"), StatementSource.FromAuthor(FormulaDsl.Disp(All("m", V("Natural"), All("M", Call("NCMatching", Add(V("m"), Num(2))), All("j", Call("Fin", Add(V("m"), Num(1))), All("k", Call("Fin", V("m")), Equal(Call("SkipPair", V("j"), Call("Partner", Call("CapSurgery", V("M"), V("j")), V("k"))), Call("ReconnectPartner", V("M"), V("j"), Call("SkipPair", V("j"), V("k")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The increasing survivor map identifies the smaller partner with the exact original rewiring. The already-paired case and every possible relative order of the two original partners are retained, including an empty surviving frontier."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
