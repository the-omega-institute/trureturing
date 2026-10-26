using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class NonclosedCapPotentialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact nonclosed-cap boundary potential.",
        H("Exact nonclosed-cap boundary potential"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("potential"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/NonclosedCapPotential.nonclose_boundaryPotential"),
                H("Exact nonclosed-cap boundary potential"), StatementSource.FromAuthor(FormulaDsl.Disp(All("L", V("Type"), All("m", V("Natural"), All("M", Call("NCMatching", Add(V("m"), Num(2))), All("j", Call("Fin", Add(V("m"), Num(1))), All("q", Call("Function", V("L"), V("Real")), All("y", Call("Function", Call("Fin", Add(V("m"), Num(1))), V("L")), All("b", V("L"), Implies(NotEqual(Call("Partner", V("M"), Call("CastSucc", V("j"))), Call("Succ", V("j"))), Implies(All("a", V("L"), NotEqual(Call("Apply", V("q"), V("a")), Num(0))), Implies(Call("Compatible", V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), Equal(Multiply(Call("BoundaryPotential", V("q"), V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), Call("Divide", Call("Apply", V("q"), V("b")), Call("Apply", V("q"), Call("Apply", V("y"), V("j"))))), Call("BoundaryPotential", V("q"), Call("CapSurgery", V("M"), V("j")), V("y"))))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary finite label type and everywhere nonzero real weights, a compatible detour satisfies the nonclosed-cap potential identity. The affected opening factors cancel using nonvanishing, while the entire unaffected product remains common. No positivity, eigenvector equation, or special label graph is assumed."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
