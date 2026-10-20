using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class ClosedCapFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed-cap compatibility and weight transport.",
        H("Closed-cap compatibility and weight transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("labels"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/ClosedCapFiber.close_compatible_iff"),
                H("Closed-cap compatibility and weight transport"), StatementSource.FromAuthor(new Formula.Layout(FormulaLayoutMode.Display, All("L", V("Type"), All("m", V("Natural"), All("M", Call("NCMatching", Add(V("m"), Num(2))), All("j", Call("Fin", Add(V("m"), Num(1))), All("y", Call("Function", Call("Fin", Add(V("m"), Num(1))), V("L")), All("b", V("L"), Implies(Equal(Call("Partner", V("M"), Call("CastSucc", V("j"))), Call("Succ", V("j"))), Equivalent(Call("Compatible", V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), Call("Compatible", Call("CapSurgery", V("M"), V("j")), V("y")))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When the original endpoints already form a pair, the inserted middle label is free. Compatibility of the full detour is equivalent to compatibility of the smaller matching for every middle label."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("potential"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/ClosedCapFiber.close_boundaryPotential"),
                H("Closed-cap compatibility and weight transport"), StatementSource.FromAuthor(new Formula.Layout(FormulaLayoutMode.Display, All("L", V("Type"), All("m", V("Natural"), All("M", Call("NCMatching", Add(V("m"), Num(2))), All("j", Call("Fin", Add(V("m"), Num(1))), All("q", Call("Function", V("L"), V("Real")), All("y", Call("Function", Call("Fin", Add(V("m"), Num(1))), V("L")), All("b", V("L"), Implies(Equal(Call("Partner", V("M"), Call("CastSucc", V("j"))), Call("Succ", V("j"))), Equal(Multiply(Call("BoundaryPotential", V("q"), V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), Call("Divide", Call("Apply", V("q"), V("b")), Call("Apply", V("q"), Call("Apply", V("y"), V("j"))))), Multiply(Call("Square", Call("Divide", Call("Apply", V("q"), V("b")), Call("Apply", V("q"), Call("Apply", V("y"), V("j"))))), Call("BoundaryPotential", V("q"), Call("CapSurgery", V("M"), V("j")), V("y")))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary real weights, multiplying the original boundary potential by the cap weight ratio gives its square times the smaller potential. The identity includes incompatible shorter labellings, where both sides vanish, and real division is the usual total field operation."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
