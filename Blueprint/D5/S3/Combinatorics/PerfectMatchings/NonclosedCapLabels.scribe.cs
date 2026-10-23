using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class NonclosedCapLabelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unique middle label of a reconnected cap.",
        H("The unique middle label of a reconnected cap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("outer"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/NonclosedCapLabels.cap_outer_label"),
                H("The unique middle label of a reconnected cap"), StatementSource.FromAuthor(FormulaDsl.Disp(All("L", V("Type"), All("m", V("Natural"), All("M", Call("NCMatching", Add(V("m"), Num(2))), All("j", Call("Fin", Add(V("m"), Num(1))), All("y", Call("Function", Call("Fin", Add(V("m"), Num(1))), V("L")), Implies(NotEqual(Call("Partner", V("M"), Call("CastSucc", V("j"))), Call("Succ", V("j"))), Implies(Call("Compatible", Call("CapSurgery", V("M"), V("j")), V("y")), Equal(Call("Apply", V("y"), V("j")), Call("Apply", V("y"), Call("Succ", Call("CapU", V("M"), V("j")))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Partner-closed intervals transport the labels through all intervening arcs in every relative-order case of a nonclosed cap."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compatible"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/NonclosedCapLabels.nonclose_compatible_iff"),
                H("The unique middle label of a reconnected cap"), StatementSource.FromAuthor(FormulaDsl.Disp(All("L", V("Type"), All("m", V("Natural"), All("M", Call("NCMatching", Add(V("m"), Num(2))), All("j", Call("Fin", Add(V("m"), Num(1))), All("y", Call("Function", Call("Fin", Add(V("m"), Num(1))), V("L")), All("b", V("L"), Implies(NotEqual(Call("Partner", V("M"), Call("CastSucc", V("j"))), Call("Succ", V("j"))), Equivalent(Call("Compatible", V("M"), Call("DetourLabels", V("j"), V("y"), V("b"))), Both(Call("Compatible", Call("CapSurgery", V("M"), V("j")), V("y")), Equal(V("b"), Call("Apply", V("y"), Call("CastSucc", Call("CapU", V("M"), V("j")))))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compatibility after reconnecting the two original partners is equivalent to compatibility before surgery with exactly the prescribed middle label. Both side equations and every surviving endpoint are retained."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
