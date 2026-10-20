using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class DetourLabelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Insertion of an adjacent labelled detour.",
        H("Insertion of an adjacent labelled detour"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("left"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/DetourLabels.detour_skip_left"),
                H("Insertion of an adjacent labelled detour"), StatementSource.FromAuthor(FormulaDsl.Disp(All("L", V("Type"), All("m", V("Natural"), All("j", Call("Fin", Add(V("m"), Num(1))), All("y", Call("Function", Call("Fin", Add(V("m"), Num(1))), V("L")), All("b", V("L"), All("k", Call("Fin", V("m")), Equal(Call("Apply", Call("DetourLabels", V("j"), V("y"), V("b")), Call("CastSucc", Call("SkipPair", V("j"), V("k")))), Call("Apply", V("y"), Call("CastSucc", V("k")))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Inserting the two cap endpoints leaves the left gap label of every surviving endpoint unchanged under the increasing survivor map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("right"),
                DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/DetourLabels.detour_skip_right"),
                H("Insertion of an adjacent labelled detour"), StatementSource.FromAuthor(FormulaDsl.Disp(All("L", V("Type"), All("m", V("Natural"), All("j", Call("Fin", Add(V("m"), Num(1))), All("y", Call("Function", Call("Fin", Add(V("m"), Num(1))), V("L")), All("b", V("L"), All("k", Call("Fin", V("m")), Equal(Call("Apply", Call("DetourLabels", V("j"), V("y"), V("b")), Call("Succ", Call("SkipPair", V("j"), V("k")))), Call("Apply", V("y"), Call("Succ", V("k")))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same transport holds for right gap labels. At the cap the three successive labels are the original gap label, the inserted middle label, and the original gap label again."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => Id(name);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
