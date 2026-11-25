using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b;

internal sealed class HardinA229635SparseDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635SparseData.";
    private const string Note = "D5/L/SpinModels/hardin2013a229635";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Successor multiplicities and the corresponding incoming lists.", H("Sparse transfer data"),
        Blocks(
            Describe.Lean(DescribeId.Create("outgoing-classes"),
                DeclarationHandle.Create(Prefix + "outgoingClasses"), H("Outgoing classes by source"),
                StatementSource.FromAuthor(Disp(All("s", Call("State"), Equal(Call("outgoingClasses", V("s")), Call("Fin.addCases", Call("Vector.get", Call("oldRows")), Call("weights"), V("s")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The first 31 rows use the inherited block. The remaining 96 rows list the checked fresh classes."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("incoming-classes"),
                DeclarationHandle.Create(Prefix + "incomingClasses"), H("Incoming classes by destination"),
                StatementSource.FromAuthor(Disp(All("j", Call("State"), Equal(Call("incomingClasses", V("j")), Call("Vector.get", Call("incomingRows"), V("j")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For each destination, the table stores the sources of incoming transitions in increasing source order, with multiplicity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transpose-lists"),
                DeclarationHandle.Create(Prefix + "transposeLists"), H("Transposing the outgoing lists"),
                StatementSource.FromAuthor(Disp(All("j", Call("State"), Equal(Call("transposeLists", V("j")), Call("List.flatten", Call("List.ofFn", Fn("i", Call("State"), Call("List.replicate", Call("List.count", V("j"), Call("outgoingClasses", V("i"))), V("i"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each lossless transpose entry includes the source once for every occurrence of the destination in that source's list."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("step"),
                DeclarationHandle.Create(Prefix + "step"), H("Sparse update by incoming classes"),
                StatementSource.FromAuthor(Disp(All("v", Arrow(Call("State"), Call("Int")), All("j", Call("State"), Equal(Call("step", V("v"), V("j")), Call("List.sum", Call("List.map", V("v"), Call("incomingClasses", V("j"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each repeated incoming source contributes its current weight one more time."))), DescribeRole.Definition))));

    private static Formula V(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Word(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] arguments)
        {
            Formula symbol = Seq(name.Split('.').SelectMany((part, index) =>
                index == 0 ? new[] { Word(part) } : new[] { Dot, Word(part) }).ToArray());
            return arguments.Length == 0 ? symbol : App(symbol, arguments);
        }
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Arrow(Formula left, Formula right) => Seq(Paren(left), Sp, To, Sp, Paren(right));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Paren(body));
    private static Formula Fn(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, Paren(body));
}
