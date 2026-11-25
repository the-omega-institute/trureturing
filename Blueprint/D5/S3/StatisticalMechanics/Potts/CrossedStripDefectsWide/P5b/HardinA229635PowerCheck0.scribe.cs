using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b;

internal sealed class HardinA229635PowerCheck0Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck0.";
    private const string Note = "D5/L/SpinModels/hardin2013a229635";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At each index, the next cached row vector agrees with one exact sparse step.", H("Forward steps 0 through 9"),
        Blocks(
            Describe.Lean(DescribeId.Create("checked"),
                DeclarationHandle.Create(Prefix + "checked"), H("Forward steps 0 through 9"),
                StatementSource.FromAuthor(Disp(All("k", Call("Fin", D(1, 0)), Let("i", Call("Fin", D(3, 0)), Call("Fin.val", V("k")), Equal(Call("power", Call("Fin.succ", V("i"))), Call("step", Call("power", Call("Fin.castSucc", V("i"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("At each index, the next cached row vector agrees with one exact sparse step."))), DescribeRole.Theorem))));

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
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Paren(body));
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
            Seq(Word("let"), Sp, V(name), Colon, Sp, type, Sp, Colon, Eq, Sp, value, Semi, Sp, Paren(body));
}
