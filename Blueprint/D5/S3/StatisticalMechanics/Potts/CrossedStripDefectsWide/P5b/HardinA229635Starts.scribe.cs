using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b;

internal sealed class HardinA229635StartsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Starts.";
    private const string Note = "D5/L/SpinModels/hardin2013a229635";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Initial state multiplicities for labelled first rows.", H("First-row census"),
        Blocks(
            Describe.Lean(DescribeId.Create("start-table"),
                DeclarationHandle.Create(Prefix + "startTable"), H("Stored first-row class list"),
                StatementSource.FromAuthor(Disp(Seq(Call("startTable"), Colon, Sp, Call("List", Call("State"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The definition stores an explicit list of state indices. The equality below relates it to the enumeration of labelled first rows."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checked-starts"),
                DeclarationHandle.Create(Prefix + "checked_starts"), H("Exact first-row list"),
                StatementSource.FromAuthor(Disp(Equal(Call("startClasses"), Call("startTable")))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Enumerating all labelled first rows gives the stored list."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("start-tallies"),
                DeclarationHandle.Create(Prefix + "start_tallies"), H("First-row multiplicity in each class"),
                StatementSource.FromAuthor(Disp(All("s", Call("State"), Equal(AsInt(Call("List.count", V("s"), Call("startTable"))), IfThenElse(Less(Call("Fin.val", V("s")), D(3, 1)), D(0), D(6)))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Paying for the first row starts in the fresh sector. Each fresh state occurs six times."))), DescribeRole.Theorem))));

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
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula AsInt(Formula value) => Paren(Seq(value, Colon, Sp, Int));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Paren(body));
    private static Formula IfThenElse(Formula guard, Formula yes, Formula no) =>
            Paren(Seq(Word("if"), Sp, guard, Sp, Word("then"), Sp, yes, Sp, Word("else"), Sp, no));
}
