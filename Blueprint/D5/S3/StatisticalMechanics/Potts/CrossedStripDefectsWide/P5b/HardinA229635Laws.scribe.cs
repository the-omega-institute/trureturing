using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b;

internal sealed class HardinA229635LawsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Laws.";
    private const string Note = "D5/L/SpinModels/hardin2013a229635";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical row reconstruction and terminal acceptance in the inherited block.", H("Boundary-state laws"),
        Blocks(
            Describe.Lean(DescribeId.Create("representatives-complete"),
                DeclarationHandle.Create(Prefix + "representatives_complete"), H("Recovery of the canonical row"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), ImpliesFormula(Call("Canonical", V("p")), ImpliesFormula(AtMost(Call("h", V("p")), D(2)), Equal(Call("rep", Call("fresh", V("p"))), V("p"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A canonical row with at most two horizontal defects is reconstructed by the index of its equality pattern."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("old-terminal"),
                DeclarationHandle.Create(Prefix + "old_terminal"), H("Acceptance on the inherited block"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), All("d", Call("Fin", D(2)), ImpliesFormula(AtMost(Add(Call("h", V("p")), Call("Fin.val", V("d"))), D(1)), Equal(Call("HardinA229532StripData.terminal", Call("HardinA229532StripData.cl", V("p"), Call("Fin.val", V("d")))), IfThenElse(Equal(Call("Fin.val", V("d")), D(0)), D(1), D(0)))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A row and budget in the one-defect sector retain the inherited terminal weight."))), DescribeRole.Theorem))));

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
    private static Formula AtMost(Formula left, Formula right) => Seq(left, Sp, Le, Sp, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula ImpliesFormula(Formula left, Formula right) => Seq(Paren(left), Sp, Implies, Sp, Paren(right));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Paren(body));
    private static Formula IfThenElse(Formula guard, Formula yes, Formula no) =>
            Paren(Seq(Word("if"), Sp, guard, Sp, Word("then"), Sp, yes, Sp, Word("else"), Sp, no));
}
