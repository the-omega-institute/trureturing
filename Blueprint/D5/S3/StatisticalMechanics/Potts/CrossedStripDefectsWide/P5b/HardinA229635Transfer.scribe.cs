using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b;

internal sealed class HardinA229635TransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Transfer.";
    private const string Note = "D5/L/SpinModels/hardin2013a229635";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transition, initial and terminal weights for the 127-state transfer.", H("The exact integer transfer"),
        Blocks(
            Describe.Lean(DescribeId.Create("t"),
                DeclarationHandle.Create(Prefix + "T"), H("The 127-state transfer matrix"),
                StatementSource.FromAuthor(Disp(All("i", Call("State"), All("j", Call("State"), Equal(Call("T", V("i"), V("j")), Call("Fin.addCases", Fn("k", Call("Fin", D(3, 1)), Call("Fin.addCases", Call("HardinA229532StripData.T", V("k")), Fn("l", Call("Fresh"), D(0)), V("j"))), Fn("l", Call("Fresh"), AsInt(Call("List.count", V("j"), Call("weights", V("l"))))), V("i"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The leading 31 by 31 block is the inherited transfer. Its outgoing entries to fresh states vanish. The remaining rows count occurrences in their checked successor lists."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial"),
                DeclarationHandle.Create(Prefix + "initial"), H("Initial weights"),
                StatementSource.FromAuthor(Disp(All("s", Call("State"), Equal(Call("initial", V("s")), IfThenElse(Less(Call("Fin.val", V("s")), D(3, 1)), D(0), D(6)))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Six labelled first rows contribute to each fresh state, and none contribute to the inherited block."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"),
                DeclarationHandle.Create(Prefix + "terminal"), H("Terminal weights"),
                StatementSource.FromAuthor(Disp(All("s", Call("State"), Equal(Call("terminal", V("s")), Call("Fin.addCases", Call("HardinA229532StripData.terminal"), Fn("i", Call("Fresh"), IfThenElse(Equal(Call("budget", V("i")), D(0)), D(1), D(0))), V("s")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The inherited terminal weights are preserved. A fresh state contributes exactly when its remaining budget is zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transition-counts"),
                DeclarationHandle.Create(Prefix + "transition_counts"), H("Exact transitions for every valid boundary state"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), All("d", Call("Nat"), All("s", Call("State"), ImpliesFormula(Call("Valid", V("p"), V("d")), Equal(SumOver("r", Call("Row"), IfThenElse(And(AtMost(Call("cost", V("p"), V("r")), V("d")), Equal(Call("cl", V("r"), Sub(V("d"), Call("cost", V("p"), V("r")))), V("s"))), D(1), D(0))), Call("T", Call("cl", V("p"), V("d")), V("s"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("In the inherited region the old weighted transitions apply. In the fresh region a common relabelling sends the source to its canonical representative and transports its full successor multiset."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("terminal-correct"),
                DeclarationHandle.Create(Prefix + "terminal_correct"), H("Exact terminal readout"),
                StatementSource.FromAuthor(Disp(All("p", Call("Row"), All("d", Call("Nat"), ImpliesFormula(Call("Valid", V("p"), V("d")), Equal(Call("terminal", Call("cl", V("p"), V("d"))), IfThenElse(Equal(V("d"), D(0)), D(1), D(0)))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Zero remaining budget accepts the array at either kind of state."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("initial-correct"),
                DeclarationHandle.Create(Prefix + "initial_correct"), H("Exact initial vector"),
                StatementSource.FromAuthor(Disp(All("s", Call("State"), Equal(SumOver("r", Call("Row"), IfThenElse(And(AtMost(Call("h", V("r")), D(2)), Equal(Call("cl", V("r"), Sub(D(2), Call("h", V("r")))), V("s"))), D(1), D(0))), Call("initial", V("s")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The initial vector counts precisely the labelled choices for the first row in each class."))), DescribeRole.Theorem))));

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
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula And(Formula left, Formula right) => Seq(Paren(left), Sp, Land, Sp, Paren(right));
    private static Formula ImpliesFormula(Formula left, Formula right) => Seq(Paren(left), Sp, Implies, Sp, Paren(right));
    private static Formula AsInt(Formula value) => Paren(Seq(value, Colon, Sp, Int));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Paren(body));
    private static Formula Fn(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, Paren(body));
    private static Formula IfThenElse(Formula guard, Formula yes, Formula no) =>
            Paren(Seq(Word("if"), Sp, guard, Sp, Word("then"), Sp, yes, Sp, Word("else"), Sp, no));
    private static Formula SumOver(string name, Formula type, Formula body) =>
            Seq(Sum, Underscore, Grp(V(name), Colon, Sp, type), Sp, Paren(body));
}
