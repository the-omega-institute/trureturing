using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b;

internal sealed class HardinA229635IntegerCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.";
    private const string Note = "D5/L/SpinModels/hardin2013a229635";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The checked initial vector and sparse steps imply a zero scalar residual prefix.", H("Signed residual certificate"),
        Blocks(
            Describe.Lean(DescribeId.Create("residual-prefix"),
                DeclarationHandle.Create(Prefix + "residual_prefix"), H("Vanishing scalar residual through dimension 127"),
                StatementSource.FromAuthor(Disp(All("t", Call("Nat"), ImpliesFormula(Less(V("t"), D(1, 2, 7)), Equal(Call("residual", Call("T"), Call("initial"), Call("terminal"), V("t")), D(0)))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The initial row vector and all thirty transitions fix the powers needed by the signed lag vector. Four disjoint coordinate ranges cover that vector. Its terminal readout and its image under one matrix step both vanish."))), DescribeRole.Theorem))));

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
    private static Formula ImpliesFormula(Formula left, Formula right) => Seq(Paren(left), Sp, Implies, Sp, Paren(right));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Paren(body));
}
