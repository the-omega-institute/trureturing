using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b;

internal sealed class HardinA229635IntegerCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.";
    private const string Note = "D5/L/SpinModels/hardin2013a229635";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The checked initial vector and sparse steps imply a zero scalar residual at every offset.", H("Signed residual certificate"),
        Blocks(
            Describe.Lean(DescribeId.Create("forward-table"),
                DeclarationHandle.Create(Prefix + "forward_table"), H("Forward iteration from a table"),
                StatementSource.FromAuthor(Disp(Equal(Call("DefectTransfer.forward", V("M"), V("v"), Call("Fin.val", V("i"))), App(V("p"), V("i"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Let M be a square integer matrix on Fin d, v an integer row vector, and i an index of Fin 31. Let p assign a row vector to each index of Fin 31. Assume next maps each row vector w to Matrix.vecMul(w,M), p at zero equals v, and p at the successor of each j in Fin 30 equals next applied to p at j cast to Fin 31. Then the displayed equality gives the forward iterate at i."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("residual-all-offsets"),
                DeclarationHandle.Create(Prefix + "residual_all_offsets"), H("Vanishing scalar residual at every offset"),
                StatementSource.FromAuthor(Disp(All("t", Call("Nat"), Equal(Call("residual", Call("T"), Call("initial"), Call("terminal"), V("t")), D(0))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The initial row vector and all thirty transitions fix the powers needed by the signed lag vector. Four disjoint coordinate ranges cover that vector. Its terminal readout vanishes at offset zero. Its image under one matrix step is zero, so every positive offset has zero readout."))), DescribeRole.Theorem))));

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
}
