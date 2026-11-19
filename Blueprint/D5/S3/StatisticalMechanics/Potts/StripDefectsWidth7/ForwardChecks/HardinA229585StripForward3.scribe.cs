using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.ForwardChecks;
internal sealed class HardinA229585StripForward3Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/ForwardChecks/HardinA229585StripForward3.";
    private const string Note = "D5/L/SpinModels/hardin2013a229585";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("The forward table records the exact labelled weights of the 72 boundary classes.")),
            Describe.Lean(DescribeId.Create("forward-steps"),
                DeclarationHandle.Create(Prefix + "forward_steps"), H("Two exact forward steps"),
                StatementSource.FromAuthor(Disp(All("i", Call("Fin", Num("2")), Eq(App(Call("HardinA229585StripData.W"), Call("Fin.mk", Add(Add(Num("6"), Call("Fin.val", V("i"))), Num("1")))), Call("Matrix.vecMul", App(Call("HardinA229585StripData.W"), Call("Fin.mk", Add(Num("6"), Call("Fin.val", V("i"))))), Call("HardinA229585StripData.T")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The finite indices carry the displayed natural values, each less than eleven. Multiplication by the transition matrix advances the row count by one."))), DescribeRole.Theorem))));

    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));

}
