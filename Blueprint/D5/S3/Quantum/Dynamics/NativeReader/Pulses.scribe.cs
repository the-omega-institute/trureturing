using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.NativeReader;

internal sealed class PulsesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic dependence of literal entrances.",
        H("Analytic dependence of literal entrances"),
        Blocks(Describe.Lean(
            DescribeId.Create("entrance-analytic"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeReader/Pulses.entrance_analytic"),
            H("Analytic dependence of literal entrances"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The matrix projection(i,j) is the original weighted legal-path projection at interior tail position j+1. Its Hermitian and idempotent properties directly apply weighted_legal_path_temperley_lieb with the actual adjacency and Perron data. Pulse(i,j,t)=exp(i*t)*(I+(exp(i*t)-1)*projection(i,j)); its global phase is retained. Only j=1 and j=3 use the common lambda; other j use alpha=3*pi/5. The physical word is (10,11,10,12,11,10,13,12,11,10,14,13,12,11,10), with local indices obtained by subtracting ten. Each entrance executes all preceding full unit-time calls.")), Paragraph(Text("EntranceCoordinate(i,k,z) denotes lambda mapped to entrance(i,lambda,k)(z). The theorem states real analyticity at every real t, for either sector, every natural k and every coordinate in its complete tail carrier. Induction uses the actual recursion, the real-linear complex inclusion, complex exponential analyticity and finite matrix sums. At the mathematical reference parameter zero, changed calls are identities; the ready row and column of every unchanged call are derived from the actual projection support and legality. Thus reference_entrance is a nonzero phase multiple of the unique ready vector. No zero-parameter operation is added to the control menu. All these helpers are consumed by the source charge and uniform nonvanishing proof."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Statement() => Disp(Seq(Forall, Sp, F.Id("i"), Colon, Sp, F.Id("Bool"), Comma, Sp, Forall, Sp, F.Id("k"), Colon, Sp, F.Id("Nat"), Comma, Sp, Forall, Sp, F.Id("z"), Colon, Sp, Call("Tail", F.Id("i")), Comma, Sp, Forall, Sp, F.Id("t"), Colon, Sp, F.Id("Real"), Comma, Sp, Call("RealAnalyticAt", Call("EntranceCoordinate", F.Id("i"), F.Id("k"), F.Id("z")), F.Id("t"))));
}
