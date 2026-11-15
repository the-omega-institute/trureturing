using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit;
internal sealed class EntriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entries of the original full QFT word", H("Entries of the original full QFT word"), Blocks(
            Describe.Lean(DescribeId.Create("full-word-entry"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Entries.circuit_entry"),
                H("Full-word Fourier entry"),
                StatementSource.FromAuthor(Disp(All(Eq(
                    C("onBinaryLabels", C("circuit", X("oracles"), X("q")), X("environment"), X("output"), X("input")),
                    Mul(C("invSqrtN", X("q")), Pow(C("omega", X("q")), Mul(C("val", X("output")), C("val", X("input")))))),
                    ("oracles", X("OracleModel")), ("q", X("Nat")),
                    ("environment", C("Interpretation", X("oracles"))),
                    ("output", C("Fin", Pow(Num(2), X("q")))),
                    ("input", C("Fin", Pow(Num(2), X("q"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("invSqrtN q is the reciprocal square root of two to the q, and omega q is exp(2 pi i / 2^q). This assembly consumes the original no-swap width induction and the actual terminal reversal. circuit_action consumes this entry law to identify every vector with the existing analytic transform."))), DescribeRole.Theorem))));
    private static Formula X(string s) => DefinitionDsl.Id(s);
    private static Formula C(string s, params Formula[] xs) => DefinitionDsl.Call(s, xs);
    private static Formula Eq(Formula x, Formula y) => DefinitionDsl.Equal(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula All(Formula f, params (string Name, Formula Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; --i)
            f = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(xs[i].Name), xs[i].Type, f);
        return f;
    }
}
