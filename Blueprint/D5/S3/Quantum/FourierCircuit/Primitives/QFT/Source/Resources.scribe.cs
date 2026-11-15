using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit;
internal sealed class ResourcesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Events of the original QFT circuit", H("Events of the original QFT circuit"), Blocks(
            Describe.Lean(DescribeId.Create("same-circuit-count"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.qftSource_circuit_event_count"),
                H("Every event coordinate of the same circuit"),
                StatementSource.FromAuthor(Disp(All(Eq(
                    C("count", X("event"), C("eventCost", C("circuit", X("oracles"), X("q")))),
                    Add(Add(Mul(X("q"), C("delta", C("hadamard"), X("event"))),
                        Mul(C("choose", X("q"), Num(2)), C("delta", C("controlledPhase"), X("event")))),
                        Mul(C("natDiv", X("q"), Num(2)), C("delta", C("swap"), X("event"))))),
                    ("oracles", X("OracleModel")),
                    ("event", C("Event", C("quantum", C("FourierModel"), X("oracles")))),
                    ("q", X("Nat"))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/qudeleap2026qft")),
                Blocks(Paragraph(Text("delta(a,event) is one if the gate event a equals event and zero otherwise. natDiv is natural-number division. eventCost traverses the same construction tree used by matrix execution. The counts are q Hadamards, choose(q,2) native controlled phases and floor(q/2) native SWAPs; every other coordinate, including oracle events, has count zero. The empty-width circuit has all counts zero. These are ideal native occurrences, not default-model expansions or hardware costs."))), DescribeRole.Theorem),
            Paragraph(Text("The phase-prefix induction counts one controlled phase at each actual step. The no-swap induction adds one Hadamard and the selected prefix. The reversal word retains its certified disjoint parallel branches and contains exactly floor(q/2) SWAP occurrences. Their sequential composition is precisely Source.circuit, also used by circuit_action.")))));
    private static Formula X(string s) => DefinitionDsl.Id(s);
    private static Formula C(string s, params Formula[] xs) => DefinitionDsl.Call(s, xs);
    private static Formula Eq(Formula x, Formula y) => DefinitionDsl.Equal(x, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula All(Formula f, params (string Name, Formula Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; --i)
            f = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(xs[i].Name), xs[i].Type, f);
        return f;
    }
}
