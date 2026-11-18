using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Primitives.QFT.Source;
internal sealed class ResourcesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Events of the original QFT circuit", H("Events of the original QFT circuit"), Blocks(
            Describe.Lean(DescribeId.Create("phase-step-count"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.phaseStep_count"),
                H("One actual controlled phase"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For every OracleModel oracles, event : Resource.Event (.quantum FourierGate.model oracles), natural n and offset : Fin n, count event (phaseStep oracles n offset).eventCost = delta(controlledPhase,event). The actual native leaf contributes one occurrence."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("phase-prefix-count"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.phasePrefix_count"),
                H("Controlled-phase prefix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For every OracleModel oracles, event : Resource.Event (.quantum FourierGate.model oracles), natural n and count with bounded : count <= n, countEvent event (phasePrefix oracles n count bounded).eventCost = count * delta(controlledPhase,event). Here countEvent denotes ResourcePool.count. The proof follows the actual prefix recursion."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("leading-hadamard-count"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.leadingHadamard_count"),
                H("One leading Hadamard"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For every OracleModel oracles, event : Resource.Event (.quantum FourierGate.model oracles) and natural n, count event (leadingHadamard oracles n).eventCost = delta(hadamard,event)."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("tail-layer-count"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.tailLayer_count"),
                H("Placement preserves the tail count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For every OracleModel oracles, event : Resource.Event (.quantum FourierGate.model oracles), natural n and body : UnitaryCircuit FourierGate.model oracles (QFTPrimitive.layout n), count event (tailLayer oracles n body).eventCost = count event body.eventCost. Physical placement preserves the original event trace."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("no-swap-count"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.noSwap_count"),
                H("Recursive word before reversal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For every OracleModel oracles, event : Resource.Event (.quantum FourierGate.model oracles) and natural n, count event (noSwap oracles n).eventCost = n * delta(hadamard,event) + choose(n,2) * delta(controlledPhase,event). The width induction consumes the leading, prefix and placed-tail counts."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("reverse-prefix-count"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Source/Resources.reversePrefix_count"),
                H("Actual reversal prefix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For every OracleModel oracles, event : Resource.Event (.quantum FourierGate.model oracles), natural n and count with bounded : count <= n/2, countEvent event (reversePrefix oracles n count bounded).eventCost = count * delta(swap,event), where countEvent is ResourcePool.count and division is natural-number division. This uses the event trace of the actual disjoint parallel reversal."))), DescribeRole.Lemma),
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
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
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
