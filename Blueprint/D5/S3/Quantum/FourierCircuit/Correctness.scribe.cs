using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit;
internal sealed class CorrectnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original recursive QFT circuit", H("Original recursive QFT circuit"), Blocks(
            Describe.Lean(DescribeId.Create("circuit-action"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Correctness.circuit_action"),
                H("Exact action on every vector"),
                StatementSource.FromAuthor(Disp(All(Eq(
                    C("mulVec", C("onBinaryLabels", C("circuit", X("oracles"), X("q")), X("environment")), X("v")),
                    C("QFT", Pow(Num(2), X("q")), X("v"))),
                    ("oracles", X("OracleModel")), ("q", X("Nat")),
                    ("environment", C("Interpretation", X("oracles"))),
                    ("v", C("ComplexVector", Pow(Num(2), X("q"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("ComplexVector m denotes Fin m to Complex. The interpreter is computed from the actual circuit construction. It executes the leading Hadamard, the ordered controlled-phase prefix, the recursively placed tail and the terminal disjoint parallel SWAP network. The theorem holds for every natural width q, including zero, every oracle interpretation and every complex input vector. The right side is the existing independently defined QuantumPhaseEstimationGeneral.QFT, with positive exponent and inverse square-root normalization. Equality preserves the full phase, including global phase."))), DescribeRole.Theorem),
            Paragraph(Text("Binary labels are big endian. Before the terminal swaps the output label in the proved matrix formula is bit reversed. The actual parallel reversal cancels that reversal. The proof retains the original phase-prefix induction, the no-swap width induction and the reversal action on every computational basis ket. It does not assign Fourier semantics as an input to the circuit.")),
            Paragraph(Text("For Chapter 15 at q equal to three, an input x with bits x2,x1,x0 has output tensor factors in frequency MSB-to-LSB order with phases 2 pi times 0.x0, 0.x1x0 and 0.x2x1x0, each divided by the square root of two. For x equal to five these phases are pi, pi/2 and 5 pi/4. This describes the convention of the universal action theorem; the fixed example does not replace it.")),
            Paragraph(Text("The matching event theorem observes the identical circuit value. Its ideal native counts do not claim data-loading, full classical readout, discrete gate synthesis or hardware cost.")))));
    private static Formula X(string s) => DefinitionDsl.Id(s);
    private static Formula C(string s, params Formula[] xs) => DefinitionDsl.Call(s, xs);
    private static Formula Eq(Formula x, Formula y) => DefinitionDsl.Equal(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula All(Formula f, params (string Name, Formula Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; --i)
            f = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(xs[i].Name), xs[i].Type, f);
        return f;
    }
}
