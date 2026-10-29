using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class CoefficientOperatorDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/FockAttenuator/CoefficientOperator.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual two-mode columns synthesize one Hilbert-Schmidt operator, and its product with its adjoint is the existing physical partial trace.",
        H("The actual completed coefficient operator"),
        Blocks(
            Result("unique-completed", "exists_unique_completed_coefficient_operator", "The complete unique column-operator contract",
                "For every completed two-mode V there exists exactly one continuous complex-linear C satisfying all occupation-column equations, the Hilbert-Schmidt property, the full Parseval square-sum equality and the identity purePartialTrace(V)=C*C-adjoint. "
                + "Uniqueness follows from continuity and equality on the total occupation basis; no basis vector is replaced by zero padding.",
                Call("UniqueCompletedCoefficientOperator", F.Id("V"))),
            Result("synthesis", "exists_coefficient_operator", "Hilbert-Schmidt synthesis of every column",
                "For every actual two-mode V, there is a continuous complex-linear operator C on H taking the j-th occupation basis vector to V(j), for every natural j. "
                + "C is Hilbert-Schmidt, and the complete sum of squared column norms equals norm(V)^2. The existing ColumnSynthesis theorem is used after reindexing the occupation Hilbert basis onto its range as a set of genuine Hilbert vectors.",
                Call("ActualHilbertSchmidtColumns", F.Id("V"))),
            Result("partial-trace", "pure_partial_trace_eq", "The existing reduced operator is C times C-adjoint",
                "For every V, purePartialTrace(V) equals coefficientOperator(V) times its Hilbert adjoint. The owner's partial trace is the full sum of rank-one operators of the actual columns. "
                + "Absolute summability in operator norm and the occupation expansion of C-adjoint(y) identify both sides on every y in H. No finite-support or finite-rank assumption is imposed.",
                Call("PartialTraceEqualsCoefficientProduct", F.Id("V"))),
            Result("sections", "kernel_eq_coefficient_operator", "Actual operator images give the evaluation sections",
                "For every V,z,w, the completed Bargmann kernel at (z,w) is the Bargmann transform at z of C applied to the actual exponential vector at w. "
                + "The full vector-valued contraction converges in H. This identity fixes the column convention and supplies a genuine Hilbert section for each complex parameter.",
                Call("KernelEqualsActualOperatorSection", F.Id("V"), F.Id("z"), F.Id("w"))))));

    private static DocumentBlock Result(string id, string declaration, string title,
        string prose, Formula formula) =>
        Describe.Lean(DescribeId.Create("fock-coefficient-" + id),
            DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
