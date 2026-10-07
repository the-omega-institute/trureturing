using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class DischargeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/Discharge.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Discharge"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate discharge to the stochastic ellipsoid construction.")),
            Node("claim-1", "matToUT", "mat To UT",
                "The coordinate vector of a symmetric matrix — the inverse of Increments.symMat.", DescribeRole.Definition),
            Node("claim-3", "trace_mul_eq_frobenius", "trace mul eq frobenius",
                "tr(B H) = ∑_{i,j} B_ij H_ij for symmetric H: the trace term of the one-step inequality is a Frobenius inner product.", DescribeRole.Theorem),
            Node("claim-4", "trace_mul_symMat_eq_inner", "trace mul sym Mat eq inner",
                "The trace term as an inner product. With H = symMat u the step's increment and B a symmetric matrix, tr(B H) = ⟪matToUT B, u⟫ — the form driftInputs_step_chain's V takes.", DescribeRole.Theorem),
            Node("claim-9", "StateBounds", "State Bounds",
                "The chain's state invariant on the good event. A_k is positive definite with a uniform lower bound m on its quadratic form, a uniform upper bound M on its operator norm, and a symmetric congruence factor S with S A_k S = 1.", DescribeRole.Definition),
            Node("claim-10", "hpt_step", "hpt step",
                "hpt for one step and one path. With V k ω = π_k (A_k⁻¹) and c = 1 / (2 M² (1+δ)²), this is exactly the inequality StepInputs2.driftInputs_step_chain consumes.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
