using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.NormCompression;

internal sealed class FinitePowerTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite two-row trace powers on the full nonnegative cone.",
        H("Finite two-row trace power"), Blocks(
            Item("definition", "Fq", "Actual operator trace power",
                "For every finite column type m, Aq q W is the complex embedding of the real entrywise roots W^(1/(2q)), and Fq q W is schattenPow (2q) (Aq q W). On entrywise nonnegative tables this is the actual Schatten power, with no rank or invertibility restriction.", DescribeRole.Definition),
            Item("operator-trace", "Fq_eq_trace_rpow", "Row Gram operator power",
                "For every real q > 0, Fq q W equals the real part of the trace of the actual CFC q-th power of Aq q W times its adjoint. The finite column type may be empty.", DescribeRole.Theorem),
            Item("continuity", "continuous_Fq", "Continuity including zero entries",
                "For every real q > 0 and every finite column type, Fq q is continuous on the entire real matrix space. Restriction therefore gives continuity on the full nonnegative cone, including singular Gram matrices and all axial tables.", DescribeRole.Theorem),
            Item("homogeneity", "Fq_smul", "Nonnegative degree-one homogeneity",
                "For every real q > 0, c >= 0 and entrywise nonnegative W, Fq q (c times W) = c times Fq q W. The zero scalar and zero table are included.", DescribeRole.Theorem),
            Item("radial", "radial_second_derivative_zero", "Actual radial second derivative",
                "For every q > 0, real c and nonnegative W, the actual second derivative at t = 0 of Fq q ((1 + tc) times W) is zero. This proves the radial inclusion only; it does not assert a converse kernel classification.", DescribeRole.Theorem),
            Paragraph(Text("The full-cone concavity theorem for 1 < q < 2, its exact support-restricted strict kernel and the local-output-orthogonal compression budget are proved in their separate owning modules. Empty finite column types are included in all universal statements; their singular-value sum is zero. Fixed-congruence Carlen-Lieb convexity on positive definite matrices is not used as a substitute for these statements.")))));

    private static DocumentBlock Item(string id, string declaration, string title,
        string text, DescribeRole role) => Describe.Lean(
            DescribeId.Create("finite-power-trace-" + id),
            DeclarationHandle.Create("D5/S3/Quantum/NormCompression/FinitePowerTrace." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
