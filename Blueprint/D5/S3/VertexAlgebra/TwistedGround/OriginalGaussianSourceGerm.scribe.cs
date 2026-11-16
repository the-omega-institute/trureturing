using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianSourceGermDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalGaussianSourceGerm", H("Original source contraction germs and trace similarity"), Blocks(
            Paragraph(Text("For a fixed frequency cutoff, both actual internal source matrices vanish at zero. The right matrix contains every retained colour in its original inverse substitution. Entrywise positive comparisons vanish there as well. Finite dimensional continuity gives one positive closed contraction disk for these four matrices. Its radius may depend on the cutoff; no uniform occupation majorant or convergence on the unit disk is asserted.")),
            Paragraph(Text("The raw product is diagonally similar to the colour identity tensored with the square of the normalized finite section. Cyclicity of trace removes the positive frequency diagonal at every power, including power zero. Thus the arbitrary-mean finite sewing trace exponential is exactly exp(-(rank/2)*finiteLog). This algebraic identity needs no inverse of the sewing variable and includes empty mode or colour types. The source energy coefficient identity still needs analytic extraction and source stabilization.")),
            Describe.Lean(DescribeId.Create("original-source-positive-internal"),
                DeclarationHandle.Create(Prefix + "positiveInternal"), H("Positive internal comparison"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take each undamped internal entry's norm and multiply by the two nonnegative radius powers at its positive frequencies. The complete inverse colour transport precedes this comparison."))), DescribeRole.Definition),
            N("left_entry_differentiable", "Polynomial left entries", "Every actual damped left entry is a polynomial in the source variable."),
            N("right_entry_differentiable", "Polynomial fully transported right entries", "The inverse transport is independent of the source variable, and damping makes each actual right entry a polynomial."),
            N("original_rows_contract_on_germ", "A common fixed-cutoff contraction germ", "A finite intersection of strict norm neighbourhoods contains a positive closed disk. Both raw internal matrices and both positive comparisons are strict Euclidean contractions throughout it. No positive-rank or nonempty-support assumption occurs."),
            N("original_rows_trace_power", "Literal raw trace similarity", "At every nonnegative power p the raw internal product trace is rank times trace(finiteSection to the power 2*p). The proof retains the complete inverse Gram transport and both positive frequency diagonals."),
            N("original_rows_trace_prefactor", "Exact finite sewing normalization", "The trace-power identity and scalar linearity of the trace series give exp(-(rank/2)*finiteLog). No charge average or extra overall factor is introduced.")), []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("original-source-germ-" + name.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
