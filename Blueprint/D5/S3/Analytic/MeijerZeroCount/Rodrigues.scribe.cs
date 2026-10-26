using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MeijerZeroCount;

internal sealed class RodriguesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rodrigues kernels with exact interior zero counts.",
        H("The compactly supported polynomial family"), Blocks(
            Definition("meijer-rodrigues-primitive", "W", "The polynomial primitive",
                "For natural n and N, W is X to the power n times (1-X) to the power N, as a real polynomial."),
            Definition("meijer-partial-fraction-coefficients", "coeffA", "The coefficients",
                "The coefficient at k is (-1) to the power n+k times (n+k) factorial divided by k factorial squared and by (n+d-1-k) factorial. The coefficient sum runs from zero through N=n+d-1."),
            Definition("meijer-rodrigues-polynomial", "rodriguesPoly", "The Rodrigues polynomial",
                "Take the nth polynomial derivative of W with N=n+d-1, then multiply by (-1) to the power n divided by N factorial."),
            Definition("meijer-compact-kernel", "f", "The Mellin kernel",
                "Inside the unit interval with endpoints excluded, f is x to the real power n+c times the Rodrigues polynomial evaluated at x, viewed as a complex number. The function is zero elsewhere."),
            Theorem("meijer-rodrigues-expansion", "f_eq_sum", "The finite power expansion",
                "For natural n and d, real c, and zero less than x less than one, f(x) is the sum over k from zero through n+d-1 of the coefficient at k times x to the real power n+c+k. Expand the primitive by the binomial theorem, apply the polynomial derivative term by term, and simplify the factorial coefficients."),
            Theorem("meijer-kernel-zero-count", "zeros_f", "Exactly n interior zeros",
                "For every natural n, every natural d at least one, and every real c, the zero set of f in the unit interval with endpoints excluded has extended cardinality n. The real power factor and the scalar normalization do not vanish there. Before the nth derivative, both endpoints remain roots. Rolle's theorem supplies an additional distinct interior root at every derivative step. The surviving factor (1-X) to the power N-n divides the nth derivative; after its removal the remaining polynomial has degree at most n. The polynomial degree bound gives the matching upper bound."))));

    private static DocumentBlock Definition(string id, string name, string title, string text) =>
        Entry(id, name, title, text, DescribeRole.Definition);
    private static DocumentBlock Theorem(string id, string name, string title, string text) =>
        Entry(id, name, title, text, DescribeRole.Theorem);
    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/MeijerZeroCount/Rodrigues." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
