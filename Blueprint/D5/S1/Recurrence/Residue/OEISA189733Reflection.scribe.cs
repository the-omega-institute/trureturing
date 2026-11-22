using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class OEISA189733ReflectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/OEISA189733Reflection.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a189733siblings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Curtz's full rational square array satisfies the signed reflection identity, and its "
            + "zeroth column is the inverse binomial transform of its zeroth row.",
        H("Reflection and inverse binomial transform for Curtz's array"),
        Blocks(
            Describe.Lean(DescribeId.Create("a189733-full-array"),
                DeclarationHandle.Create(Prefix + "B"),
                H("The full square array"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For m ≤ n the entry B(m, n) is the upper entry triangle m (n − m) of the "
                    + "frozen denominator module. For m > n it is defined by the lower branch "
                    + "B(m, n) = B(m − 1, n + 1) − B(m − 1, n), as in the A189733 programs."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a189733-reflection"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Reflection and the inverse binomial transform"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For all m and d, B(m, m + d) is the frozen entry triangle m d. "
                    + "For all m and n: "
                    + "B(m, m) = 0, B(m, n) = (−1)^{m+n+1} B(n, m), and "
                    + "B(m + 1, n) = B(m, n + 1) − B(m, n). Moreover, for every n ≥ 0, "
                    + "B(n, 0) = ∑_{j=0}^{n} (−1)^{n−j} C(n, j) b_j = (−1)^{n+1} b_n, where "
                    + "b_j = B(0, j). The reflection is proved by induction on m for m ≥ n. "
                    + "At m = n + 1 the lower branch gives B(n, n + 1). For larger m, the "
                    + "upper recurrence B(n, m) = B(n, m − 1) + B(n + 1, m − 1) matches the "
                    + "lower branch after the sign change. The difference identity is the "
                    + "lower branch below the diagonal and the rearranged upper recurrence "
                    + "above it. Iterating it expresses B(m, ·) as the m-th forward "
                    + "difference of the zeroth row. Setting n = 0 and applying reflection "
                    + "gives the last identity. This is Corollary 3 of H. Ma and W. Zhang's "
                    + "note (DOI 10.5281/zenodo.23957584). Together with the finite sums of "
                    + "Corollary 4, the zero diagonal and the reflection determine every "
                    + "entry of the array."))),
                DescribeRole.Theorem))));
}
