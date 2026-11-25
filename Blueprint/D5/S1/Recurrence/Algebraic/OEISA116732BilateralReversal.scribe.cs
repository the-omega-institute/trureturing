using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class OEISA116732BilateralReversalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/OEISA116732BilateralReversal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a400645siblings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unrounded A116732 companion extends uniquely to all integer indices, and the "
            + "extension satisfies Somos's reversal identity u_n = −u_{2−n}.",
        H("Bilateral reversal for the A116732 companion"),
        Blocks(
            Describe.Lean(DescribeId.Create("a116732-bilateral-recurrence"),
                DeclarationHandle.Create(Prefix + "IsRec"),
                H("The bilateral recurrence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A function u from the integers to the integers satisfies the bilateral "
                    + "recurrence when u_n = u_{n−1} + u_{n−2} + u_{n−3} − u_{n−4} for every "
                    + "integer n, including negative n."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a116732-initial-values"),
                DeclarationHandle.Create(Prefix + "IsInit"),
                H("The initial values"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The initial values are u_0 = u_1 = u_2 = 0 and u_3 = 1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a116732-bilateral-reversal"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Unique extension and reversal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "There is exactly one function u from the integers to the integers with "
                    + "these initial values that satisfies the bilateral recurrence, and every "
                    + "such function satisfies u_n = −u_{2−n} for every integer n. The trailing "
                    + "coefficient of the recurrence is −1, so a solution vanishing at 0, 1, 2 "
                    + "and 3 vanishes at every integer, by induction upward and downward. This "
                    + "gives uniqueness, and existence comes from reflecting the forward "
                    + "solution through index one. The characteristic polynomial is "
                    + "palindromic: comparing the recurrence at n and at 6 − n shows that "
                    + "n ↦ u_n + u_{2−n} again satisfies the recurrence. The recurrence at "
                    + "n = 3 forces u_{−1} = −1, so this sum vanishes at 0, 1, 2 and 3, hence "
                    + "everywhere, which is the identity. This is Corollary 7 of H. Ma and "
                    + "W. Zhang's note (DOI 10.5281/zenodo.24369110), which reproves the "
                    + "identity recorded by Michael Somos in A116732."))),
                DescribeRole.Theorem))));
}
