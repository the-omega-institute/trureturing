using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class ChenChenRealStepSignsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/ChenChenRealStepSigns.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026chenchenparity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For real r ≥ 3, the step −r Eulerian triangle has positive even rows and negative "
            + "odd-row interiors.",
        H("Signs of the real-step Eulerian triangle"),
        Blocks(
            Describe.Lean(DescribeId.Create("chen-chen-real-step-second-column"),
                DeclarationHandle.Create(Prefix + "second_even_positive"),
                H("The second column in even rows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For real r ≥ 3 and every solution T of the step −r recursion, T(n,2)>0 "
                    + "for every even n ≥ 2. Applying the recursion twice at k=2 gives "
                    + "T(n+2,2)=(r−1)²T(n,2)+r(r−2)n+2−r². Since T(2,2)=1, the case n=2 "
                    + "gives T(4,2)=2r(r−3)+3>0. For n ≥ 4 the forcing term equals "
                    + "r(r−2)(n−4)+3r(r−3)+r+2>0, and induction over even n finishes."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chen-chen-real-step-signs-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Even rows positive, odd interiors negative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every real r ≥ 3 the step −r recursion has a solution, and every "
                    + "solution T satisfies T(n,k)>0 for every positive even n and 1 ≤ k ≤ n, "
                    + "and T(n,k)<0 for every odd n ≥ 3 and 1<k<n. If row n is positive, both "
                    + "coefficients −r(n+1−k)+1 and −r(k−1)+1 are negative at each interior "
                    + "position of row n+1, so that row's interior is negative. In the next "
                    + "even row both products at positions 3 through n are then positive. The "
                    + "second position uses the column bound above, the penultimate one the "
                    + "reflection T(n,k)=T(n,n+1−k), and the two boundary entries equal 1. "
                    + "This is Theorem 1 of H. Ma and W. Zhang's proof of Chen and Chen's "
                    + "parity-positivity conjectures (DOI 10.5281/zenodo.23957560) for all real "
                    + "r ≥ 3. The integer steps r=3,4,5 are the conjectures of OEIS "
                    + "A392664–A392666, already formalized over ℤ in "
                    + "ChenChenParityPositivity."))),
                DescribeRole.Theorem))));
}
