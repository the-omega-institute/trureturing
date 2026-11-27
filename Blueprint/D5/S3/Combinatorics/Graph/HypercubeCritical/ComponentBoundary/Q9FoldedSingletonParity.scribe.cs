using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9FoldedSingletonParityDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSingletonParity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A residual incidence count excludes odd singleton completions within the quota for three archived folds.",
        H("Singleton parity in three archived Q₉ folds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("residual-singleton-quota"),
                DeclarationHandle.Create(Module + ".card_rows_le_residual_quota"),
                H("Odd rows force a residual incidence quota"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let R be a finite set of rows, N(r) the finite set of sites adjacent to row r, and A the fixed sites. Suppose a completion S contains A. For each row in R, assume the degree on A is odd and the degree on S is even. If each site of S outside A is incident to at most m rows in R, then |R| ≤ m · (|S| − |A|).")),
                    Paragraph(Text("At each row the degree on S adds the degree on A and the degree on S outside A. The last degree is odd by parity cancellation, hence positive. Counting the incidences between the rows and the chosen sites outside A gives at least one per row and at most m per such site. Mathlib's Finset.card_mul_le_card_mul supplies the incidence bound."))),
                DescribeRole.Theorem),
            Paragraph(Text("For a Huang-balanced induced cubic support of order 126, fold Q₉ along the archived axis to Q₈. At each folded centre, apply Q9FoldedIncidence.folded_degree_of_balanced_cubic with each of the two original cube parities as source. The degree for each source includes the centre label and the eight transverse labels. It is odd exactly when the centre belongs to the opposite folded parity set. Adding the two degrees modulo two therefore gives the singleton bit at the centre. The centre label already contributes that bit, so the sum of the eight transverse singleton bits is even.")),
            Paragraph(Text("For cases 2, 3 and 6, take S to be the singleton sites in the odd class of Q₈. The 18+3 dimer profile gives 168 transverse edges, since 3 · 126 / 2 − (18 + 3) = 168. On the odd class each of the three dimers accounts for four transverse incidences and each singleton for three. Thus the odd class has a quota of 52 singletons.")),
            Describe.Lean(
                DescribeId.Create("archived-completion-card-lower-bound"),
                DeclarationHandle.Create(Module + ".archived_completion_card_lower_bound"),
                H("Odd singleton lower bounds for cases 2, 3 and 6"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Index the archive cases 2, 3 and 6 by 0, 1 and 2 in Fin 3. Encode each Q₈ site by its eight binary digits. Let A be the fixed set for the case and F its admissible free set. If a set S of sites contains A, if every site of S outside A belongs to F, and if every even centre has an even number of transverse neighbours in S, then S contains at least 54 sites in cases 2 and 3 and at least 56 in case 6.")),
                    Paragraph(Text("The lists for A and F come from the order126 archive's fold-parity-quota.py replay. The signed-shadow domains and one pass of parity forcing give A. The odd sites outside both the shadow and A give F. Lean forms the eight transverse neighbours by XOR with the eight one-bit masks. Among the even centres it selects the rows with odd degree into A.")),
                    Paragraph(Text("The finite calculation gives 48 fixed sites in each case, 24, 24 and 32 selected rows, respectively, and maximum incidence four over the free sites in each case. The residual incidence bound requires at least 6, 6 and 8 extra sites, respectively. Each exceeds the four remaining slots under the quota of 52."))),
                DescribeRole.Theorem),
            Paragraph(Text("The exclusion is conditional on the archived fixed and admissible free masks for the three inherited folds and on the even-centre parity constraints. Hong, Wu and Xia's Problem 2 asks for the full value of f₂(Q₉), which remains open. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
        []));
}
