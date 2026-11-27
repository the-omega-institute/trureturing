using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicDirectedOccupationCapDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Directed CAR occupation bounds separate a scalar obstruction from the physical cubic deficit.",
        H("Directed occupation cap and same-spectrum deficit gap"),
        Blocks(
            Entry("jump-weight-le", "jumpWeight_le", "Directed occupation cap",
                "Let x and y be arbitrary complex vectors in the occupation basis 00, 01, 10, 11. " +
                "Write E, O and F for the empty, odd and full squared coordinate masses. For every t > 0, " +
                "the sum of the two squared CAR lowering amplitudes from y to x is at most " +
                "(1+t)E(x)O(y) + (1+1/t)O(x)F(y). The two occupation blocks have Euclidean norms " +
                "√(E(x)O(y)) and √(O(x)F(y)), so the triangle inequality and Young's inequality give the cap."),
            Entry("table-no-unitary-realization", "table_no_unitary_realization", "Forbidden directed edge",
                "The scalar table has rows (1/4, 3/4, 1/2, 0), (1/4, 1/4, 0, 1/2), " +
                "(0, 0, 1/4, 3/4), and (0, 0, 1/4, 1/4). No complex unitary frame realizes this table " +
                "with even occupation 1/2 in every column. The row minus column totals fix the empty " +
                "mass of column 0 at 1/2 and the full mass of column 1 at 1/4. With t = 2/3 the cap " +
                "gives w₀₁ ≤ 35/48, whereas the table has w₀₁ = 3/4."),
            Entry("strengthened-relaxation-refuted", "strengthenedRelaxation_refuted", "Negative scalar deficit",
                "Fix the ascending spectrum λ = (43³, 45³, 73³, 76³)/998625 and h = 3 log(21/20). " +
                "The table satisfies the scalar CAR constraints at even occupations eᵢ = 1/2 and " +
                "moment m = (λ₃−λ₀)/2. It also satisfies |∑ⱼ(wᵢⱼ−wⱼᵢ)| ≤ 2eᵢ for every i. " +
                "Its normalized cubic deficit, (4 cosh(h)/9)(E₃−α₃ H), is strictly below −1/250, " +
                "with the ordinary Wu cubic coefficient α₃ and entropy H = ∑ᵢ λᵢ log(4λᵢ) + " +
                "2 log(cosh h) − 2hm."),
            Entry("balanced-frame-normalized-cubic-deficit-gt", "balancedFrame_normalizedCubicDeficit_gt",
                "Positive physical deficit at the same spectrum",
                "At the same λ and h, every complex unitary frame with even occupation 1/2 in each " +
                "column has normalized cubic deficit strictly greater than 1/500. Here m is the " +
                "λ-weighted full minus empty mass of its columns. The directed cap bounds the cheapest " +
                "of the three matching weights, and rational logarithm bounds give the strict margin."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
