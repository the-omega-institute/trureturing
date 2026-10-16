using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class TwelveStateGhostDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero-mass ghost in the actual twelve-state law", H("A zero-mass ghost in the actual twelve-state law"),
        Blocks(
            Paragraph(Text("Retain every original twelve-state hidden state as some(i), and adjoin the state none. Its initial mass is zero. On the original block the two marked matrices are unchanged; all cross-block entries are zero. The ghost zero entry is zero and the ghost one entry is one. Thus the ghost emits ones forever but is never visited under the stationary law.")),
            Describe.Lean(DescribeId.Create("visible-eq-of-cylinders"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateGhost.visible_eq_of_cylinders"),
                H("Whole bilateral law from integer cylinders"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any two finite measures on bilateral Boolean output paths, equality of the real masses of every integer-origin finite cylinder implies equality of the complete measures. A finite coordinate set is contained in a symmetric integer window, so its marginal is the corresponding restriction of a finite word marginal; projective-limit uniqueness finishes the proof. This helper is consumed by the ghost preservation and positive-mass trimming bridges."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("parameter"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateGhost.parameter"),
                H("The lawful thirteen-state padding"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The padded initial row and marked matrices form a Presentation on Option Hidden. Every entry is nonnegative; initial masses sum to one; both original and ghost rows are stochastic; and the initial row is stationary. The stationary weighted two-one mass remains zero because the original block satisfies no11 and the ghost has zero initial mass. Thus membership of the complete original producer domain permits the unused all-ones state."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-ghost-counterexample"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateGhost.actual_ghost_counterexample"),
                H("The same visible law has an unsupported singleton rectangle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Option Hidden has exactly thirteen states. The entire visible probability measure of the padded parameter equals the original actual visible measure P. For every integer start, its cylinder for the word 11 has real mass zero. Nevertheless, the product of its one matrix with itself has entry one exactly at the pair (none,none), and zero at every other pair. Its support is therefore the nonempty positive rectangle consisting of the singleton ghost row and singleton ghost column.")),
                    Paragraph(Text("Induction on word length shows that every word product has the original product on the original block, zero cross-block entries, and ghost entry one exactly when all its letters are one. The zero ghost initial mass leaves every actual visible cylinder unchanged. Equality of all symmetric finite-window marginals gives equality of all finite-coordinate marginals, and the existing projective-limit uniqueness theorem gives equality of the full bilateral visible measures. The original no11 support gives zero actual occurrence probability to 11. This is the exact permitted zero-mass boundary: it does not weaken the supported-word obstruction and supplies no statement about positive-weight components."))), DescribeRole.Theorem))));
}
