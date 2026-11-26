using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class CompleteHockeyStickDoeblinRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/CompleteHockeyStickDoeblinRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/georgehirchenuradhawilde2026doeblin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary channel violates the proposed complete hockey-stick bound using Hermitian alpha.",
        H("Complete hockey-stick contraction and the Hermitian Doeblin coefficient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-hockey-stick-hermitian-doeblin-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The proposed bound at gamma two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For the binary measure-and-prepare channel, the proposed inequality in Section 9.2(1) would imply that "
                    + "at gamma two the complete coefficient is at most one minus the trace of "
                    + "every Hermitian H with I tensor H below the unnormalized Choi operator. "
                    + "Definition 4 takes the supremum over these traces."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("complete-hockey-stick-hermitian-doeblin-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A Hermitian minorant of trace two fifths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The channel measures in the computational basis and prepares the rays "
                        + "of (1,0) and (4/5,3/5). Its unnormalized Choi operator has those two "
                        + "density matrices P and Q as diagonal blocks in input-first order. "
                        + "The matrix H = [[13,6],[6,-3]]/25 is Hermitian. The differences P − H "
                        + "and Q − H are 3/25 times the outer products of (2,-1) and (1,2), "
                        + "respectively, so I tensor H lies below the Choi operator.")),
                    Paragraph(Text(
                        "The trace of H is 2/5 and the complete coefficient at gamma two "
                        + "is at least 9/10, which exceeds 3/5. Hence the coefficient also "
                        + "exceeds one minus the supremum in Definition 4. Proposition 31 "
                        + "applies to alpha plus, whose feasible matrices must be positive "
                        + "semidefinite."))),
                DescribeRole.Theorem))));
}
