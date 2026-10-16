using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class TwelveStateFutureRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recovery of the original future residue", H("Recovery of the original future residue"),
        Blocks(
            Describe.Lean(DescribeId.Create("residue-target"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.residueTarget"),
                H("Only the time-one residue"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("residueTarget(z) is the index modulo three of the original hidden state H1. Its target omits the initial F/T phase."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("future-word"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.futureWord"),
                H("The actual future prefix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("futureWord(r,z) reads exactly the original emitted coordinates one through r from the same original hidden/output realization."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("residue-map"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.residueMAP"),
                H("The same-law initial-residue MAP choice"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each natural r, residueMAP is the existing fixed-order actual cell-mass maximizer for residueTarget and futureWord(r) under the original J. All words, ties and zero-mass observations remain in its total domain."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-future-residue-recovery"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateFutureRecovery.actual_future_residue_recovery"),
                H("Summable errors recover Z1"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On exactly the original J, every initial-residue MAP error at length r is at most ofReal((11/2)*rho^(r/2)), and these estimates are almost surely eventually equal to Z1. The source conclusion requires measurability of Z1; this proof uses a summable coefficient obtained before merging the twelve original hidden lifts. Actual state/future cylinder masses feed the actual MAP estimate. Their word probabilities factor through the six original phase/residue labels. Distinct initial residues remain distinct under every common word, so full affinity for such a pair equals its killed-pair survival affinity. The actual two-step affinity and specified_survival give the same rho=sqrt(15)/4. The proof does not infer an initial F/T phase decoder."))), DescribeRole.Theorem))));
}
