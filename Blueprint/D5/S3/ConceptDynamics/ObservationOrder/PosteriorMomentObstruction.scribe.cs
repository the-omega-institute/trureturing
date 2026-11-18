using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class PosteriorMomentObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/ObservationOrder/PosteriorMomentObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational five-target candidate moment satisfies centered matrix positivity and fails finite posterior realizability.",
        H("An obstruction to posterior moment realizability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("posterior-moment-sufficiency-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Candidate sufficient conditions at a uniform prior"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The prior puts mass one fifth on each of five targets. The claim asks whether every "
                    + "symmetric real matrix with nonnegative entries, row sums equal to the prior, and "
                    + "positive semidefinite centered part is a finite mixture of posterior outer products. "
                    + "The mixture masses and the coordinates of each posterior vector are nonnegative and "
                    + "sum to one over their respective index sets. The row sums determine the mixture barycenter."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("posterior-moment-obstruction"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A five-cycle moment refutes the claim"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Index the targets by a cycle of length five. The proposed moment has diagonal entries "
                        + "5/55, entries 3/55 on adjacent pairs, and zero elsewhere. Its row sums are 1/5. "
                        + "An exact sum of four squares gives the quadratic form of its centered part and "
                        + "establishes positive semidefiniteness.")),
                    Paragraph(Text(
                        "Zero entries on nonedges force every positive-mass posterior to have support in a clique "
                        + "of the cycle. Each clique has at most two vertices. On such a support, the sum of squares "
                        + "is at least twice the sum of products along cycle edges. Summing over posterior components "
                        + "would bound twice the edge sum by the trace. The proposed moment has twice the edge sum "
                        + "30/55 and trace 25/55.")),
                    Paragraph(Text(
                        "The conclusion concerns finite mixtures and this specified uniform prior. The contradiction "
                        + "holds for any finite number of nonnegative factors, with or without their normalization."))),
                DescribeRole.Theorem))));
}
