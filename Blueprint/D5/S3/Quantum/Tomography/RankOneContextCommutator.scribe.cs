using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class RankOneContextCommutatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete normalized rank-one contexts satisfy the aggregate projection commutator formula.",
        H("Rank-One Context Commutator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-one-contexts-satisfy-the-aggregate-commutator-formula"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/RankOneContextCommutator."
                        + "aggregated_rank_one_context_commutator"),
                H("Aggregate projection commutator formula"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let B and C be complete normalized rank-one projective contexts in "
                            + "complex dimension d, with d at least two. Each projection is "
                            + "self-adjoint, idempotent, has trace one, and satisfies the "
                            + "rank-one sandwich law; each context resolves the identity.")),
                    Paragraph(Text(
                        "The squared Hilbert-Schmidt norm is represented by the real part of "
                            + "trace(A* A). The proof applies the exact trace conjugation, "
                            + "cyclicity, finite-sum, and scalar-linearity declarations from "
                            + "the pinned library to obtain the pairwise identity "
                            + "2 m (1-m), then sums it over both contexts.")),
                    Paragraph(Text(
                        "Completeness makes the total overlap equal to d. Cancelling the "
                            + "nonzero factor d-1 against the definition of normalized "
                            + "incompatibility gives the displayed formula without fixing a "
                            + "particular dimension or pair of contexts."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula left = F.Id("B");
        Formula right = F.Id("C");
        Formula dimension = F.Id("d");
        Formula contexts = Apply("CompleteNormalizedRankOneContexts", left, right, dimension);
        Formula aggregate = Apply("AggregateCommutatorSquare", left, right);
        Formula incompatibility = Apply("Incompatibility", left, right);
        return Disp(Seq(
            contexts, Sp, Land, Sp, D(2), Sp, Leq, Sp, dimension, Sp, Rightarrow, RowBreak,
            aggregate, Sp, Eq, Sp, D(2), Open, dimension, Sp, Minus, Sp, D(1), Close,
            incompatibility, Dot));
    }
}
