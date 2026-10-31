using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class ContractingCoverRegularClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Uniformly contracting open self-covers propagate a nonempty open patch throughout a compact metric carrier.",
            H("Regular closure from a contracting open cover"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("contracting-cover-regular-closure"),
                    DeclarationHandle.Create("D5/S3/Topology/ContractingCoverRegularClosure.closure_interior_eq_of_contracting_cover"),
                    H("The parametric regular closure theorem"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Let K be compact in any metric space, with nonempty interior. A family f_i of open maps "
                        + "with one common NNReal Lipschitz constant q < 1 and exact union of images equal to K "
                        + "forces closure(interior K) = K. The branch index need not be finite, and no ambient "
                        + "completeness or properness is assumed. "
                        + "The consumed core lemma requires a closed nonempty C contained in K, invariant under "
                        + "every branch, and covering preimages from K. Compactness of C supplies nearest points; "
                        + "the continuous distance to C attains a maximum M on K. A covering preimage and its "
                        + "nearest point give M <= q M, hence M = 0 and C = K. The nonemptiness of C is explicit "
                        + "because real-valued infDist of the empty set is zero. "
                        + "For C = closure(interior K), compactness makes C compact and contained in K. Open "
                        + "branches preserve the interior and Lipschitz continuity preserves its closure. "
                        + "This is a classical contraction argument, with no literature novelty claim; the "
                        + "actual Tribonacci Rauzy closure consumes this inference together with its proved symbolic cover."))), DescribeRole.Theorem)),
            [

            ]));
    }
}
