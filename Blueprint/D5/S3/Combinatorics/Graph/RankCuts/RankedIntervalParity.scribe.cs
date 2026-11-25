using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.RankCuts;

internal sealed class RankedIntervalParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/RankCuts/RankedIntervalParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bound how often strict crossing parity can change across an ordered list of ranks.",
        H("Changes of strict crossing parity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rank-cut-padded-parity"),
                DeclarationHandle.Create(Prefix + "paddedParity"),
                H("Strict crossings on the observed ranks"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(
                    Call("PaddedParity", F.Id("j")), FormulaRelationOperator.Equal,
                    Call("PaddedStrictCrossingsModTwo", F.Id("j"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The observation at slot j for 1 ≤ j ≤ n is cut j−1. "
                    + "An indexed interval contributes exactly when its lower endpoint is "
                    + "strictly below the cut and its upper endpoint is strictly above it. "
                    + "PaddedStrictCrossingsModTwo is the number of contributing indices "
                    + "modulo two at such slots and zero at all other natural-number slots."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rank-cut-parity-changes"),
                DeclarationHandle.Create(Prefix + "changes_le_twice_jumps"),
                H("Every interval supplies at most two changes of cut parity"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(
                    Call("AdjacentChanges", F.Id("p")), FormulaRelationOperator.LessThanOrEqual,
                    Call("TwiceCardinality", F.Id("I"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let I be a finite index type, let n be a natural number "
                        + "and take a monotone list of n natural-number cuts. Each index has "
                        + "two natural-number endpoints. The sequence p consists of the "
                        + "strict crossing parities at these cuts, with zero at both ends. "
                        + "AdjacentChanges(p) counts neighboring unequal entries, including "
                        + "both padding boundaries. TwiceCardinality(I) is twice the number "
                        + "of indices.")),
                    Paragraph(Text("The cuts strictly between the endpoints occupy a contiguous "
                        + "block. If no block starts or ends at a boundary then every index "
                        + "gives the same contribution on either side, so parity does not "
                        + "change there. Counting endpoints with multiplicity gives the bound. "
                        + "For example, at three cuts parities one, zero, one require four "
                        + "changes and hence at least two intervals. Degree and support "
                        + "constraints must be checked independently when constructing a factor."))),
                DescribeRole.Theorem))));
}
