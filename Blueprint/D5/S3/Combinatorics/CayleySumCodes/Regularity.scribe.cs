using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class RegularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/Regularity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/GraphInvariants/Nikandish/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degrees and regularity of finite normal-connection sum graphs.",
        H("The exact square-set regularity dichotomy"),
        Blocks(
            Describe.Lean(DescribeId.Create("sum-graph-degree"),
                DeclarationHandle.Create(Prefix + "degree_card"), H("The exact open degree"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "At g the actual neighbor set is bijective with Y minus {g squared}, "
                    + "by h maps to g h. Its cardinal is therefore |Y| minus one when the "
                    + "square lies in Y and |Y| otherwise. Self-neighbors are excluded; "
                    + "inverse closure of Y is unnecessary. This is the degree calculation "
                    + "used in correction section 3.2 and the regularity antecedents."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("regularity-dichotomy"),
                DeclarationHandle.Create(Prefix + "result"), H("All squares or no squares"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every finite group and every conjugation-invariant connection "
                    + "set Y, all actual graph degrees are equal if and only if Y contains "
                    + "every square of G or contains none. Regularity is expressed by the "
                    + "neighbor cardinal at every vertex equaling that at the identity, "
                    + "which exists in every group. This supplies the full graph-regularity "
                    + "part of C7; abelian subgroup PC/TPC classifications, Frattini "
                    + "identities, the trivial-subgroup positive case and all reported "
                    + "enumeration tables remain separate obligations."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion"))]));
}
