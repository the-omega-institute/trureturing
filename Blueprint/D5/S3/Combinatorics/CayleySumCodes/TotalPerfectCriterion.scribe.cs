using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class TotalPerfectCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact fixed-connection-set two-case criterion for total perfect subgroup codes.",
        H("The missing two-element case in a loopless sum graph"),
        Blocks(
            Describe.Lean(DescribeId.Create("normal-connection-set"),
                DeclarationHandle.Create(Prefix + "NormalSubset"), H("A normal subset"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Y is stable under conjugation a*x*a^-1 for every a in the group. "
                    + "It need not be a subgroup, inverse closed, or disjoint from the identity."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("loopless-sum-graph"),
                DeclarationHandle.Create(Prefix + "sumGraph"), H("The actual Cayley sum graph"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The vertices are the group elements. Distinct g,h are adjacent exactly "
                    + "when g*h belongs to Y. Conjugation invariance makes this symmetric. "
                    + "Equality is always excluded, including when g*g belongs to Y. "
                    + "This is the sum graph of the source, with no inverse closure hypothesis."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("open-neighbor-code"),
                DeclarationHandle.Create(Prefix + "IsTotalPerfectCode"), H("Total perfect codes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Every vertex g has exactly one open neighbor in C. This condition applies "
                    + "also to g in C; self-neighbors never count. The predicate is stated with "
                    + "existence and uniqueness in the actual SimpleGraph, not a count supplied "
                    + "as a hypothesis."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("subgroup-square-set"),
                DeclarationHandle.Create(Prefix + "squares"), H("Squares in the subgroup"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The square set consists of h*h for h in H, viewed in the ambient group. "
                    + "A nonsquare of H can be a square of the ambient group. No subgroup "
                    + "structure is imposed on this set in a noncommutative group."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-two-case-criterion"),
                DeclarationHandle.Create(Prefix + "result"), H("Both directions and both cases"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For every finite group G, every subgroup H, and every fixed normal "
                        + "subset Y, H is a total perfect code precisely when each outside left "
                        + "coset gH meets Y once and one of two conditions holds. Either "
                        + "Y intersect H is a singleton {z} whose element is a nonsquare of H; "
                        + "or Y intersect H has two elements and contains every square of H. "
                        + "H need not be normal. Coset membership is the exact condition "
                        + "g^-1*y in H.")),
                    Paragraph(Text(
                        "Multiplication h maps to g*h is a bijection between the open H-neighbors "
                        + "of g and (Y intersect gH) with g*g erased. If g is outside H, the erased "
                        + "element was absent already. If g is in H, the slice is Y intersect H. "
                        + "At g=1 the unique-neighbor condition forces its size to be one or two. "
                        + "In size one no subgroup square can be that element; in size two every "
                        + "subgroup square must be one of the two elements. These same bijections "
                        + "prove sufficiency in both cases.")),
                    Paragraph(Text(
                        "The primary source is Theorem 2.1 in both public versions of Ma, "
                        + "Nikandish and Zhang, with version identities distinguished in the "
                        + "library note. The two-element branch corrects the antecedent total-code "
                        + "necessity. The surviving transversal sufficiency is not refuted. "
                        + "Quantifying Y gives the corresponding existence criterion. "
                        + "Index-cardinality formulas, induced-matching parity, actual Q8/D8 "
                        + "and order-32 examples, normalized perfect codes and the later "
                        + "classification/equivalence outcomes remain separate obligations."))),
                DescribeRole.Theorem)), []));
}
