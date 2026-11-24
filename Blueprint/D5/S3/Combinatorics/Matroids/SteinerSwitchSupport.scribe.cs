using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerSwitchSupportDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerSwitchSupport";
    private static readonly LibraryNoteRef CriticalProblem =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/gruica2023mrdcolumnlimit");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subspace criteria for common Steiner return patterns and simultaneous switch counts.",
        H("Simultaneous Steiner Switch Supports"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("steiner-return-support-codimension"),
                DeclarationHandle.Create(Module + ".realizesReturnSupport"),
                H("The codimension criterion for return supports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(CriticalProblem),
                Blocks(
                    Paragraph(Text("Take the binary span of the requested circuit rows in a finite Steiner loop with trivial centre. Quotient that span by the span of the rows required to have zero return. One labelling has the specified zero pattern on the full requested components exactly when a subspace of the quotient avoids every projected row required to have nonzero return and has codimension at most the binary dimension of the fibre.")),
                    Paragraph(Text("The kernel of the realized return map contains the span of the zero rows and descends to such a subspace. Conversely, embed the quotient by the avoiding subspace in the fibre. Extend the resulting map on the row span to the space of triples and take its values on the triple basis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("steiner-switch-count-fibre-profile"),
                DeclarationHandle.Create(Module + ".commonSwitchCounts"),
                H("The range of simultaneous counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(CriticalProblem),
                Blocks(
                    Paragraph(Text("A family of counts of noncommuting starts in one normalized extension with the identity fibre as its centre is realizable exactly when one subspace of the triple-coordinate space gives all the counts. Its codimension is at most the fibre dimension. For each pivot pair, count every quotient vertex that fails to return within two rounds and every other vertex whose circuit row lies outside the subspace. Multiply this number by the size of the fibre."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("steiner-shared-labelled-counts"),
                DeclarationHandle.Create(Module + ".labelledCommonSwitchCounts"),
                H("Realizing the profile in one labelled triple system"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(CriticalProblem),
                Blocks(
                    Paragraph(Text("For a nontrivial base loop and distinct nonidentity members of every pivot pair, the same normalized extension and the same labelled complete triple system realize the counts supplied by the chosen subspace. The extension has exactly the identity fibre as its centre. Its triple labelling has exactly the chosen subspace as its kernel, so the same system realizes the support and the count profile. The matching of uncovered pairs after each deletion is the actual matching of that labelled system. The fibre count therefore applies to the successful switch starts for all the specified deletions and pivots."))),
                DescribeRole.Theorem))));
}
