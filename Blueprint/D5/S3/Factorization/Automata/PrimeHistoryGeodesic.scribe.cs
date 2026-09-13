using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class PrimeHistoryGeodesicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact contextual behavior has a shortest three-run representative, with a matching all-word bound.",
        H("Shortest Prime History Representatives"),
        Blocks(
            Paragraph(Text(
                "For a nonempty interval translation [l,u] with final displacement d in "
                + "capacity a, the necessary visited displacement interval is [-l,a-u]. "
                + "Every realizing history must account for both extrema. A word with the "
                + "same net displacement but a smaller excursion would have a different "
                + "legal starting-state set, and is not an admissible replacement.")),
            Describe.Lean(
                DescribeId.Create("prime-history-geodesic-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryGeodesic.word_length_lower_bound"),
                H("The sharp excursion cost lower bound applies to every word"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(2), Sp, F.Id("width(w)"), Sp, Minus, Sp,
                    F.Id("abs(displacement(w))"), Sp, Leq, Sp, F.Id("length(w)")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof inducts on the actual command list using the derived bounds "
                    + "low<=0<=high and low<=displacement<=high. Prepending one unit step "
                    + "increases the displayed required cost by at most one. The integer "
                    + "maximum of d and -d represents absolute displacement in the source."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-history-sharp-representative"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryGeodesic.shortest_realization"),
                H("The lower bound is attained by an explicit word"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("minimumLength"), Sp, Eq, Sp,
                    D(2), Sp, F.Id("(a-u+l)"), Sp, Minus, Sp, F.Id("abs(d)")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonnegative d, use the earlier lower-first realization. For negative "
                    + "d, reflect the capacity interval, realize the reflected form, then "
                    + "exchange multiplication and division. The proof computes its exact "
                    + "signature and length. Uniqueness of a nonempty normal form forces every "
                    + "competing word to have the same extrema and final displacement, so the "
                    + "all-word lower bound proves optimality. This is minimum operation count "
                    + "inside a contextual behavior class, not recovery of the original "
                    + "history's length and not a preservation theorem for other costs."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Factorization/Automata/PrimeHistoryNormalForm"))]));
}
