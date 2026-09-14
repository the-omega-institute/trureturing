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
                DescribeId.Create("prime-history-sharp-representative"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Automata/PrimeHistoryGeodesic.shortest_realization"),
                H("The lower bound is attained by an explicit word"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("normal(a,shortestWord(t))"), Sp, Eq, Sp, F.Id("some(t)"), Sp, Land, Sp,
                    F.Id("length(shortestWord(t))"), Sp, Eq, Sp,
                    D(2), Sp, F.Id("(a-u+l)"), Sp, Minus, Sp, F.Id("abs(d)"), Sp, Land, Sp,
                    Forall, Sp, F.Id("w"), Comma, Sp,
                    F.Id("normal(a,w)"), Sp, Eq, Sp, F.Id("some(t)"), Sp, Rightarrow, Sp,
                    F.Id("length(shortestWord(t))"), Sp, Leq, Sp, F.Id("length(w)")))),
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
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Factorization/Automata/PrimeHistoryNormalForm")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Factorization/Automata/WordExcursionLowerBound"))
        ]));
}
