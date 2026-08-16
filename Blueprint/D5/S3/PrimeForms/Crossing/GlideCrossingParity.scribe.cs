using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Crossing;

internal sealed class GlideCrossingParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed-point-free glide involution pairs a finite crossing set into two-element orbits.",
        H("Glide Crossing Parity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-glide-pairing-makes-the-crossing-count-even"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/GlideCrossingParity."
                    + "glide_crossing_count_even"),
                H("A glide pairing makes the crossing count even"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("X"), Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open,
                    F.Id("X"), Close, CloseBracket, Comma, Esc,
                    Forall, Sp, F.Id("g"), Colon, Sp, F.Id("X"), Sp, To, Sp,
                    F.Id("X"), Comma, Esc,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    F.Id("g"), Open, F.Id("g"), Open, F.Id("x"), Close, Close,
                    Sp, Eq, Sp, F.Id("x"), Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    F.Id("g"), Open, F.Id("x"), Close, Sp, Neq, Sp, F.Id("x"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("Even")), Open,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("X"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let g be an involution of a finite crossing set with no fixed points. "
                            + "Join each crossing x to g(x). Involutivity makes adjacency "
                            + "symmetric, while the fixed-point-free hypothesis removes loops.")),
                    Paragraph(Text(
                        "Every vertex in the resulting simple graph has the unique neighbor "
                            + "g(x), so the full graph is a perfect matching. Mathlib's theorem "
                            + "SimpleGraph.Subgraph.IsPerfectMatching.even_card then gives even "
                            + "cardinality without reproving the matching parity theorem.")),
                    Paragraph(Text(
                        "This closes only the even-crossing assertion in remark 27.479-27.480. "
                            + "It does not formalize the numerical crossing counts, the Pell "
                            + "trace identification, or the rejected multiplicity model.")),
                    Paragraph(Text(
                        "Repository search found no equivalent D5 declaration. Pinned-Mathlib "
                            + "search found and reused IsPerfectMatching.even_card; no direct "
                            + "fixed-point-free involution parity theorem was found. Loogle had "
                            + "no matching declaration, and GitHub code search required "
                            + "authentication."))),
                DescribeRole.Theorem))));
}
