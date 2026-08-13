using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Diagonalization;

internal sealed class BooleanSwapLoadDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boolean negation is exactly the operation that carries universal self-diagonal escape.",
        H("The Load Carried by the Boolean Swap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boolean-swap-carries-diagonal-escape"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Diagonalization/BooleanSwapLoad.boolean_swap_carries_diagonal_escape"),
                H("The Boolean swap carries universal diagonal escape"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, SigmaLower, Colon, Sp,
                    F.Id("Bool"), To, Sp, F.Id("Bool"), Comma, Sp,
                    Open,
                    Open, Forall, Sp,
                    Open, F.Id("History"), Sp, Colon, Sp, F.Id("Type"), Close, Sp,
                    Open, F.Id("V"), Sp, Colon, Sp,
                    F.Id("History"), To, Sp, F.Id("History"), To, Sp, F.Id("Bool"),
                    Close, Sp, Open, F.Id("h"), Sp, Colon, Sp, F.Id("History"), Close,
                    Comma, Sp,
                    SigmaLower, Open, F.Id("V"), Open, F.Id("h"), Comma, F.Id("h"), Close,
                    Close, Sp, Neq, Sp,
                    F.Id("V"), Open, F.Id("h"), Comma, F.Id("h"), Close,
                    Close, Sp, Iff, Sp, SigmaLower, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("Bool"), Dot, F.Id("not")),
                    Close, RowBreak, Sp, Land, Sp, Neg, Open, Forall, Sp,
                    Open, F.Id("History"), Sp, Colon, Sp, F.Id("Type"), Close, Sp,
                    Open, F.Id("V"), Sp, Colon, Sp,
                    F.Id("History"), To, Sp, F.Id("History"), To, Sp, F.Id("Bool"),
                    Close, Sp, Open, F.Id("h"), Sp, Colon, Sp, F.Id("History"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("id")), Open,
                    F.Id("V"), Open, F.Id("h"), Comma, F.Id("h"), Close, Close,
                    Sp, Neq, Sp,
                    F.Id("V"), Open, F.Id("h"), Comma, F.Id("h"), Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let sigma be an operation on the minimal binary carrier Bool. The first "
                        + "conjunct isolates the engine shared by the source diagonal consequences: "
                        + "for every history type, every total Boolean evaluator V, and every "
                        + "self-coordinate h, applying sigma to V(h,h) changes that value exactly "
                        + "when sigma is Boolean negation.")),
                    Paragraph(Text(
                        "The second conjunct records the source's deletion test explicitly. Replacing "
                        + "the swap by identity fails on the constant-false evaluator over Unit, so "
                        + "the diagonal contradiction has no statement after the swap is removed. "
                        + "Conversely, Bool.not_ne_self supplies the mismatch for negation; testing any "
                        + "universally escaping operation on the two constant diagonals forces both of "
                        + "its values and hence forces the operation itself to be Bool.not.")),
                    Paragraph(Text(
                        "The neighboring DiagonalSwap theorem proves the forward mismatch for a fixed "
                        + "natural-number assignment. This theorem quantifies over every history type "
                        + "and evaluator, proves the converse characterization, and includes the "
                        + "identity deletion witness, so it is not a renamed duplicate."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Conventions/DiagonalSwap"))]));
}
