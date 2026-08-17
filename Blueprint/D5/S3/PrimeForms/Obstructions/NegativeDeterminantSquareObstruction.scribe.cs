using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Obstructions;

internal sealed class NegativeDeterminantSquareObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Determinant minus one prevents an integer matrix from being a matrix square.",
        H("The Negative-Determinant Square Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("determinant-minus-one-obstructs-matrix-squares"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Obstructions/NegativeDeterminantSquareObstruction."
                    + "det_neg_one_not_matrix_square"),
                H("A determinant-minus-one integer matrix is not a square"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Comma, Sp,
                    F.Id("M"), InMacro, Operatorname, Grp(F.Id("Mat")),
                    Underscore, F.Id("n"), Open, Mathbb, Grp(F.Id("Z")), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("det")), Open, F.Id("M"), Close,
                    Eq, Minus, D(1), Sp, Rightarrow, Sp,
                    Neg, Sp, Exists, Sp, F.Id("A"), InMacro,
                    Operatorname, Grp(F.Id("Mat")), Underscore, F.Id("n"),
                    Open, Mathbb, Grp(F.Id("Z")), Close, Comma, Sp,
                    F.Id("A"), Caret, Grp(D(2)), Eq, F.Id("M")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If M were A squared, determinant multiplicativity would give "
                        + "det(M) = det(A)^2. An integer square is nonnegative, contradicting "
                        + "det(M) = -1. The argument works in every finite matrix dimension.")),
                    Paragraph(Text(
                        "Repository search found concrete determinant-minus-one calculations but no "
                        + "general matrix-square obstruction. Pinned Mathlib text search and "
                        + "smart_search.sh found no exact theorem; the exact reusable declarations "
                        + "were Matrix.det_mul and mul_self_nonneg. An external GitHub-index search "
                        + "through Tavily likewise returned no exact declaration. The Lean proof "
                        + "therefore applies those two Mathlib results directly.")),
                    Paragraph(Text(
                        "This closes only the determinant-minus-one obstruction sentence in residual "
                        + "remark 27.399-27.400. It does not claim that an odd word square is primitive, "
                        + "the balance formula, the trace divisibility statement, the census, or the "
                        + "zero-layer dimension bound stated elsewhere in the same atom."))),
                DescribeRole.Theorem
            )),
        []));
}
