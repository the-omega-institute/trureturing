using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Crossing;

internal sealed class NegativeDeterminantTraceSquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A 2x2 integer matrix of determinant -1 has trace of its square equal to trace squared plus two.",
        H("The Trace Square at Determinant Minus One"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("trace-square-at-determinant-minus-one"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/NegativeDeterminantTraceSquare.trace_square_of_det_neg_one"),
                H("Determinant minus one fixes the trace of the square"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("A"), InMacro, Operatorname, Grp(F.Id("Mat")),
                    Underscore, Grp(D(2)), Open, Mathbb, Grp(F.Id("Z")), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("det")), Open, F.Id("A"), Close, Eq, Minus, D(1),
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("tr")), Open, F.Id("A"), Caret, Grp(D(2)), Close,
                    Eq, Operatorname, Grp(F.Id("tr")), Open, F.Id("A"), Close,
                    Caret, Grp(D(2)), Plus, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a 2x2 matrix A, direct expansion gives tr(A^2) = tr(A)^2 - 2 det(A). "
                        + "The determinant hypothesis det(A) = -1 therefore gives "
                        + "tr(A^2) = tr(A)^2 + 2.")),
                    Paragraph(Text(
                        "Pinned Mathlib and repository searches found no exact trace-square theorem. "
                        + "The proof imports and applies Mathlib's Matrix.trace_fin_two and "
                        + "Matrix.det_fin_two expansions, expands the two-entry matrix products, and "
                        + "closes the resulting integer polynomial identity with ring.")),
                    Paragraph(Text(
                        "This formalizes only clause (c) of residual E.38: the trace identity forced by "
                        + "determinant -1. It does not assert the word-primitivity criterion, balance, "
                        + "the square-city parameter formula, divisibility by 12, the census, or the "
                        + "zero-layer dimension bound stated elsewhere in that atom."))),
                DescribeRole.Theorem
            )),
        []));
}
