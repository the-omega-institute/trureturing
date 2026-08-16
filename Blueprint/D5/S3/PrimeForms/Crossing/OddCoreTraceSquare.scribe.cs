using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Crossing;

internal sealed class OddCoreTraceSquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A determinant-minus-one integer matrix satisfies the odd-core trace-square identity.",
        H("The Odd-Core Trace-Square Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("odd-core-trace-square"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/OddCoreTraceSquare.trace_square_eq_of_det_neg_one"),
                H("Determinant minus one fixes the trace of the square"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("delta"), InMacro, Operatorname, Grp(F.Id("Mat")),
                    Underscore, Grp(D(2)), Open, Mathbb, Grp(F.Id("Z")), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("det")), Open, F.Id("delta"), Close, Eq, Minus, D(1),
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("tr")), Open, F.Id("delta"), Caret, Grp(D(2)), Close,
                    Eq, Operatorname, Grp(F.Id("tr")), Open, F.Id("delta"), Close, Caret,
                    Grp(D(2)), Plus, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let delta be a 2x2 integer matrix with determinant -1. Then the trace of "
                        + "delta squared equals the square of the trace of delta plus two. This is "
                        + "the trace-square clause (c) of the odd-core theorem in residual E.38.")),
                    Paragraph(Text(
                        "The proof expands the two diagonal entries of delta squared and substitutes "
                        + "the determinant hypothesis. It directly applies Mathlib declarations "
                        + "Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, and "
                        + "Fin.sum_univ_two; integer nonlinear arithmetic closes the resulting identity.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no existing declaration of this "
                        + "exact trace-square identity. Matrix.charpoly_fin_two provides the related "
                        + "two-dimensional characteristic-polynomial formula. This formalization does "
                        + "not claim the primitive-word, balance, pinned-divisibility, or dimension-bound "
                        + "clauses (a), (b), and (d) of E.38."))),
                DescribeRole.Theorem
            )),
        []));
}
