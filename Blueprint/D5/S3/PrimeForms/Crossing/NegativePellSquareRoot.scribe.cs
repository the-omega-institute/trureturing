using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Crossing;

internal sealed class NegativePellSquareRootDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A trace-zero square root of the negative-Pell discriminant produces a determinant-minus-one matrix.",
        H("The Negative-Pell Matrix Square Root"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("negative-pell-matrix-square-root"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/NegativePellSquareRoot.negative_pell_square_root"),
                H("The trace-zero discriminant root yields determinant minus one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("j"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    F.Id("V"), InMacro, Operatorname, Grp(F.Id("Mat")), Underscore, Grp(D(2)),
                    Open, Mathbb, Grp(F.Id("Z")), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("tr")), Open, F.Id("V"), Close, Eq, D(0), Sp, Land, Sp,
                    F.Id("V"), Caret, Grp(D(2)), Eq,
                    Open, D(3, 6), F.Id("j"), Caret, Grp(D(2)), Plus, D(1), Close, F.Id("I"),
                    Sp, Rightarrow, Sp,
                    F.Id("delta"), Eq, D(6), F.Id("j"), F.Id("I"), Plus, F.Id("V"), Comma, Sp,
                    Operatorname, Grp(F.Id("det")), Open, F.Id("delta"), Close, Eq, Minus, D(1),
                    Comma, Sp, F.Id("delta"), Caret, Grp(D(2)), Eq,
                    Open, D(7, 2), F.Id("j"), Caret, Grp(D(2)), Plus, D(1), Close, F.Id("I"),
                    Plus, D(1, 2), F.Id("j"), F.Id("V")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V be an integer 2x2 matrix of trace zero whose square is "
                        + "(36 j^2 + 1) times the identity. The matrix delta = 6 j I + V then has "
                        + "determinant -1, and delta^2 is exactly "
                        + "(72 j^2 + 1) I + 12 j V. This is the matrix form of the negative-Pell "
                        + "square-root construction in residual E.43.")),
                    Paragraph(Text(
                        "Mathlib's trace_fin_two turns trace V = 0 into V_11 = -V_00. The (0,0) "
                        + "entry of the square hypothesis gives V_00^2 + V_01 V_10 = 36 j^2 + 1. "
                        + "Substitution in Mathlib's det_fin_two formula gives det(6 j I + V) = -1. "
                        + "For the square formula, distributivity, commutation of scalar matrices, "
                        + "and the assumed value of V^2 reduce the result to two integer ring identities.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no theorem combining a trace-zero "
                        + "2x2 scalar square with this determinant and explicit square conclusion. Exact "
                        + "Mathlib hits were Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.scalar, and "
                        + "Matrix.scalar_comm; the proof imports and applies those declarations. This "
                        + "formalization closes only the delta-construction clause of E.43. It does not "
                        + "claim the inert-prime valuation lemma, the divisibility construction of V, the "
                        + "purity theorem, or the representation criterion."))),
                DescribeRole.Theorem
            )),
        []));
}
