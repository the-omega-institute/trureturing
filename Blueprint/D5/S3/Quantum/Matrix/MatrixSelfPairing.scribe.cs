using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class MatrixSelfPairingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive trace-one matrix weights pair operations with themselves as nonnegative norm squares.",
        H("Matrix Self-Pairing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-matrix-self-pairings-are-nonnegative-norm-squares"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Matrix/MatrixSelfPairing.matrix_self_pairing_and_nonnegative"),
                H("Positive matrix self-pairings are nonnegative norm squares"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("d"), Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("d"), Close,
                    CloseBracket, Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, F.Id("d"), Close,
                    CloseBracket, Comma, Esc,
                    Forall, Sp, Rho, Comma, F.Id("x"), InMacro, Sp, F.Id("M"), Underscore,
                    Grp(F.Id("d")), Open, Mathbb, Grp(F.Id("C")), Close, Comma, Esc,
                    Operatorname, Grp(F.Id("PosSemidef")), Open, Rho, Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Tr")), Open, Rho, Close, Eq, D(1), Sp,
                    Rightarrow, Sp, Open,
                    Operatorname, Grp(F.Id("Tr")), Open, Rho, Sp, F.Id("x"), Caret,
                    Grp(Star), Sp, F.Id("x"), Close, Eq,
                    Vert, Sp, F.Id("x"), Sqrt, Grp(Rho), Vert, Underscore, Grp(F.Id("HS")),
                    Caret, Grp(D(2)), Sp, Land, Sp,
                    D(0), Le, Vert, Sp, F.Id("x"), Sqrt, Grp(Rho), Vert, Underscore,
                    Grp(F.Id("HS")), Caret, Grp(D(2)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite index type d, positive semidefinite complex square " +
                        "matrix rho with trace one, and complex square matrix x, the trace of " +
                        "rho times x star times x equals the squared Frobenius norm of x times " +
                        "the positive continuous-functional-calculus square root of rho, and " +
                        "that real norm square is nonnegative. The displayed Hilbert-Schmidt " +
                        "notation denotes the Frobenius norm."))),
                DescribeRole.Theorem))));
}
