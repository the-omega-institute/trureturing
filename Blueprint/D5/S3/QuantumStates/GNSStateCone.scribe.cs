using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class GNSStateConeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positivity and normalization clauses of a finite matrix state are sections of its GNS norm-square identity.",
        H("Matrix-State Cone Sections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("matrix-state-positivity-and-normalization-are-gns-cone-sections"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumStates/GNSStateCone.state_cone_sections"),
                H("Matrix-state positivity and normalization are GNS cone sections"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("d"), Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("d"), Close,
                    CloseBracket, Comma, Esc,
                    OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, F.Id("d"), Close,
                    CloseBracket, Comma, Esc,
                    Forall, Sp, Rho, InMacro, Sp, F.Id("M"), Underscore,
                    Grp(F.Id("d")), Open, Mathbb, Grp(F.Id("C")), Close, Comma, Esc,
                    Operatorname, Grp(F.Id("PosSemidef")), Open, Rho, Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Tr")), Open, Rho, Close, Eq, D(1), Sp,
                    Rightarrow, Sp, OpenBracket, RowBreak,
                    Left, Open, Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("M"), Underscore,
                    Grp(F.Id("d")), Open, Mathbb, Grp(F.Id("C")), Close, Comma, Esc,
                    Operatorname, Grp(F.Id("Tr")), Open, Rho, Sp, F.Id("x"), Caret,
                    Grp(Star), Sp, F.Id("x"), Close, Eq,
                    Vert, Sp, F.Id("x"), Sqrt, Grp(Rho), Vert, Underscore,
                    Grp(F.Id("HS")), Caret, Grp(D(2)), Sp, Land, Sp,
                    D(0), Sp, Leq, Sp,
                    Operatorname, Grp(F.Id("Tr")), Open, Rho, Sp, F.Id("x"), Caret,
                    Grp(Star), Sp, F.Id("x"), Close, Right, Close, Sp, Land, RowBreak,
                    Operatorname, Grp(F.Id("Tr")), Open, Rho, Sp, D(1), Caret,
                    Grp(Star), Sp, D(1), Close, Eq, D(1), Sp, Land, RowBreak,
                    Vert, Sqrt, Grp(Rho), Vert, Underscore, Grp(F.Id("HS")),
                    Caret, Grp(D(2)), Eq,
                    Operatorname, Grp(F.Id("Tr")), Open, Rho, Close, Sp, Land, RowBreak,
                    Operatorname, Grp(F.Id("Tr")), Open, Rho, Close, Eq, D(1),
                    RowBreak, CloseBracket))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let d be a finite index type and rho a positive semidefinite complex d-by-d matrix with trace one. For every complex matrix x, the trace expectation of x star x is exactly the squared Frobenius norm of x times the positive continuous-functional-calculus square root of rho, and is therefore nonnegative.")),
                    Paragraph(Text(
                        "Specializing x to the identity gives normalized expectation one. The same specialization identifies the squared Frobenius norm of the square root of rho with the trace of rho, which is one. Thus the two state-space clauses are the positivity and identity sections of the same squared-length formula.")),
                    Paragraph(Text(
                        "The declaration reuses the matrix GNS identity rather than proving it again. Its scope is finite-dimensional complex matrix algebras; it makes no claim for arbitrary C-star algebras."))),
                DescribeRole.Theorem))));
}
