using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class ZaunerSymplecticMatrixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit modular Zauner matrix has order three and fixes the displayed residue vector.",
        H("An Exact Modular Zauner-Matrix Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zauner-symplectic-matrix-certificate"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumContext/ZaunerSymplecticMatrix."
                    + "zauner_symplectic_matrix_certificate"),
                H("The displayed modular Zauner matrix has order three and a fixed vector"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be the matrix with rows (6,23) and (19,17) over Z/24Z, and let "
                            + "v=(8,16). Exact residue arithmetic gives det(S)=1 and tr(S)=-1. "
                            + "The matrix satisfies S^2+S+I=0 and S^3=I, while S is not the "
                            + "identity, so its order is exactly three. Direct matrix-vector "
                            + "multiplication gives Sv=v.")),
                    Paragraph(Text(
                        "The pinned mathlib search found the general two-by-two determinant and "
                            + "trace formulas, which the Lean proof applies before reducing the "
                            + "finite residue equalities in the kernel. No unchecked evaluator, "
                            + "native_decide, numerical approximation, or private axiom is used.")),
                    Paragraph(Text(
                        "This is an instance-level certificate for the explicit matrix and fixed "
                            + "vector in the source clause. It does not formalize the exhaustive "
                            + "GL(2,Z/24Z) search, identify the full value-preserving group with "
                            + "Z/6Z, or rule out additional antiunitary symmetries."))),
                DescribeRole.Theorem))));

    private static Formula CertificateFormula()
    {
        Formula matrix = F.Id("S");
        Formula vector = F.Id("v");
        Formula identity = F.Id("I");

        return Disp(Seq(
            matrix, Eq, Begin, Grp(F.Id("pmatrix")),
            D(6), Amp, D(2, 3), RowBreak, D(1, 9), Amp, D(1, 7),
            End, Grp(F.Id("pmatrix")), Comma, Sp,
            vector, Eq, Open, D(8), Comma, Sp, D(1, 6), Close, Comma, RowBreak,
            Operatorname, Grp(F.Id("det")), Open, matrix, Close, Eq, D(1), Sp, Land, Sp,
            Operatorname, Grp(F.Id("tr")), Open, matrix, Close, Eq, Minus, D(1), Sp, Land,
            RowBreak, matrix, Caret, Grp(D(2)), Plus, matrix, Plus, identity, Eq, D(0), Sp,
            Land, Sp, matrix, Caret, Grp(D(3)), Eq, identity, Sp, Land, Sp,
            matrix, Neq, Sp, identity, Sp, Land, Sp, matrix, vector, Eq, vector, Dot));
    }
}
