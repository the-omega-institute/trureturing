using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints.Algebraic;

internal sealed class GoldenTransferTriangleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive critical radius, the positive first Gauss fixed point, its local "
            + "multiplier, and the shortest golden geodesic obey the golden transfer triangle.",
        H("Golden Transfer Triangle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-transfer-triangle"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/Algebraic/GoldenTransferTriangle."
                        + "golden_transfer_triangle"),
                H("The golden radius links the Gauss branch and shortest geodesic"),
                StatementSource.FromAuthor(TransferTriangleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let psi_1(x) = 1/(x+1). The five hypotheses are the adjacent-source "
                            + "characterizations: r_* is positive and satisfies its critical "
                            + "quadratic, x_* is positive and fixed by psi_1, and ell_phi is "
                            + "four times log(phi). These are assumptions about the source "
                            + "objects, not restatements of any conclusion leaf.")),
                    Paragraph(Text(
                        "The first boxed group has exactly four equality leaves: r_* = phi, "
                            + "x_* = r_* - 1, x_* = phi^(-1), and the absolute derivative "
                            + "equals r_*^(-2). The second boxed group is the fifth leaf, "
                            + "exp(-ell_phi) = r_*^(-4).")),
                    Paragraph(Text(
                        "The proof imports the repository's positive golden fixed-point "
                            + "uniqueness theorem, uses Mathlib's derivative rule for inversion, "
                            + "and rewrites the sourced length equation with elementary "
                            + "exponential and logarithm identities. It uses no conjectural "
                            + "or Riemann-hypothesis premise."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S1/FixedPoints/Algebraic/GoldenFixedPoint"))]));

    private static Formula TransferTriangleFormula()
    {
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula rStar = new Formula.Subscript(F.Id("r"), Star);
        Formula xStar = new Formula.Subscript(F.Id("x"), Star);
        Formula ellPhi = new Formula.Subscript(Ell, Varphi);
        Formula psiOne = new Formula.Subscript(Psi, D(1));
        Formula psiAtX = Seq(psiOne, Open, xStar, Close);
        Formula derivativeAtX = Seq(psiOne, Apos, Open, xStar, Close);

        Formula premises = Seq(
            D(0), Sp, Lt, Sp, rStar, Sp, Land, Sp,
            new Formula.Power(rStar, D(2)), Sp, Eq, Sp, rStar, Sp, Plus, Sp, D(1), Sp,
            Land, Sp, D(0), Sp, Lt, Sp, xStar, Sp, Land, Sp,
            psiAtX, Sp, Eq, Sp, xStar, Sp, Land, Sp,
            ellPhi, Sp, Eq, Sp, D(4), Sp, Cdot, Sp, Log, Open, Varphi, Close);

        Formula firstBox = Seq(
            rStar, Sp, Eq, Sp, Varphi, Sp, Land, Sp,
            xStar, Sp, Eq, Sp, rStar, Sp, Minus, Sp, D(1), Sp, Land, Sp,
            xStar, Sp, Eq, Sp, new Formula.Power(Varphi, new Formula.Negate(D(1))), Sp,
            Land, Sp, new Formula.Absolute(derivativeAtX), Sp, Eq, Sp,
            new Formula.Power(rStar, new Formula.Negate(D(2))));

        Formula secondBox = Seq(
            Exp, Open, new Formula.Negate(ellPhi), Close, Sp, Eq, Sp,
            new Formula.Power(rStar, new Formula.Negate(D(4))));

        return Disp(Seq(
            Forall, Sp, rStar, Comma, Sp, xStar, Comma, Sp, ellPhi,
            Sp, InMacro, Sp, reals, Comma, Sp,
            Open, premises, Close, Sp, Rightarrow, Sp,
            Open, Open, firstBox, Close, Sp, Land, Sp, secondBox, Close, Dot));
    }
}
