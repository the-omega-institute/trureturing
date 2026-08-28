using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints.Algebraic;

internal sealed class GoldenTransferTriangleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximal real disk, the Mayer operator, its first fixed branch, and the shortest "
            + "modular geodesic select the golden transfer triangle without caller premises.",
        H("Golden Transfer Triangle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-transfer-triangle"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/Algebraic/GoldenTransferTriangle."
                        + "golden_transfer_triangle"),
                H("The maximal disk and Mayer operator select the golden triangle"),
                StatementSource.FromAuthor(TransferTriangleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There are no public premises. The proof chooses r_*, x_*, and ell_phi "
                            + "from concrete source carriers: the sharp real disk IsLUB, the "
                            + "first branch of the full Mayer operator, and the least positive "
                            + "PSL_2(Z) hyperbolic-trace length.")),
                    Paragraph(Text(
                        "The modular length carrier consists of positive ell for which "
                            + "2 cosh(ell/2) is an integer trace at least three. Its least "
                            + "member is 4 log(phi), and exp(-ell_phi) = r_*^(-4).")),
                    Paragraph(Text(
                        "For every natural weight, the Mayer operator is exactly the sum over "
                            + "psi_n(x) = 1/(x+n), n >= 1. Its defining formula contains no "
                            + "golden parameter; phi is selected by maximality and the fixed "
                            + "branch. The proof uses no conjectural premise."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S1/FixedPoints/Algebraic/GoldenFixedPoint"))]));

    private static Formula TransferTriangleFormula()
    {
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula rStar = new Formula.Subscript(F.Id("r"), Star);
        Formula xStar = new Formula.Subscript(F.Id("x"), Star);
        Formula ellPhi = new Formula.Subscript(Ell, Varphi);
        Formula r = F.Id("r");
        Formula n = F.Id("n");
        Formula w = F.Id("w");
        Formula x = F.Id("x");
        Formula f = F.Id("f");
        Formula psiOne = new Formula.Subscript(Psi, D(1));
        Formula psiAtX = Seq(psiOne, Open, xStar, Close);
        Formula derivativeAtX = Seq(psiOne, Apos, Open, xStar, Close);
        Formula diskSet = Seq(
            OpenBrace, r, Sp, Mid, Sp, D(1), Sp, Le, Sp, r, Sp, Land, Sp,
            r, Sp, Lt, Sp, D(2), Sp, Land, Sp,
            D(1), Sp, Slash, Sp, Open, D(2), Sp, Minus, Sp, r, Close,
            Sp, Lt, Sp, D(1), Sp, Plus, Sp, r, CloseBrace);
        Formula isLub = Seq(
            Operatorname, Grp(F.Id("IsLUB")), Open, diskSet, Comma, Sp, rStar, Close);
        Formula geodesicSpectrum = Seq(
            Operatorname, Grp(F.Id("L")), Underscore,
            Grp(Operatorname, Grp(F.Id("PSL")), Underscore, D(2), Open, Mathbb,
                Grp(F.Id("Z")), Close));
        Formula isLeast = Seq(
            Operatorname, Grp(F.Id("IsLeast")), Open, geodesicSpectrum,
            Comma, Sp, ellPhi, Close);
        Formula mayer = new Formula.Subscript(
            Seq(Operatorname, Grp(F.Id("M"))), w);
        Formula psiN = new Formula.Subscript(Psi, n);
        Formula mayerExact = Seq(
            Forall, Sp, w, Sp, InMacro, Sp, naturals, Comma, Sp,
            f, Colon, Sp, reals, Sp, To, Sp, reals, Comma, Sp,
            x, Sp, InMacro, Sp, reals, Comma, Sp,
            mayer, Open, f, Close, Open, x, Close, Sp, Eq, Sp,
            Sum, Underscore, Grp(n, Sp, Ge, Sp, D(1)), Sp,
            new Formula.Power(Seq(psiN, Open, x, Close), Seq(D(2), w)), Sp,
            f, Open, psiN, Open, x, Close, Close);

        return Disp(Seq(
            Exists, Sp, rStar, Comma, Sp, xStar, Comma, Sp, ellPhi,
            Sp, InMacro, Sp, reals, Comma, Sp,
            isLub, Sp, Land, Sp,
            rStar, Sp, Eq, Sp, Varphi, Sp, Land, Sp,
            xStar, Sp, Eq, Sp, rStar, Sp, Minus, Sp, D(1), Sp, Land, Sp,
            xStar, Sp, Eq, Sp, new Formula.Power(Varphi, new Formula.Negate(D(1))), Sp,
            Land, Sp, psiAtX, Sp, Eq, Sp, xStar, Sp, Land, Sp,
            new Formula.Absolute(derivativeAtX), Sp, Eq, Sp,
            new Formula.Power(rStar, new Formula.Negate(D(2))), Sp, Land, Sp,
            isLeast, Sp, Land, Sp,
            Exp, Open, new Formula.Negate(ellPhi), Close, Sp, Eq, Sp,
            new Formula.Power(rStar, new Formula.Negate(D(4))), Sp, Land, Sp,
            Open, mayerExact, Close, Dot));
    }
}
