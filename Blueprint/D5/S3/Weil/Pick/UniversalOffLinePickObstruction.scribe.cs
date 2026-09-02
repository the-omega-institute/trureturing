using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class UniversalOffLinePickObstructionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/Pick/UniversalOffLinePickObstruction.universal_off_line_pick_obstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every right-side zero image gives the same determinant-minus-one "
            + "two-point Pick matrix, independently of its ordinate.",
        H("Universal Off-Line Pick Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("universal-off-line-pick-obstruction"),
                DeclarationHandle.Create(Declaration),
                H("The two-point obstruction is independent of the ordinate"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source point rho is constructed from its real coordinate sigma "
                            + "and ordinate gamma, and its disk image is one minus the "
                            + "reciprocal of rho.")),
                    Paragraph(Text(
                        "When the arithmetic Schur object vanishes at the origin and has unit "
                            + "contact at that image, the standard Pick kernel gives the fixed "
                            + "matrix with rows (1,1) and (1,0). Its determinant is minus one, "
                            + "with gamma publicly bound but absent from the resulting constants."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula schur = F.Id("s");
        Formula sigma = F.Id("sigma");
        Formula gamma = F.Id("gamma");
        Formula rho = F.Id("rho");
        Formula zrho = F.Id("zrho");
        Formula z = F.Id("z");
        Formula w = F.Id("w");
        Formula index = F.Id("i");
        Formula kernel = F.Id("K");
        Formula points = F.Id("p");
        Formula relation = F.Id("R");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));

        Formula rhoDefinition = Seq(sigma, Plus, F.Id("i"), Cdot, Sp, gamma);
        Formula zrhoDefinition = Seq(
            D(1), Minus, new Formula.Fraction(D(1), rho));
        Formula contactPoint = Seq(
            D(1), Minus, new Formula.Fraction(D(1), Grp(rhoDefinition)));
        Formula kernelBody = new Formula.Fraction(
            Seq(D(1), Minus, Call("s", z), Times, Conjugate(Call("s", w))),
            Seq(D(1), Minus, z, Times, Conjugate(w)));
        Formula kernelDefinition = Seq(
            Open, z, Comma, Sp, w, Sp, Mapsto, Sp, kernelBody, Close);
        Formula relationDefinition = Seq(
            Open, index, Comma, Sp, F.Id("j"), Sp, Mapsto, Sp,
            Call("K", Call("p", index), Call("p", F.Id("j"))), Close);

        return Disp(Seq(
            Forall, Sp, schur, Colon, Sp, complex, Sp, To, Sp, complex, Comma, Sp,
            sigma, Comma, Sp, gamma, Sp, InMacro, Sp, real, Comma, Sp,
            Open, new Formula.Fraction(D(1), D(2)), Sp, Lt, Sp, sigma, Sp, Land, Sp,
            Call("s", D(0)), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Call("s", contactPoint), Sp, Eq, Sp, D(1), Close, Sp,
            Rightarrow, Sp, Operatorname, Grp(F.Id("let")), Open,
            rho, Sp, Colon, Eq, Sp, rhoDefinition, Comma, Sp,
            zrho, Sp, Colon, Eq, Sp, zrhoDefinition, Comma, Sp,
            kernel, Sp, Colon, Eq, Sp, kernelDefinition, Comma, Sp,
            points, Sp, Colon, Eq, Sp, Call("vector", D(0), zrho), Comma, Sp,
            relation, Sp, Colon, Eq, Sp, relationDefinition, Close, SemiSpace,
            new Formula.Norm(zrho), Sp, Lt, Sp, D(1), Sp, Land, Sp,
            relation, Sp, Eq, Sp, Call("matrix", D(1), D(1), D(1), D(0)), Sp, Land, Sp,
            Call("det", relation), Sp, Eq, Sp, Minus, D(1), Dot));
    }

    private static Formula Conjugate(Formula value) => Seq(Overline, Grp(value));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
