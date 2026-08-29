using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class BarycenterDefectDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completion barycenter and anti-coordinate separate center from mirror displacement.",
        H("Barycenter Defect Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("barycenter-and-anti-coordinate-separate-mirror-pairs"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/BarycenterDefectDecomposition."
                        + "barycenter_defect_decomposition"),
                H("Barycenter and anti-coordinate separate mirror pairs"),
                StatementSource.FromAuthor(BarycenterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The barycenter and anti-coordinate are constructed from the frozen "
                            + "conjugate-reflection map. Vanishing anti-coordinate on every "
                            + "nontrivial zero is exactly the critical-line condition.")),
                    Paragraph(Text(
                        "For every real nonzero displacement and real height, the explicitly "
                            + "constructed symmetric pair has a common completion center, "
                            + "opposite anti-coordinates, and is exchanged by the mirror map. "
                            + "Its canonical two-point mirror orbit has radius equal to the "
                            + "absolute displacement."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Zeros/Symmetry/ZeroSymmetryAction")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula BarycenterFormula()
    {
        Formula rho = Rho;
        Formula delta = Delta;
        Formula gamma = Gamma;
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula critical = Seq(Operatorname, Grp(F.Id("criticalAbscissa")));
        Formula mirrorRho = Call("mirror", rho);
        Formula barycenter = Call("completionBarycenter", rho);
        Formula anti = Call("antiCoordinate", rho);
        Formula right = F.Id("r");
        Formula left = Ell;
        Formula center = F.Id("c");
        Formula rightPoint = Seq(
            Open, critical, Plus, delta, Close, Plus, F.Id("i"), gamma);
        Formula leftPoint = Seq(
            Open, critical, Minus, delta, Close, Plus, F.Id("i"), gamma);
        Formula centerPoint = Seq(critical, Plus, F.Id("i"), gamma);
        Formula criticalZeros = Seq(
            Forall, Sp, rho, InMacro, Sp, complex, Comma, Sp,
            Call("IsNontrivialZero", rho), Sp, Rightarrow, Sp,
            Re, Open, rho, Close, Sp, Eq, Sp, critical);
        Formula zeroAnti = Seq(
            Forall, Sp, rho, InMacro, Sp, complex, Comma, Sp,
            Call("IsNontrivialZero", rho), Sp, Rightarrow, Sp,
            Call("antiCoordinate", rho), Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, rho, InMacro, Sp, complex, Comma, Sp,
            barycenter, Sp, Colon, Eq, Sp,
            Frac, Grp(rho, Plus, mirrorRho), Grp(D(2)), Comma, Quad, Sp,
            anti, Sp, Colon, Eq, Sp,
            Frac, Grp(rho, Minus, mirrorRho), Grp(D(2)), Comma,
            RowBreak, Grp(),
            Open, Open, criticalZeros, Close, Sp, Leftrightarrow, Sp,
            Open, zeroAnti, Close, Close, Sp, Land,
            RowBreak, Grp(),
            Forall, Sp, delta, Comma, Sp, gamma, InMacro, Sp, real, Comma, Sp,
            delta, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Operatorname, Grp(F.Id("let")), Sp,
            right, Colon, Sp, complex, Sp, Colon, Eq, Sp, rightPoint, Semi, Sp,
            Operatorname, Grp(F.Id("let")), Sp,
            left, Colon, Sp, complex, Sp, Colon, Eq, Sp, leftPoint, Semi,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            center, Colon, Sp, complex, Sp, Colon, Eq, Sp, centerPoint, Semi, Sp,
            Call("completionBarycenter", right), Sp, Eq, Sp, center, Sp, Land, Sp,
            Call("completionBarycenter", left), Sp, Eq, Sp, center, Sp, Land,
            RowBreak, Grp(),
            Call("antiCoordinate", right), Sp, Eq, Sp, delta, Sp, Land, Sp,
            Call("antiCoordinate", left), Sp, Eq, Sp, Minus, delta, Sp, Land, Sp,
            Call("mirror", right), Sp, Eq, Sp, left, Sp, Land, Sp,
            Call("mirror", left), Sp, Eq, Sp, right, Sp, Land,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("card")), OpenBrace,
            right, Comma, Sp, Call("mirror", right), CloseBrace,
            Sp, Eq, Sp, D(2), Sp, Land, Sp,
            new Formula.Norm(Seq(right, Minus, center)), Sp, Eq, Sp,
            new Formula.Absolute(delta), Sp, Land, Sp,
            new Formula.Norm(Seq(left, Minus, center)), Sp, Eq, Sp,
            new Formula.Absolute(delta), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
