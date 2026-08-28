using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Dilation;

internal sealed class GoldenUnitZetaRegulatorCircleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden-unit lattice zeta is periodic and descends to its regulator circle.",
        H("Golden Unit Zeta on the Regulator Circle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-unit-zeta-regulator-circle"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Dilation/GoldenUnitZetaRegulatorCircle."
                        + "golden_unit_zeta_regulator_circle"),
                H("The golden-unit zeta descends through the regulator period"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here goldenUnitZeta is the named sum over the nonzero coefficient "
                            + "lattice Z x Z for Z[phi]. Its named anisotropic form uses the "
                            + "two concrete embeddings a+b phi and a+b psi.")),
                    Paragraph(Text(
                        "The first conjunct is the literal shift equality by twice log(phi). "
                            + "Its proof directly reuses the already-frozen lattice "
                            + "reindexing theorem.")),
                    Paragraph(Text(
                        "The second conjunct evaluates the named quotient lift on the class "
                            + "of eta in AddCircle(2 log(phi)). Mathlib's Periodic.lift_coe "
                            + "identifies that pullback with the original zeta, so the "
                            + "quotient carrier appears in Lean rather than only in prose."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Dilation/GoldenUnitZetaPeriodicity")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula complexes = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        Formula s = F.Id("s");
        Formula eta = F.Id("eta");
        Formula period = F.Seq(
            F.D(2), F.Sp, F.Cdot, F.Sp, Call("log", F.Varphi));
        Formula circle = Call("AddCircle", period);
        Formula etaClass = F.Seq(
            F.OpenBracket, eta, F.CloseBracket,
            F.Underscore, F.Grp(circle));

        Formula periodicity = F.Seq(
            F.Forall, F.Sp, s, F.Sp, F.InMacro, F.Sp, complexes,
            F.Comma, F.Sp,
            F.Forall, F.Sp, eta, F.Sp, F.InMacro, F.Sp, reals,
            F.Comma, F.Sp,
            Call("goldenUnitZeta", s,
                F.Seq(eta, F.Sp, F.Plus, F.Sp, period)),
            F.Sp, F.Eq, F.Sp, Call("goldenUnitZeta", s, eta));
        Formula quotientPullback = F.Seq(
            F.Forall, F.Sp, s, F.Sp, F.InMacro, F.Sp, complexes,
            F.Comma, F.Sp,
            F.Forall, F.Sp, eta, F.Sp, F.InMacro, F.Sp, reals,
            F.Comma, F.Sp,
            Call("goldenUnitZetaOnRegulatorCircle", s, etaClass),
            F.Sp, F.Eq, F.Sp, Call("goldenUnitZeta", s, eta));

        return F.Disp(new Formula.Aligned([
            F.Seq(F.Open, periodicity, F.Close, F.Sp, F.Land),
            F.Seq(F.Open, quotientPullback, F.Close, F.Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq([.. pieces]);
    }
}
