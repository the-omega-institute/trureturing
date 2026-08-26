using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Boundary;

internal sealed class GoldenDisplacementConvergenceRegionOpenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden displacement convergence region is open in its real parameter plane.",
        H("Golden Displacement Convergence Region Is Open"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-displacement-convergence-region-is-open"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Boundary/GoldenDisplacementConvergenceRegionOpen."
                        + "golden_displacement_convergence_region_open"),
                H("The golden displacement convergence region is open"),
                StatementSource.FromAuthor(RegionOpenFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The summability characterization identifies the parameter region with "
                            + "the intersection of two strict affine half-planes.")),
                    Paragraph(Text(
                        "Each affine expression is continuous on the product parameter space, "
                            + "so the strict inequality defines an open set. Their intersection is "
                            + "therefore open. This records the topological property separately "
                            + "from the already established convexity statement.")),
                    Paragraph(Text(
                        "Repository searches found no existing IsOpen declaration for this region. "
                            + "Pinned Mathlib supplies isOpen_lt and continuity of the affine "
                            + "maps; "
                            + "the Lean proof combines those facts with the repository's exact "
                            + "two-constraint summability theorem."))),
                DescribeRole.Theorem))));

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
        return F.Seq(pieces.ToArray());
    }

    private static Formula PairProjection(string variable, byte index) =>
        F.Seq(F.Id(variable), F.Dot, F.D(index));

    private static Formula DTerm(Formula s, Formula w) =>
        Call("dTerm", s, w);

    private static Formula Summable(Formula term) =>
        Call("Summable", term);

    private static Formula RegionOpenFormula()
    {
        Formula p = F.Id("p");
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula product = F.Seq(real, F.Sp, F.Times, F.Sp, real);
        Formula region = F.Seq(
            F.OpenBrace, p, F.Colon, F.Sp, product, F.Sp, F.Mid, F.Sp,
            Summable(DTerm(PairProjection("p", 1), PairProjection("p", 2))),
            F.CloseBrace);

        return F.Disp(Call("IsOpen", region));
    }
}
