using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Boundary;

internal sealed class GoldenDisplacementConvergenceBoundaryDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The boundary of golden displacement convergence is exactly the graph of its "
        + "critical-boundary function.",
        H("Golden Displacement Convergence Boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-displacement-convergence-boundary"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Boundary/GoldenDisplacementConvergenceBoundary."
                    + "golden_displacement_convergence_boundary"),
                H("The convergence boundary is the critical graph"),
                StatementSource.FromAuthor(BoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The binding-constraint theorem identifies summability with the strict "
                        + "epigraph of the critical-boundary function. Continuity of the maximum "
                        + "of its two affine branches puts every frontier point on the graph.")),
                    Paragraph(Text(
                        "The reverse inclusion is substantive. At a graph point (s,w), every "
                        + "positive epsilon gives the convergent point (s,w+epsilon/2) inside "
                        + "the strict epigraph, while the graph point itself lies in its "
                        + "complement. Thus both sides accumulate at the point.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies only the applicable frontier-to-equality "
                        + "inclusion. This theorem adds the vertical perturbation required for "
                        + "equality and makes no separate closure or interior claim."))),
                DescribeRole.Theorem))));

    private static Formula BoundaryFormula()
    {
        Formula point = F.Id("p");
        Formula first = F.Seq(point, F.Dot, F.D(1));
        Formula second = F.Seq(point, F.Dot, F.D(2));
        Formula reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula domain = F.Seq(reals, F.Sp, F.Times, F.Sp, reals);
        Formula summable = Call("Summable", Call("dTerm", first, second));
        Formula convergenceRegion = SetOf(point, domain, summable);
        Formula criticalGraph = SetOf(
            point,
            domain,
            F.Seq(
                Call("goldenDisplacementCriticalBoundary", first),
                F.Sp, F.Eq, F.Sp, second));

        return F.Disp(F.Seq(
            Call("frontier", convergenceRegion),
            F.Sp, F.Eq, F.Sp, criticalGraph, F.Dot));
    }

    private static Formula SetOf(Formula point, Formula domain, Formula predicate) =>
        F.Seq(
            F.Left, F.OpenBrace, point, F.Sp, F.Colon, F.Sp, domain,
            F.Sp, F.Mid, F.Sp, predicate, F.Right, F.CloseBrace);

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
}
