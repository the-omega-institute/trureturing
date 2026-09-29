using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class CrossoverUniqueMinimaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit crossover costs have unique interior global minima, with the minimum "
            + "for denominator power two strictly preceding that for power one.",
        H("Unique Ordered Minima of the Crossover Costs"),
        Blocks(
            Paragraph(Text(
                "All variables are real. Set g(z)=1+(z squared-sqrt(z to the fourth+4))/2, "
                    + "A(z)=c+(h-z) squared, D(z)=1-gamma g(z), and F_j(z)=A(z)/(D(z) raised to "
                    + "the power j), for j=1,2. The feasible set S consists of all z with "
                    + "0 <= z <= h and D(z)>0.")),
            Describe.Lean(
                DescribeId.Create("unique-ordered-minima"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/StationaryPreparation/CrossoverUniqueMinima.result"),
                H("Strict global minima on the full feasible set"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write r=h-z, v=z squared/sqrt(z to the fourth+4), "
                            + "p=z(1-v), and q=(1-v)(1-2v-2v squared). Then g'=p and p'=q. "
                            + "For H_t=g+t A p/r, where 1/2 <= t <= 1, differentiation gives "
                            + "H_t'=(1-t)p+t[c p/r squared+(r+c/r)q].")),
                    Paragraph(Text(
                        "The expression in brackets is strictly positive on 0<z<h. "
                            + "After division by a positive factor, the assertion is "
                            + "z+r(1+r squared/c)(1-2v-2v squared)>0. For z<=4/5, "
                            + "v<=8/25 makes the final factor positive. On the next three "
                            + "intervals, bounded above by 1, 6/5, and h respectively, "
                            + "the negative part K=2v+2v squared-1 is bounded above by "
                            + "1/3, 1, and 3. The corresponding r bounds are 3/4, 11/20, "
                            + "and 7/20; together with c>12/5 they give r(1+r squared/c)K<z.")),
                    Paragraph(Text(
                        "The continuous expression r(g-1/gamma)+t A p is negative at zero "
                            + "and positive at h, so it vanishes at an interior point a. "
                            + "There gamma H_t(a)=1, and H_t(a)>g(a) implies D(a)>0. "
                            + "Strict increase of H_t gives uniqueness of its root. "
                            + "Since H_1>H_(1/2) in the interior, their roots satisfy z2<z1.")),
                    Paragraph(Text(
                        "For j=1,2 the derivative of F_j is "
                            + "2r D to the power -(j+1) times (gamma H_(j/2)-1). "
                            + "It is negative below its root and positive above. "
                            + "Strict increase of g ensures positivity of D on every "
                            + "comparison interval ending at a feasible point. Continuity "
                            + "then includes zero and h whenever those endpoints are feasible. "
                            + "Thus each root has strictly smaller cost than every other "
                            + "point of S, which also proves uniqueness.")),
                    Paragraph(Text(
                        "This statement concerns the two scalar costs. Dependence of the "
                            + "minima on gamma, convexity of a Pareto curve, asymptotic "
                            + "expansions, and attainment by physical preparations are "
                            + "separate assertions."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula c = F.Id("c"), h = F.Id("h"), z = F.Id("z");
        Formula z1 = Seq(z, Underscore, D(1)), z2 = Seq(z, Underscore, D(2));
        return Disp(Seq(
            Forall, Sp, c, Comma, h, Comma, GammaLower, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            Open, Frac, Grp(D(1, 2)), Grp(D(5)), Lt, c, Land, Sp, D(0), Lt, h, Lt,
            Frac, Grp(D(3, 1)), Grp(D(2, 0)), Land, Sp, D(0), Lt, GammaLower, Close, Implies, Sp, Esc,
            Exists, Sp, z2, Comma, z1, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            D(0), Lt, z2, Lt, z1, Lt, h, Land, Sp, z2, InMacro, Sp, F.Id("S"), Land, Sp,
            z1, InMacro, Sp, F.Id("S"), Land, Sp, Esc,
            StrictMinimum(2, z2, z), Land, Sp, Esc, StrictMinimum(1, z1, z)));
    }

    private static Formula StrictMinimum(byte j, Formula a, Formula z) => Seq(
        Open, Forall, Sp, z, InMacro, Sp, F.Id("S"), Comma, Sp, z, Neq, Sp, a, Implies, Sp,
        Cost(j, a), Lt, Cost(j, z), Close);

    private static Formula Cost(byte j, Formula z) => Seq(F.Id("F"), Underscore, D(j), Open, z, Close);
}
