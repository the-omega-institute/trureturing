using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Regularity;

internal sealed class ScaleSmoothnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A derivative relation across a scale of real normed spaces gives smooth paths on a closed interval.",
        H("Smoothness Across Normed-Space Grades"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cont-diff-on-scale-of-has-deriv-within-at"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Regularity/ScaleSmoothness."
                    + "cont_diff_on_scale_of_has_deriv_within_at"),
                H("Smoothness from derivatives at a shifted grade"),
                StatementSource.FromAuthor(SmoothnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be any family of types indexed by the natural numbers. For every "
                        + "grade m, give E(m) a normed additive commutative group structure and a "
                        + "compatible real normed vector space structure. Let r be any natural "
                        + "number, including zero, and let T be any positive real number. For "
                        + "every m, choose a path u(m) from the real line to E(m) and a map F(m) "
                        + "from E(m+r) to E(m). The products in the formula denote these families "
                        + "of functions, with the indicated domain and codomain at each grade.")),
                    Paragraph(Text(
                        "Assume F(m) is infinitely continuously differentiable over the reals "
                        + "for every natural grade m. Assume also that for every natural m and "
                        + "every real t in the closed interval [0,T], the derivative of u(m) "
                        + "within [0,T] exists and equals F(m)(u(m+r)(t)). Then u(m) is infinitely "
                        + "continuously differentiable within [0,T] for every natural m. Both "
                        + "the derivative hypothesis and the conclusion include t=0 and t=T; "
                        + "smoothness here is relative to the closed interval.")),
                    Paragraph(Text(
                        "The proof establishes each finite differentiability order "
                        + "simultaneously at all grades. At order zero, the derivative "
                        + "hypothesis gives continuity of each path on [0,T]. For the successor "
                        + "step, suppose every path has order n. In particular, u(m+r) has "
                        + "order n. Composing it with the smooth map F(m) gives an order n "
                        + "function into E(m). Since T is positive, derivatives within [0,T] "
                        + "are unique, so this composition equals the derivative within [0,T] "
                        + "of u(m). The successor criterion for continuous differentiability "
                        + "therefore gives order n+1 at grade m. This holds for all m, closing "
                        + "the induction. Having every finite order yields infinite "
                        + "continuous differentiability at each grade.")),
                    Paragraph(Text(
                        "No completeness or finite-dimensionality of the spaces is required. "
                        + "Continuity of the paths follows from the derivative hypothesis. "
                        + "The family needs no inclusions or norm comparisons between different "
                        + "grades: the maps F(m) provide the stated relations between them."))),
                DescribeRole.Theorem))));

    private static Formula SmoothnessFormula()
    {
        Formula natural = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula m = F.Id("m");
        Formula r = F.Id("r");
        Formula t = F.Id("t");
        Formula time = F.Id("T");
        Formula interval = F.Seq(F.OpenBracket, F.D(0), F.Comma, time, F.CloseBracket);
        Formula grade = F.Seq(m, F.Plus, r);
        Formula space = Call("E", m);
        Formula path = Call("u", m);
        Formula map = Call("F", m);
        Formula pathType = Family(m, natural, Arrow(real, space));
        Formula mapType = Family(m, natural, Arrow(Call("E", grade), space));
        Formula derivative = Call(
            "HasDerivWithinAt", path,
            Apply(map, Apply(Call("u", grade), t)), interval, t);

        return F.Disp(new Formula.Aligned([
            F.Seq(ForAll("E", Arrow(natural, F.Id("Type"))),
                F.OpenBracket, ForAll("m", natural),
                Call("NormedAddCommGroup", space), F.CloseBracket, F.Comma),
            F.Seq(F.Grp(), F.OpenBracket, ForAll("m", natural),
                Call("NormedSpace", real, space), F.CloseBracket, F.Comma),
            F.Seq(ForAll("r", natural), ForAll("T", real),
                F.D(0), F.Lt, time, F.Sp, F.Rightarrow),
            F.Seq(ForAll("u", pathType), ForAll("F", mapType)),
            F.Seq(F.Open, ForAll("m", natural),
                Call("ContDiff", real, F.Infty, map), F.Close, F.Sp, F.Rightarrow),
            F.Seq(F.Open, ForAll("m", natural), ForAll("t", real),
                t, F.InMacro, interval, F.Sp, F.Rightarrow, F.Sp,
                derivative, F.Close, F.Sp, F.Rightarrow),
            F.Seq(ForAll("m", natural),
                Call("ContDiffOn", real, F.Infty, path, interval), F.Dot),
        ]));
    }

    private static Formula ForAll(string name, Formula type) =>
        F.Seq(F.Forall, F.Sp, F.Id(name), F.Sp, F.Colon, F.Sp, type, F.Comma, F.Sp);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        F.Seq(domain, F.Sp, F.To, F.Sp, codomain);

    private static Formula Family(Formula index, Formula domain, Formula type) =>
        F.Seq(F.Prod, F.Underscore, F.Grp(index, F.InMacro, domain),
            F.Open, type, F.Close);

    private static Formula Apply(Formula function, Formula argument) =>
        F.Seq(function, F.Open, argument, F.Close);

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
