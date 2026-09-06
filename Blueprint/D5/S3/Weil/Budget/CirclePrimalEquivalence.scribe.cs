using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class CirclePrimalEquivalenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The budgeted circle primal is the attained maximal normalized-Haar floor, "
            + "equivalently the attained maximal coefficient in a positive residual decomposition.",
        H("Circle Primal Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("circle-primal-equivalence"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Budget/CirclePrimalEquivalence."
                        + "circle_primal_equivalence"),
                H("The circle primal and residual programs have the same attained maximum"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The continuous moment family is normalized so that its Haar integral "
                            + "is twice a times the designated center evaluation. The positivity "
                            + "assumption on a is required when dividing the primal identity by "
                            + "twice a; without it Lean's totalized division would collapse that "
                            + "quotient to zero.")),
                    Paragraph(Text(
                        "The existing full-circle attainment theorem supplies a feasible measure "
                            + "and a globally greatest dominated Haar coefficient. Taking the "
                            + "measure difference constructs a positive residual and gives the "
                            + "displayed budget and moment equations.")),
                    Paragraph(Text(
                        "Conversely, adding any positive residual to the Haar component constructs "
                            + "a feasible measure dominating that coefficient. Thus the measure "
                            + "floor maximum and the explicit residual maximum have exactly the "
                            + "same feasible coefficients and the same attained optimizer."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a");
        Formula alpha = Alpha;
        Formula sigma = SigmaLower;
        Formula measure = Mu;
        Formula budget = F.Id("C");
        Formula primal = F.Id("Lambda");
        Formula moments = F.Id("Gamma");
        Formula target = F.Id("W");
        Formula center = F.Id("c");
        Formula index = F.Id("i");
        Formula haar = Seq(F.Id("m"), Underscore, Grp(F.Id("T")));
        Formula feasibleSet = Seq(Mathcal, Grp(F.Id("M")), Underscore, Grp(F.Id("C")));
        Formula floor = Call("hfloor", measure);
        Formula residualConditions = Seq(
            alpha, Plus, Call("mass", sigma), Sp, Leq, Sp, budget, Comma, Sp,
            Forall, Sp, index, Comma, Sp,
            D(2), a, alpha, Call("apply", center, index), Plus,
            Int, Sp, Call("apply", moments, index), Sp, Mathrm, Grp(F.Id("d")), sigma,
            Sp, Eq, Sp, Call("apply", target, index));

        return Disp(new Formula.Aligned([
            Seq(a, Sp, Gt, Sp, D(0), Comma, Sp,
                Forall, Sp, index, Comma, Sp,
                Int, Sp, Call("apply", moments, index), Sp,
                Mathrm, Grp(F.Id("d")), haar, Sp, Eq, Sp,
                D(2), a, Call("apply", center, index), Comma),
            Seq(feasibleSet, Sp, Neq, Sp, Emptyset, Sp, Rightarrow, Sp,
                Exists, Sp, measure, Comma, alpha, Comma, Sp,
                measure, InMacro, feasibleSet, Sp, Land, Sp,
                alpha, Sp, haar, Sp, Leq, Sp, measure, Comma),
            Seq(primal, Sp, Eq, Sp, D(2), a,
                Max, Underscore, Grp(measure, InMacro, feasibleSet), floor,
                Sp, Eq, Sp, D(2), a, alpha, Comma),
            Seq(Frac, Grp(primal), Grp(D(2), a), Sp, Eq, Sp, alpha,
                Sp, Eq, Sp, Max, Underscore, Grp(alpha, Geq, D(0)),
                Left, OpenBrace, alpha, Colon, Sp, Exists, Sp, sigma, Geq, D(0), Comma, Sp,
                residualConditions, Right, CloseBrace, Dot),
        ]));
    }
}
