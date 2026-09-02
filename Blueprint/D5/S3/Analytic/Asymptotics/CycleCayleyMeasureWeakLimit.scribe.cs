using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class CycleCayleyMeasureWeakLimitDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite cyclic Cayley measures converge weakly to the standard Cauchy law.",
        H("Cyclic Cayley Measure Weak Limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cycle-cayley-measure-weak-limit"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Asymptotics/CycleCayleyMeasureWeakLimit."
                    + "cycle_cayley_measure_weak_limit"),
                H("The cyclic Cayley measures converge to the standard Cauchy law"),
                StatementSource.FromAuthor(WeakLimitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For n in the natural numbers, the cycle size is n+2. The measure is "
                        + "constructed by putting the uniform probability mass on Fin(n+1), "
                        + "then mapping index j to -cot(pi(j+1)/(n+2)). Thus every cycle size "
                        + "K at least two occurs exactly once, with all K-1 nontrivial phases "
                        + "having mass 1/(K-1).")),
                    Paragraph(Text(
                        "The proof computes each lower-interval mass exactly. The Cayley order "
                        + "equivalence turns the event into a finite grid count, whose size is "
                        + "a floor. Pinned Mathlib's floor-ratio limit makes these masses tend "
                        + "to the standard Cauchy distribution function.")),
                    Paragraph(Text(
                        "Convergence on the pi-system of half-open intervals is then promoted by "
                        + "Mathlib's probability-measure convergence theorem to Tendsto in the "
                        + "weak topology. The target cauchyMeasure(0,1) is the probability law "
                        + "with density 1/(pi(1+h^2)); no affine shift or scale is introduced."))),
                DescribeRole.Theorem))));

    private static Formula WeakLimitFormula()
    {
        Formula n = F.Id("n");
        Formula j = F.Id("j");
        Formula naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula empirical = F.Id("cycleCayleyEmpiricalMeasure");
        Formula finSize = F.Seq(n, F.Sp, F.Plus, F.Sp, F.D(1));
        Formula cycleSize = F.Seq(n, F.Sp, F.Plus, F.Sp, F.D(2));
        Formula angle = new Formula.Fraction(
            F.Seq(F.Pi, F.Sp, F.Open, j, F.Sp, F.Plus, F.Sp, F.D(1), F.Close),
            cycleSize);
        Formula cayleyPoint = F.Seq(F.Minus, Call("cot", angle));
        Formula phaseLaw = Call("uniformOfFintype", Call("Fin", finSize));
        Formula pushedLaw = Call("map",
            F.Seq(j, F.Sp, F.Mapsto, F.Sp, cayleyPoint), phaseLaw);
        Formula measureDefinition = Call("asProbabilityMeasure",
            Call("toMeasure", pushedLaw));
        Formula probabilityMeasures = Call("ProbabilityMeasure", reals);
        Formula target = Call("cauchyMeasure", reals, F.D(0), F.D(1));

        return F.Disp(F.Seq(
            F.Begin, F.Grp(F.Id("gathered")),
            empirical, F.Colon, F.Sp, naturals, F.Sp, F.To, F.Sp,
            probabilityMeasures, F.Comma, F.RowBreak, F.Grp(),
            F.Forall, F.Sp, n, F.Sp, F.InMacro, F.Sp, naturals, F.Comma, F.Quad, F.Sp,
            new Formula.Apply(empirical, [n]), F.Sp, F.Colon, F.Eq, F.Sp,
            measureDefinition, F.Comma, F.RowBreak, F.Grp(),
            Call("Tendsto", empirical, Call("atTop", naturals), Call("nhds", target)),
            F.Dot,
            F.End, F.Grp(F.Id("gathered"))));
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
        return F.Seq(pieces.ToArray());
    }
}
