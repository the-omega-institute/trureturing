using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class RecurrentOrbitAgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A recurrent real flow orbit admits no continuous clock equal to elapsed time.",
        H("Recurrent Orbits Have No Continuous Age"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-recurrent-orbit-has-no-continuous-age"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/RecurrentOrbitAge."
                        + "recurrent_orbit_has_no_continuous_age"),
                H("A recurrent orbit has no continuous age"),
                StatementSource.FromAuthor(RecurrentOrbitAgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Phi be a continuous real flow on a topological space X. "
                            + "Assume a sequence of times tends to positive infinity while "
                            + "the corresponding orbit points converge back to x0.")),
                    Paragraph(Text(
                        "Continuity would make the proposed age values along those orbit "
                            + "points converge to age(x0). The clock identity applies at all "
                            + "sufficiently large sequence times, so the same values tend to "
                            + "positive infinity. The two limits are incompatible.")),
                    Paragraph(Text(
                        "Loogle supplied Continuous.tendsto, Tendsto.eventually, and "
                            + "Tendsto.congr'. LeanSearch supplied the exact contradiction "
                            + "theorem not_tendsto_atTop_of_tendsto_nhds; each supporting "
                            + "result is imported and applied. No full-statement library or "
                            + "repository match was found. The identity flow on Unit with "
                            + "natural-number real times is a checked recurrence witness."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var separated = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                separated.Add(Comma);
                separated.Add(Sp);
            }

            separated.Add(arguments[index]);
        }

        return Seq(function, Open, Seq([.. separated]), Close);
    }

    private static Formula RecurrentOrbitAgeFormula()
    {
        Formula x = F.Id("X");
        Formula x0 = Seq(F.Id("x"), Underscore, D(0));
        Formula time = F.Id("t");
        Formula index = F.Id("n");
        Formula times = F.Id("times");
        Formula age = F.Id("age");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula atTop = OperatornameThen("atTop");
        Formula indexedTime = Seq(times, Underscore, Grp(index));
        Formula orbitPoint = Apply(Seq(Phi, Underscore, Grp(indexedTime)), x0);
        Formula flowPoint = Apply(Seq(Phi, Underscore, Grp(time)), x0);

        Formula Tendsto(Formula function, Formula source, Formula target) =>
            Apply(OperatornameThen("Tendsto"), function, source, target);

        Formula nhds(Formula point) => Apply(OperatornameThen("nhds"), point);

        return Disp(Seq(
            Forall, Sp, x, Comma, Sp,
            OpenBracket, OperatornameThen("TopologicalSpace"), Open, x, Close,
            CloseBracket, Comma, Esc,
            Phi, Colon, Sp, Apply(OperatornameThen("Flow"), real, x), Comma, Sp,
            x0, Colon, Sp, x, Comma, Sp,
            times, Colon, Sp, naturals, Sp, To, Sp, real, Comma, Esc,
            Open,
            Tendsto(times, atTop, atTop), Sp, Land, Sp,
            Tendsto(Seq(Open, index, Sp, Mapsto, Sp, orbitPoint, Close),
                atTop, nhds(x0)),
            Close, Sp, Rightarrow, Esc,
            Neg, Exists, Sp, age, Colon, Sp, x, Sp, To, Sp, real, Comma, Esc,
            Apply(OperatornameThen("Continuous"), age), Sp, Land, Sp,
            Forall, Sp, time, InMacro, Sp, real, Comma, Sp,
            D(0), Sp, Leq, Sp, time, Sp, Rightarrow, Sp,
            Apply(age, flowPoint), Sp, Eq, Sp, time, Dot));
    }

    private static Formula OperatornameThen(string name) =>
        Seq(Operatorname, Grp(F.Id(name)));
}
