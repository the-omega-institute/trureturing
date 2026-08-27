using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PredictionDepth;

internal sealed class FiniteTimeObserverMonotonicityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Longer Heisenberg observation enlarges the visible span and shrinks its orthogonal residual.",
        H("Finite-Time Observer Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-time-observer-monotonicity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PredictionDepth/FiniteTimeObserverMonotonicity."
                        + "finite_time_observer_monotonicity"),
                H("Visible spaces grow while orthogonal residuals shrink"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the canonical real Hermitian matrix space. At horizon n, "
                            + "the visible space is constructed as the real span of the identity "
                            + "and every effect after a Heisenberg iterate t with t < n.")),
                    Paragraph(Text(
                        "Each generator at horizon n is also a generator at horizon n+1, so the "
                            + "first public clause includes the smaller visible span in the larger "
                            + "one. Orthogonal complementation reverses that inclusion for the "
                            + "second public clause.")),
                    Paragraph(Text(
                        "The theorem uses the source's finite-time test directly and introduces no "
                            + "parallel visible-space or residual definition."))),
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

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Visible(
        Formula real,
        Formula dimension,
        Formula count,
        Formula horizon,
        Formula heisenberg,
        Formula effects)
    {
        Formula effect = F.Id("E");
        Formula time = F.Id("t");
        Formula index = F.Id("i");
        Formula iterate = Seq(
            Apply(Seq(heisenberg, Caret, Grp(time)),
                Apply(effects, index)));
        Formula generated = Seq(
            OpenBrace, effect, Sp, Mid, Sp,
            Exists, Sp, time, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            index, InMacro, Sp, Call("Fin", Seq(count, Plus, D(1))), Comma, Sp,
            time, Sp, Lt, Sp, horizon, Sp, Land, Sp,
            effect, Sp, Eq, Sp, iterate, CloseBrace);
        return Call("span", real, Seq(
            Call("insert", Call("identityHermitian", dimension), generated)));
    }

    private static Formula TheoremFormula()
    {
        Formula natural = F.Id("Nat");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula dimension = F.Id("d");
        Formula count = F.Id("r");
        Formula heisenberg = F.Id("H");
        Formula effects = F.Id("E");
        Formula horizon = F.Id("n");
        Formula carrier = Call("HermitianSpace", dimension);
        Formula visible = Visible(real, dimension, count, horizon, heisenberg, effects);
        Formula next = Visible(
            real, dimension, count, Seq(horizon, Plus, D(1)), heisenberg, effects);

        return Disp(Seq(
            Forall, Sp, dimension, InMacro, Sp, natural, Comma, Sp,
            count, InMacro, Sp, natural, Comma, Sp,
            heisenberg, Colon, Sp, Call("LinearMap", real, carrier, carrier), Comma, Sp,
            effects, Colon, Sp, Arrow(Call("Fin", Seq(count, Plus, D(1))), carrier),
            Rightarrow, RowBreak, Grp(),
            Forall, Sp, horizon, InMacro, Sp, natural, Comma, Sp,
            visible, Sp, Subseteq, Sp, next, Sp, Land, Sp,
            Call("orthogonal", next), Sp, Subseteq, Sp,
            Call("orthogonal", visible), Dot));
    }
}
