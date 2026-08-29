using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class GroundStateZeroLocalizationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Vague residual-spectrum convergence forces eventual ground-transform zeros near "
            + "each canonical zero ordinate.",
        H("Ground-State Zero Localization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ground-state-zero-localization"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Budget/GroundStateZeroLocalization."
                        + "ground_state_zero_localization"),
                H("Residual supports localize ground-transform zeros"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The target is the canonical multiplicity-weighted real-ordinate "
                            + "measure constructed from ZeroData. Vague convergence is exposed "
                            + "publicly through convergence against every nonnegative compactly "
                            + "supported continuous real test.")),
                    Paragraph(Text(
                        "A smooth bump supported in the chosen open neighborhood equals one at "
                            + "the selected ordinate. Its target integral is positive because "
                            + "that ordinate has positive canonical multiplicity.")),
                    Paragraph(Text(
                        "Eventually the residual bump integral is positive, so the neighborhood "
                            + "meets the residual support. The public support inclusion then "
                            + "places a ground-transform zero there. The argument works for any "
                            + "open neighborhood, so a separate isolation premise is unnecessary."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

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

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula zeros = F.Id("Z");
        Formula zeroIndex = F.Id("n");
        Formula residual = F.Id("mu");
        Formula transform = F.Id("F");
        Formula neighborhood = F.Id("U");
        Formula j = F.Id("j");
        Formula xi = F.Id("xi");
        Formula test = F.Id("phi");
        Formula target = Call("zeroCountingMeasure", zeros);
        Formula residualAtJ = Call("apply", residual, j);
        Formula transformAt = Call("apply", Call("apply", transform, j), xi);
        Formula zeroSet = new Formula.SetBuilder(
            Seq(transformAt, Sp, Eq, Sp, D(0)), xi, real);
        Formula supportInZeros = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("j", nat)],
            Seq(Call("support", residualAtJ), Sp, Subseteq, Sp, zeroSet));
        Formula ordinate = Call("im", Call("zero", zeros, zeroIndex));
        Formula testAt = Call("apply", test, xi);
        Formula testWeight = Call("ofReal", testAt);
        Formula residualIntegral = Call(
            "lintegral", residualAtJ,
            Lambda(Seq(xi, Colon, Sp, real), testWeight));
        Formula targetIntegral = Call(
            "lintegral", target,
            Lambda(Seq(xi, Colon, Sp, real), testWeight));
        Formula nonnegativeTest = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("xi", real)],
            Seq(D(0), Sp, Leq, Sp, testAt));
        Formula vague = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("phi", Seq(real, Sp, To, Sp, real))],
            Seq(
                Call("Continuous", test), Sp, Land, Sp,
                Call("HasCompactSupport", test), Sp, Land, Sp,
                Open, nonnegativeTest, Close, Sp, Rightarrow, Sp,
                Call(
                    "Tendsto",
                    Lambda(Seq(j, Colon, Sp, nat), residualIntegral),
                    Call("atTop"),
                    Call("nhds", targetIntegral))));
        Formula eventualConclusion = Call(
            "EventuallyAtTop",
            Lambda(
                Seq(j, Colon, Sp, nat),
                Call("Nonempty", Call("inter", zeroSet, neighborhood))));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp,
                zeros, Colon, Sp, Call("ZeroData"), Comma, Sp,
                zeroIndex, Colon, Sp, nat, Comma),
            Seq(residual, Colon, Sp, nat, Sp, To, Sp, Call("Measure", real),
                Comma, Sp, transform, Colon, Sp, nat, Sp, To, Sp,
                real, Sp, To, Sp, complex, Comma),
            Seq(neighborhood, Colon, Sp, Call("Set", real), Comma, Sp,
                Call("IsOpen", neighborhood), Sp, Land, Sp,
                Call("mem", ordinate, neighborhood), Sp, Land, Sp,
                supportInZeros, Sp, Land),
            Seq(vague, Sp, Rightarrow),
            Seq(eventualConclusion, Dot),
        ]));
    }
}
