using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class ContactZeroLocalizationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Vague convergence of finite contact spectra localizes an indexed positive atom "
            + "near every enumerated zero ordinate.",
        H("Contact-Zero Localization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("contact-zero-localization"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Budget/ContactZeroLocalization."
                        + "contact_zero_localization"),
                H("Finite contact spectra localize positive atoms"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The signed contact atoms are indexed directly. Their subtype records "
                            + "the transform-zero equation, and the residual measure is the "
                            + "corresponding finite positive Dirac sum.")),
                    Paragraph(Text(
                        "A compactly supported smooth bump at the selected ordinate has positive "
                            + "integral against the multiplicity-weighted target measure. Vague "
                            + "convergence makes its residual integral eventually positive.")),
                    Paragraph(Text(
                        "Expanding that residual integral as a finite sum produces an indexed "
                            + "positive-weight atom in the bump support and hence in the chosen "
                            + "open neighborhood. No separate isolation premise is needed."))),
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
        Formula ennreal = F.Id("ENNReal");
        Formula zeros = F.Id("Z");
        Formula zeroIndex = F.Id("n0");
        Formula count = F.Id("M");
        Formula transform = F.Id("G");
        Formula atom = F.Id("tau");
        Formula weight = F.Id("c");
        Formula neighborhood = F.Id("U");
        Formula n = F.Id("n");
        Formula j = F.Id("j");
        Formula xi = F.Id("xi");
        Formula test = F.Id("phi");
        Formula countAtN = Call("apply", count, n);
        Formula contactIndex = Call("Fin", countAtN);
        Formula transformAt = Call("apply", Call("apply", transform, n), xi);
        Formula contactSubtype = Call(
            "Subtype",
            Seq(xi, Colon, Sp, real),
            Seq(transformAt, Sp, Eq, Sp, D(0)));
        Formula atomAt = Call("apply", Call("apply", atom, n), j);
        Formula atomValue = Call("val", atomAt);
        Formula weightAt = Call("apply", Call("apply", weight, n), j);
        Formula testAt = Call("apply", test, xi);
        Formula testWeight = Call("ofReal", testAt);
        Formula residual = Call(
            "sumMeasure",
            Lambda(
                Seq(j, Colon, Sp, contactIndex),
                Seq(weightAt, Sp, Cdot, Sp, Call("dirac", atomValue))));
        Formula target = Call("zeroCountingMeasure", zeros);
        Formula residualIntegral = Call(
            "lintegral", residual,
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
                    Lambda(Seq(n, Colon, Sp, nat), residualIntegral),
                    Call("atTop"),
                    Call("nhds", targetIntegral))));
        Formula ordinate = Call("im", Call("zero", zeros, zeroIndex));
        Formula localizedAtom = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("j", contactIndex)],
            Seq(
                D(0), Sp, Lt, Sp, weightAt, Sp, Land, Sp,
                Call("mem", atomValue, neighborhood)));
        Formula eventualConclusion = Call(
            "EventuallyAtTop",
            Lambda(Seq(n, Colon, Sp, nat), localizedAtom));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp,
                zeros, Colon, Sp, Call("ZeroData"), Comma, Sp,
                zeroIndex, Colon, Sp, nat, Comma),
            Seq(count, Colon, Sp, nat, Sp, To, Sp, nat, Comma, Sp,
                transform, Colon, Sp, nat, Sp, To, Sp,
                real, Sp, To, Sp, complex, Comma),
            Seq(atom, Colon, Sp, Forall, Sp, n, Colon, Sp, nat, Comma, Sp,
                Call("Fin", Call("apply", count, n)), Sp, To, Sp,
                contactSubtype, Comma),
            Seq(weight, Colon, Sp, Forall, Sp, n, Colon, Sp, nat, Comma, Sp,
                Call("Fin", Call("apply", count, n)), Sp, To, Sp,
                ennreal, Comma),
            Seq(neighborhood, Colon, Sp, Call("Set", real), Comma, Sp,
                Call("IsOpen", neighborhood), Sp, Land, Sp,
                Call("mem", ordinate, neighborhood), Sp, Land),
            Seq(vague, Sp, Rightarrow),
            Seq(eventualConclusion, Dot),
        ]));
    }
}
