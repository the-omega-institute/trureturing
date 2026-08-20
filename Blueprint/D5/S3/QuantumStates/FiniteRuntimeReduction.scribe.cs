using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class FiniteRuntimeReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed finite-precision runtime is a finite deterministic observation system.",
        H("Finite-Precision Runtime Reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-precision-runtime-reduction"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumStates/FiniteRuntimeReduction."
                        + "finite_precision_runtime_reduction"),
                H("Finite-precision runtime reduction"),
                StatementSource.FromAuthor(RuntimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The complete runtime state is constructed as the product of the five "
                            + "finite source components C, K, R, M, and S. Fixed parameters make "
                            + "the update and readout deterministic maps on that product, while "
                            + "the empty external-input type records the absence of uncounted inputs.")),
                    Paragraph(Text(
                        "The public conclusion includes the exact product cardinality, an injective "
                            + "b-bit encoding bound for N parameter slots, and the expanded product "
                            + "cardinality when online learning carries parameters and optimizer state.")),
                    Paragraph(Text(
                        "Repository search found no packaged theorem with this complete reduction. "
                            + "Pinned Mathlib supplies and is applied through Fintype.card_prod, "
                            + "Fintype.card_fun, Fintype.card_fin, and "
                            + "Fintype.card_le_of_injective."))),
                DescribeRole.Theorem))));

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula RuntimeFormula()
    {
        Formula c = F.Id("C");
        Formula k = F.Id("K");
        Formula r = F.Id("R");
        Formula m = F.Id("M");
        Formula s = F.Id("S");
        Formula o = F.Id("O");
        Formula thetaType = F.Id("Theta");
        Formula external = F.Id("External");
        Formula state = Call("RuntimeState", c, k, r, m, s);
        Formula theta = F.Id("theta");
        Formula update = F.Id("update");
        Formula readout = F.Id("readout");
        Formula n = F.Id("N");
        Formula b = F.Id("b");
        Formula encoding = F.Id("parameterEncoding");
        Formula injective = F.Id("hParameterInjective");
        Formula online = F.Id("onlineLearning");
        Formula system = F.Id("system");
        Formula optimizer = F.Id("Optimizer");
        Func<Formula, Formula> card = type => Call("card", type);
        Formula updateType = Seq(thetaType, Sp, To, Sp, state, Sp, To, Sp, state);
        Formula readoutType = Seq(thetaType, Sp, To, Sp, state, Sp, To, Sp, o);
        Formula parameterEncodingType = Seq(thetaType, Sp, To, Sp,
            Call("ParameterSlots", n, b));
        Formula productState = Seq(c, Sp, Times, Sp, k, Sp, Times, Sp, r,
            Sp, Times, Sp, m, Sp, Times, Sp, s);
        Formula onlineState = Call("Prod", Call("Prod", state, thetaType), optimizer);

        return Disp(Seq(
            Forall, Sp, c, Comma, Sp, k, Comma, Sp, r, Comma, Sp, m, Comma, Sp,
            s, Comma, Sp, o, Comma, Sp, thetaType, Comma, Sp, external, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Typeclass("Fintype", c), Comma, Sp, Typeclass("Fintype", k), Comma, Sp,
            Typeclass("Fintype", r), Comma, Sp, Typeclass("Fintype", m), Comma, Sp,
            Typeclass("Fintype", s), Comma, Sp, Typeclass("Fintype", o), Comma, Sp,
            Typeclass("Fintype", thetaType), Comma, Sp, Typeclass("IsEmpty", external),
            Comma, Esc,
            theta, Colon, Sp, thetaType, Comma, Sp,
            update, Colon, Sp, updateType, Comma, Sp,
            readout, Colon, Sp, readoutType, Comma, Esc,
            n, Sp, b, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            encoding, Colon, Sp, parameterEncodingType, Comma, Sp,
            injective, Colon, Sp, Call("Injective", encoding), Comma, Sp,
            online, Colon, Sp, F.Id("Prop"), Comma, Esc,
            Exists, Sp, system, Colon, Sp,
            Call("ObservationSystem", state, o), Comma, Sp,
            Call("transition", system), Sp, Eq, Sp,
            Apply(update, theta), Sp, Land, Sp,
            Call("readout", system), Sp, Eq, Sp,
            Apply(readout, theta), Sp, Land, Sp,
            card(state), Sp, Eq, Sp,
            Seq(card(c), Sp, Times, Sp, card(k), Sp, Times, Sp, card(r),
                Sp, Times, Sp, card(m), Sp, Times, Sp, card(s)), Sp, Land, Sp,
            card(thetaType), Sp, Leq, Sp,
            new Formula.Power(D(2), Seq(b, Sp, Times, Sp, n)), Sp, Land, Sp,
            Open, online, Sp, Rightarrow, Sp,
            Forall, Sp, optimizer, Colon, Sp, Operatorname, Grp(F.Id("Type")),
            Sp, Typeclass("Fintype", optimizer), Comma, Sp,
            card(onlineState), Sp, Eq, Sp,
            Seq(card(state), Sp, Times, Sp, card(thetaType), Sp, Times, Sp,
                card(optimizer)), Close, Dot));
    }
}
