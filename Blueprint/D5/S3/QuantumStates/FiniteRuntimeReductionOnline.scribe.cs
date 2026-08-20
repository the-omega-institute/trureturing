using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class FiniteRuntimeReductionOnlineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed finite-precision runtime is finite, and online learning requires an expanded state.",
        H("Finite Runtime Reduction with Online State Extension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-runtime-reduction-with-falsifiable-online-extension"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumStates/FiniteRuntimeReductionOnline."
                        + "finite_precision_runtime_reduction_online"),
                H("Finite-precision runtime reduction with online state extension"),
                StatementSource.FromAuthor(RuntimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The complete runtime state is constructed as the product of the five "
                            + "finite source components C, K, R, M, and S. Fixed parameters make "
                            + "the update and readout deterministic maps on that product; no "
                            + "uncounted input appears in either function's domain.")),
                    Paragraph(Text(
                        "The public conclusion includes the exact product cardinality and the "
                            + "injective b-bit parameter bound. Its online clause constructs the "
                            + "expanded runtime state, records an actual parameter or optimizer "
                            + "mutation, and rules out collapse to a fixed runtime when that "
                            + "mutation changes the readout against frozen old values.")),
                    Paragraph(Text(
                        "Repository search found no exact packaged theorem. Pinned Mathlib supplies "
                            + "and is applied through Fintype.card_prod, Fintype.card_fun, "
                            + "Fintype.card_fin, and Fintype.card_le_of_injective."))),
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
        Formula optimizer = F.Id("Optimizer");
        Formula state = Call("RuntimeState", c, k, r, m, s);
        Formula learningState = Call("LearningState", c, k, r, m, s, thetaType, optimizer);
        Formula theta = F.Id("theta");
        Formula update = F.Id("update");
        Formula readout = F.Id("readout");
        Formula n = F.Id("N");
        Formula b = F.Id("b");
        Formula encoding = F.Id("parameterEncoding");
        Formula injective = F.Id("hParameterInjective");
        Formula onlineUpdate = F.Id("onlineUpdate");
        Formula onlineReadout = F.Id("onlineReadout");
        Formula online = Call("onlineLearningOccurred", onlineUpdate, onlineReadout);
        Formula system = F.Id("system");
        Formula onlineSystem = F.Id("onlineSystem");
        Func<Formula, Formula> card = type => Call("card", type);
        Formula updateType = Seq(thetaType, Sp, To, Sp, state, Sp, To, Sp, state);
        Formula readoutType = Seq(thetaType, Sp, To, Sp, state, Sp, To, Sp, o);
        Formula onlineUpdateType = Seq(learningState, Sp, To, Sp, learningState);
        Formula onlineReadoutType = Seq(learningState, Sp, To, Sp, o);
        Formula parameterEncodingType = Seq(thetaType, Sp, To, Sp,
            Call("ParameterSlots", n, b));
        Formula fixedReadout = F.Id("fixedReadout");
        Formula fixedState = F.Id("state");
        Formula productCard = Seq(card(state), Sp, Times, Sp, card(thetaType),
            Sp, Times, Sp, card(optimizer));
        Formula updatedTheta = Seq(Apply(onlineUpdate, fixedState), Dot, D(2), Dot, D(1));
        Formula oldTheta = Seq(fixedState, Dot, D(2), Dot, D(1));
        Formula updatedOptimizer = Seq(Apply(onlineUpdate, fixedState), Dot, D(2), Dot, D(2));
        Formula oldOptimizer = Seq(fixedState, Dot, D(2), Dot, D(2));
        Formula fixedRuntime = Seq(fixedState, Dot, D(1));

        return Disp(Seq(
            Forall, Sp, c, Comma, Sp, k, Comma, Sp, r, Comma, Sp, m, Comma, Sp,
            s, Comma, Sp, o, Comma, Sp, thetaType, Comma, Sp,
            optimizer, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Typeclass("Fintype", c), Comma, Sp, Typeclass("Fintype", k), Comma, Sp,
            Typeclass("Fintype", r), Comma, Sp, Typeclass("Fintype", m), Comma, Sp,
            Typeclass("Fintype", s), Comma, Sp, Typeclass("Finite", o), Comma, Sp,
            Typeclass("Fintype", thetaType), Comma, Sp, Typeclass("Fintype", optimizer), Comma, Esc,
            theta, Colon, Sp, thetaType, Comma, Sp,
            update, Colon, Sp, updateType, Comma, Sp,
            readout, Colon, Sp, readoutType, Comma, Esc,
            n, Sp, b, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            encoding, Colon, Sp, parameterEncodingType, Comma, Sp,
            injective, Colon, Sp, Call("Injective", encoding), Comma, Sp,
            onlineUpdate, Colon, Sp, onlineUpdateType, Comma, Sp,
            onlineReadout, Colon, Sp, onlineReadoutType, Comma, Esc,
            Exists, Sp, system, Colon, Sp, Call("ObservationSystem", state, o), Comma, Sp,
            Call("transition", system), Sp, Eq, Sp, Call("Apply", update, theta), Sp,
            Land, Sp, Call("readout", system), Sp, Eq, Sp, Call("Apply", readout, theta), Sp,
            Land, Sp, card(state), Sp, Eq, Sp,
            Seq(card(c), Sp, Times, Sp, card(k), Sp, Times, Sp, card(r),
                Sp, Times, Sp, card(m), Sp, Times, Sp, card(s)), Sp, Land, Sp,
            card(thetaType), Sp, Leq, Sp,
            new Formula.Power(D(2), Seq(b, Sp, Times, Sp, n)), Sp, Land, Sp,
            Open, online, Sp, Rightarrow, Sp,
            Open,
            Open, Exists, Sp, onlineSystem, Colon, Sp,
            Call("ObservationSystem", learningState, o), Comma, Sp,
            Call("transition", onlineSystem), Sp, Eq, Sp, onlineUpdate, Sp, Land, Sp,
            Call("readout", onlineSystem), Sp, Eq, Sp, onlineReadout, Sp, Land, Sp,
            card(learningState), Sp, Eq, Sp, productCard, Sp, Land, Sp,
            Exists, Sp, fixedState, Comma, Sp,
            Open,
            updatedTheta, Sp, Neq, Sp, oldTheta, Sp, Lor, Sp,
            updatedOptimizer, Sp, Neq, Sp, oldOptimizer,
            Close, Close,
            Sp, Land, Sp,
            Neg, Sp, Exists, Sp, fixedReadout, Colon, Sp, Seq(state, Sp, To, Sp, o), Comma, Sp,
            Forall, Sp, fixedState, Comma, Sp,
            Apply(fixedReadout, fixedRuntime), Sp, Eq, Sp,
            Apply(onlineReadout, fixedState), Close, Close, Dot));
    }
}
