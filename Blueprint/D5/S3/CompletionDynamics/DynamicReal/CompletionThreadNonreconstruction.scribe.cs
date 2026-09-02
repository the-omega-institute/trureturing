using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.DynamicReal;

internal sealed class CompletionThreadNonreconstructionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/CompletionDynamics/DynamicReal/CompletionThreadNonreconstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden real threads converge to one completion while retaining distinct histories, "
            + "and finite controlled behavior has its canonical minimal quotient.",
        H("Completion Thread Nonreconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-thread-nonreconstruction"),
                DeclarationHandle.Create(Prefix + "completion_thread_nonreconstruction"),
                H("Completion thread nonreconstruction"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real origin coefficient, the canonical golden geometric "
                            + "thread converges to the golden ratio, and its filter limit is "
                            + "that completed value.")),
                    Paragraph(Text(
                        "On the realized range of these thread functions, the completed-value "
                            + "readout is not injective. Consequently no function of the "
                            + "completed real value can recover every origin coefficient.")),
                    Paragraph(Text(
                        "For an arbitrary finite controlled state carrier and finite exact "
                            + "realization, the canonical completion uses equality of readouts "
                            + "after every finite input word. The imported universal property "
                            + "gives the unique surjective factor onto that quotient, preserves "
                            + "all input updates and the readout, and proves its cardinal "
                            + "minimality.")),
                    Paragraph(Text(
                        "This is a classical quotient-information result. The source's final "
                            + "qualifier that internal representatives usually cannot be "
                            + "recovered has no quantified scope, so it is not promoted to a "
                            + "separate universal assertion."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula ExistsOne(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Bang, Sp, variable, Colon, Sp, type, Comma, Sp, body);

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = F.Id("Type");
        Formula phi = Varphi;
        Formula c = F.Id("c");
        Formula thread = F.Id("thread");
        Formula decoder = F.Id("decode");
        Formula atTop = F.Id("atTop");
        Formula goldenThread = F.Id("goldenGeometricThread");
        Formula threadAtC = Apply(goldenThread, c);
        Formula threadRange = Call("range", goldenThread);
        Formula completedAtC = Call("limUnder", atTop, threadAtC);
        Formula completedThread = Lambda(
            Seq(thread, Colon, Sp, threadRange),
            Call("limUnder", atTop, Call("val", thread)));

        Formula convergence = All(
            [Bound("c", real)],
            And(
                Call("Tendsto", threadAtC, atTop, Call("nhds", phi)),
                Equal(completedAtC, phi)));
        Formula notInjective = new Formula.Not(Call("Injective", completedThread));
        Formula recoversEveryOrigin = All(
            [Bound("c", real)],
            Equal(Apply(decoder, completedAtC), c));
        Formula noDecoder = new Formula.Not(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("decode", Arrow(real, real))],
            recoversEveryOrigin));

        Formula yType = F.Id("Y");
        Formula inputType = F.Id("U");
        Formula outputType = F.Id("O");
        Formula realizedType = F.Id("W");
        Formula update = F.Id("update");
        Formula readout = F.Id("readout");
        Formula realization = F.Id("realization");
        Formula realizedUpdate = F.Id("realizedUpdate");
        Formula realizedReadout = F.Id("realizedReadout");
        Formula input = F.Id("u");
        Formula factor = F.Id("factor");
        Formula completion = Call("ControlledCompletion", update, readout);

        Formula updatesCommute = All(
            [Bound("u", inputType)],
            Equal(
                Call("comp", realization, Apply(update, input)),
                Call("comp", Apply(realizedUpdate, input), realization)));
        Formula controlledPremises = And(
            Call("Fintype", yType),
            And(
                Call("Fintype", realizedType),
                And(
                    Call("Surjective", realization),
                    And(
                        updatesCommute,
                        Equal(
                            readout,
                            Call("comp", realizedReadout, realization))))));

        Formula factorUpdates = All(
            [Bound("u", inputType)],
            Equal(
                Call("comp", factor, Apply(realizedUpdate, input)),
                Call("comp",
                    Call("completionUpdate", update, readout, input),
                    factor)));
        Formula factorProperties = And(
            Call("Surjective", factor),
            And(
                Equal(
                    Call("completionProjection", update, readout),
                    Call("comp", factor, realization)),
                And(
                    factorUpdates,
                    Equal(
                        Call("comp",
                            Call("completionReadout", update, readout), factor),
                        realizedReadout))));
        Formula controlledConclusion = And(
            ExistsOne(factor, Arrow(realizedType, completion), factorProperties),
            LessOrEqual(Call("card", completion), Call("card", realizedType)));
        Formula controlledMinimality = All(
            [
                Bound("Y", type),
                Bound("U", type),
                Bound("O", type),
                Bound("W", type),
                Bound("update", Arrow(inputType, Arrow(yType, yType))),
                Bound("readout", Arrow(yType, outputType)),
                Bound("realization", Arrow(yType, realizedType)),
                Bound("realizedUpdate", Arrow(inputType, Arrow(realizedType, realizedType))),
                Bound("realizedReadout", Arrow(realizedType, outputType)),
            ],
            Implies(controlledPremises, controlledConclusion));

        return Disp(And(
            convergence,
            And(notInjective, And(noDecoder, controlledMinimality))));
    }
}
