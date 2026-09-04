using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class FirstThreeRealizationsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first three frozen statements are equivalent to their realization laws.",
        H("First Three Legacy Primitive Realizations"),
        Blocks(
            DefinitionNode("agenda-power-realization-definition", "agendaPowerRealization",
                "Agenda power realization",
                "The typed realization reads the sequential majority winner and decides ValidAgenda, with no point anchors."),
            TheoremNode("agenda-power-realization", "agenda_power_realization",
                "Agenda power realization certificate", AgendaFormula(),
                "The certificate identifies the full frozen agenda-power proposition with agendaPowerArena.Law agendaPowerRealization."),
            DefinitionNode("residue-realization-definition", "residueRealization",
                "Residue realization",
                "The typed realization uses residueReadout at every residue sensor and has no point anchors."),
            TheoremNode("adaptive-residue-realization",
                "two_step_adaptive_residue_identification_realization",
                "Adaptive residue realization certificate", ResidueFormula(),
                "The certificate identifies every clause of the frozen adaptive-residue proposition with residueArena.Law residueRealization."),
            DefinitionNode("spectrum-realization-definition", "spectrumRealization",
                "Spectrum realization",
                "The typed realization reads SpectrumAtom.index at the sole readout and has no point anchors."),
            TheoremNode("spectrum-index-realization",
                "spectrum_atom_index_bijective_realization",
                "Spectrum index realization certificate", SpectrumFormula(),
                "The certificate identifies Function.Bijective SpectrumAtom.index with spectrumArena.Law spectrumRealization."))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe TheoremNode(
        string id, string declaration, string title, Formula formula, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Theorem);

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

    private static Formula Member(Formula owner, string field) =>
        Seq(owner, Dot, F.Id(field));

    private static Formula Paren(Formula formula) => Seq(Open, formula, Close);

    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(Paren(clauses[index]));
        }
        return Seq([.. items]);
    }

    private static Formula Or(Formula left, Formula right) =>
        Seq(Paren(left), Sp, Lor, Sp, Paren(right));

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        Seq(left, Sp, Neq, Sp, right);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula ForallTyped(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);

    private static Formula ExistsTyped(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, variable, Colon, Sp, type, Comma, Sp, body);

    private static Formula ExistsTwoTyped(
        Formula first, Formula second, Formula type, Formula body) =>
        Seq(Exists, Sp, first, Sp, second, Colon, Sp, type, Comma, Sp, body);

    private static Formula Qualified(string owner, string name) =>
        Member(F.Id(owner), name);

    private static Formula ApplyExact(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Sensor(string name) => Qualified("ResidueSensor", name);

    private static Formula FinWitness(byte value) =>
        Seq(Langle, D(value), Comma, Sp, F.Id("by"), Sp, F.Id("decide"), Rangle);

    private static Formula Law(string arena, string realization) =>
        Seq(Member(F.Id(arena), "Law"), Sp, F.Id(realization));

    private static Formula Certificate(Formula statement, string arena, string realization) =>
        Disp(Seq(Paren(statement), Sp, Iff, Sp, Law(arena, realization), Dot));

    private static Formula AgendaFormula()
    {
        Formula desired = F.Id("desired");
        Formula agenda = F.Id("agenda");
        Formula agendaPrime = Seq(F.Id("agenda"), Apos);
        Formula agendaType = F.Id("Agenda");
        Formula winner = Call("sequentialWinner", F.Id("majorityPrefers"), agenda);
        Formula winnerPrime = Call(
            "sequentialWinner", F.Id("majorityPrefers"), agendaPrime);
        Formula allWinners = ForallTyped(desired, Call("Fin", D(3)),
            ExistsTyped(agenda, agendaType, And(
                Call("ValidAgenda", agenda), Equal(winner, desired))));
        Formula separatingPair = ExistsTwoTyped(agenda, agendaPrime, agendaType, And(
            Call("ValidAgenda", agenda),
            Call("ValidAgenda", agendaPrime),
            NotEqual(agenda, agendaPrime),
            NotEqual(winner, winnerPrime)));

        return Certificate(
            And(allWinners, separatingPair),
            "agendaPowerArena", "agendaPowerRealization");
    }

    private static Formula ResidueFormula()
    {
        Formula state = F.Id("state");
        Formula sensor = F.Id("sensor");
        Formula depth = F.Id("depth");
        Formula protocol = F.Id("protocol");
        Formula history = F.Id("history");
        Formula residueState = F.Id("ResidueState");
        Formula readTwo = Call("residueReadout", Sensor("two"), state);
        Formula falseFiber = ForallTyped(state, residueState, Seq(
            Equal(readTwo, F.Id("false")), Sp, Iff, Sp,
            Or(Equal(state, F.Id("zeroState")), Equal(state, F.Id("tenState")))));
        Formula trueFiber = ForallTyped(state, residueState, Seq(
            Equal(readTwo, F.Id("true")), Sp, Iff, Sp,
            Or(Equal(state, F.Id("fifteenState")),
                Equal(state, F.Id("twentyOneState")))));
        Formula question = Member(protocol, "question");
        Formula firstQuestion = ForallTyped(history, Arrow(Call("Fin", D(0)), F.Id("Bool")),
            Equal(
                ApplyExact(question, FinWitness(0), history),
                Call("residueReadout", Sensor("two"))));
        Formula secondQuestion = ForallTyped(history, Arrow(Call("Fin", D(1)), F.Id("Bool")),
            Equal(
                ApplyExact(question, FinWitness(1), history),
                Call("if", Call("history", D(0)),
                    Call("residueReadout", Sensor("five")),
                    Call("residueReadout", Sensor("three")))));
        Formula protocolExists = ExistsTyped(
            protocol, Call("BinaryProtocol", residueState, D(2)), And(
                firstQuestion,
                secondQuestion,
                Call("UsesReadoutFamily", F.Id("residueReadout"), protocol),
                ApplyExact(Qualified("Function", "Injective"),
                    Member(protocol, "transcript"))));
        Formula noSensorInjective = ForallTyped(sensor, F.Id("ResidueSensor"), Seq(
            Neg, Sp, ApplyExact(Qualified("Function", "Injective"),
                Call("residueReadout", sensor))));
        Formula noShallowerProtocol = ForallTyped(depth, F.Id("Nat"), Seq(
            depth, Sp, Lt, Sp, D(2), Sp, Rightarrow, Sp, Neg, Sp,
            Call("ExactAtDepth", F.Id("residueReadout"), depth)));
        Formula statement = And(
            falseFiber,
            trueFiber,
            protocolExists,
            noSensorInjective,
            noShallowerProtocol,
            Equal(F.Id("residueAdaptiveDepth"), D(2)),
            Equal(F.Id("residueStaticDepth"), D(3)),
            Seq(F.Id("residueAdaptiveDepth"), Sp, Lt, Sp,
                F.Id("residueStaticDepth")));

        return Certificate(statement, "residueArena", "residueRealization");
    }

    private static Formula SpectrumFormula()
    {
        Formula statement = ApplyExact(
            Qualified("Function", "Bijective"), Qualified("SpectrumAtom", "index"));
        return Certificate(statement, "spectrumArena", "spectrumRealization");
    }
}
