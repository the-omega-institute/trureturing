using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class TestingTowerStructureMembershipDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The testing tower satisfies its carrier, valuation, and two-height classification clauses.",
        H("Testing Tower Structure Membership"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("testing-tower-has-multi-filtration-membership"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/TestingTowerStructureMembership."
                        + "testing_tower_has_multi_filtration_membership"),
                H("The testing tower is a multi-filtration naming system"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the sequence space over a finite nontrivial output type, "
                            + "with its Polish and Borel structures and an explicitly supplied "
                            + "atomless sigma-finite measure.")),
                    Paragraph(Text(
                        "The constructed assignment retains the default table extension. The public "
                            + "clauses expose countability of the exact TestingName carrier, the "
                            + "noncomputable halting domain of program names, finite description-length "
                            + "sublevels, an infinite execution-"
                            + "cost sublevel, finite mixed-cost sublevels, and the null named image.")),
                    Paragraph(Text(
                        "The constructed tower wraps NamingSystem as its primary coordinate and "
                            + "uses the execution-cost model as its secondary coordinate. The proof "
                            + "applies the three standalone prerequisites and the frozen dark-side "
                            + "conservation owner."))),
                DescribeRole.Lemma)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Naming/MultiFiltrationNamingSystem")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Naming/TestingCostClassification")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Naming/TestingTowerValuation"))
        ]));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Lambda(Formula binder, Formula domain, Formula body) =>
        Seq(Open, binder, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula TheoremFormula()
    {
        Formula output = F.Id("O");
        Formula defaultOutput = F.Id("o0");
        Formula decoder = F.Id("decode");
        Formula programInput = F.Id("input");
        Formula code = F.Id("code");
        Formula programCost = F.Id("programCost");
        Formula measure = Mu;
        Formula program = F.Id("p");
        Formula codeObject = F.Id("c");
        Formula name = F.Id("a");
        Formula budget = F.Id("Q");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula sequenceType = Arrow(naturals, output);
        Formula names = Call("TestingName", output);
        Formula codeType = Arrow(names, Call("List", F.Id("Bool")));
        Formula decoderType = Arrow(naturals, sequenceType);
        Formula programCostType = Arrow(naturals, naturals);
        Formula measureType = Call("Measure", sequenceType);

        Formula programAssignment = Call(
            "testingAssignment", defaultOutput, decoder, programInput, Call("inr", program));
        Formula decodedProgram = Call("ofNatCode", program);
        Formula haltingDomain = Call("Dom", Call("eval", decodedProgram, programInput));
        Formula programClause = Seq(
            Forall, Sp, program, Colon, Sp, naturals, Comma, Sp,
            Call("isSome", programAssignment), Sp, Iff, Sp, haltingDomain);

        Formula encodedAssignment = Call(
            "testingAssignment", defaultOutput, decoder, programInput,
            Call("inr", Call("encodeCode", codeObject)));
        Formula computableDomain = Call("ComputablePred", Lambda(
            codeObject,
            F.Id("PartrecCode"),
            Call("isSome", encodedAssignment)));

        Formula codeLength = Call("length", Call("code", name));
        Formula executionCost = Call("testingExecutionCost", programCost, name);
        Formula finiteCodeClause = Seq(
            Forall, Sp, budget, Colon, Sp, naturals, Comma, Sp,
            Call("Finite", new Formula.SetBuilder(
                Seq(codeLength, Sp, Leq, Sp, budget), name, names)));
        Formula infiniteExecutionClause = Call("Infinite", new Formula.SetBuilder(
            Seq(executionCost, Sp, Leq, Sp, D(1)), name, names));
        Formula mixedCost = Seq(
            codeLength, Sp, Plus, Sp, Call("natLog", D(2), executionCost));
        Formula finiteMixedClause = Seq(
            Forall, Sp, budget, Colon, Sp, naturals, Comma, Sp,
            Call("Finite", new Formula.SetBuilder(
                Seq(mixedCost, Sp, Leq, Sp, budget), name, names)));

        Formula tower = Call(
            "testingTower", defaultOutput, decoder, programInput, code, programCost, measure);
        Formula namedImage = Call("named", Call("primary", tower));
        Formula nullNamedImage = Seq(
            Apply(measure, namedImage), Sp, Eq, Sp, D(0));

        Formula conclusion = Seq(
            Call("Countable", names), Sp, Land, RowBreak, Grp(),
            Open, programClause, Close, Sp, Land, RowBreak, Grp(),
            Neg, Sp, computableDomain, Sp, Land, RowBreak, Grp(),
            Open, finiteCodeClause, Close, Sp, Land, RowBreak, Grp(),
            infiniteExecutionClause, Sp, Land, RowBreak, Grp(),
            Open, finiteMixedClause, Close, Sp, Land, RowBreak, Grp(),
            nullNamedImage);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, output, Colon, Sp, type, Comma, RowBreak, Grp(),
            OpenBracket, Call("Finite", output), CloseBracket, Comma, Sp,
            OpenBracket, Call("Nontrivial", output), CloseBracket, Comma, RowBreak, Grp(),
            OpenBracket, Call("TopologicalSpace", sequenceType), CloseBracket, Comma, Sp,
            OpenBracket, Call("PolishSpace", sequenceType), CloseBracket, Comma, RowBreak, Grp(),
            OpenBracket, Call("MeasurableSpace", sequenceType), CloseBracket, Comma, Sp,
            OpenBracket, Call("BorelSpace", sequenceType), CloseBracket, Comma, RowBreak, Grp(),
            OpenBracket, Call("Uncountable", sequenceType), CloseBracket, Comma, RowBreak, Grp(),
            Forall, Sp, defaultOutput, Colon, Sp, output, Comma, Sp,
            decoder, Colon, Sp, decoderType, Comma, RowBreak, Grp(),
            programInput, Colon, Sp, naturals, Comma, RowBreak, Grp(),
            code, Colon, Sp, codeType, Comma, Sp,
            programCost, Colon, Sp, programCostType, Comma, RowBreak, Grp(),
            measure, Colon, Sp, measureType, Comma, RowBreak, Grp(),
            OpenBracket, Call("NullSingletonClass", measure), CloseBracket, Comma, Sp,
            OpenBracket, Call("SigmaFinite", measure), CloseBracket, Comma, RowBreak, Grp(),
            Call("Injective", code), Sp, Rightarrow, Sp,
            Call("withMeasureSpace", measure, Seq(Open, conclusion, Close)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
