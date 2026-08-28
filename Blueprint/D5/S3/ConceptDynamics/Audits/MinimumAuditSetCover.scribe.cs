using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Audits;

internal sealed class MinimumAuditSetCoverDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Audits/MinimumAuditSetCover."
            + "minimum_audit_set_is_set_cover";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum target-complete audit suites are minimum defect set covers.",
        H("Minimum Audit Set Cover"),
        Blocks(Describe.Lean(
            DescribeId.Create("minimum-audit-set-is-set-cover"),
            DeclarationHandle.Create(Declaration),
            H("Minimum complete audit suites are minimum defect covers"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The current and target concepts construct the canonical defect relation. "
                        + "Each test covers exactly the defects on which its response differs.")),
                Paragraph(Text(
                    "Completeness is stated on the canonical joint readout of a selected finite "
                        + "suite. The theorem transports both feasibility and cardinality comparison "
                        + "against every candidate suite, so no optimizer is assumed to exist."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula stateType = F.Id("X");
        Formula currentType = F.Id("C");
        Formula targetType = F.Id("T");
        Formula testType = F.Id("I");
        Formula response = F.Id("O");
        Formula current = F.Id("c");
        Formula target = F.Id("t");
        Formula test = F.Id("q");
        Formula selected = F.Id("J");
        Formula suite = F.Id("K");
        Formula candidate = F.Id("L");
        Formula audit = F.Id("i");
        Formula leftPoint = F.Id("x");
        Formula rightPoint = F.Id("y");
        Formula pair = F.Id("p");
        Formula suiteType = Call("Finset", testType);
        Formula defect = Call("defectRelation", current, target);

        Formula selectedReadout(Formula family, Formula point) =>
            Call("jointReadout", Call("restrict", test, family), point);
        Formula evidenceAt(Formula family, Formula point) => Seq(
            Open,
            Apply(current, point),
            Comma,
            Sp,
            selectedReadout(family, point),
            Close);
        Formula completeAt(Formula family) => new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", stateType), Bound("y", stateType)],
            Implies(
                Equal(evidenceAt(family, leftPoint), evidenceAt(family, rightPoint)),
                Equal(Apply(target, leftPoint), Apply(target, rightPoint))));
        Formula testCover = new Formula.SetBuilder(
            NotEqual(
                Apply(Apply(test, audit), Call("fst", pair)),
                Apply(Apply(test, audit), Call("snd", pair))),
            pair,
            defect);
        Formula coversAt(Formula family) => Equal(
            Call("Union", Seq(audit, Sp, InMacro, Sp, family), testCover),
            defect);
        Formula completeLet = Seq(
            Operatorname,
            Grp(F.Id("let")),
            Sp,
            Seq(F.Id("Complete"), Open, suite, Colon, Sp, suiteType, Close),
            Sp,
            Colon,
            Eq,
            Sp,
            completeAt(suite),
            Semi,
            Sp);
        Formula coversLet = Seq(
            Operatorname,
            Grp(F.Id("let")),
            Sp,
            Seq(F.Id("Covers"), Open, suite, Colon, Sp, suiteType, Close),
            Sp,
            Colon,
            Eq,
            Sp,
            coversAt(suite),
            Semi,
            Sp);
        Formula minimumComplete = And(
            Call("Complete", selected),
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("L"),
                suiteType,
                Implies(
                    Call("Complete", candidate),
                    LessOrEqual(Call("card", selected), Call("card", candidate)))));
        Formula minimumCover = And(
            Call("Covers", selected),
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("L"),
                suiteType,
                Implies(
                    Call("Covers", candidate),
                    LessOrEqual(Call("card", selected), Call("card", candidate)))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("C", type),
                Bound("T", type),
                Bound("I", type),
                Bound("O", Arrow(testType, type)),
                Bound("c", Arrow(stateType, currentType)),
                Bound("t", Arrow(stateType, targetType)),
                Bound("q", DependentReadoutType(testType, stateType, response)),
                Bound("J", suiteType),
            ],
            Seq(
                completeLet,
                coversLet,
                new Formula.Logic(
                    minimumComplete,
                    FormulaLogicOperator.Iff,
                    minimumCover))));
    }

    private static Formula DependentReadoutType(
        Formula testType,
        Formula stateType,
        Formula response) => Seq(
            Forall,
            Sp,
            F.Id("i"),
            Colon,
            Sp,
            testType,
            Comma,
            Sp,
            stateType,
            Sp,
            To,
            Sp,
            Apply(response, F.Id("i")));

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

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
