using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Termination;

internal sealed class ClosureMethodStopThreeParameterCompletionReopeningDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact and approximate closure support method stopping and three-parameter completion/reopening.",
        H("Closure, Method Stop, and Three-Parameter Completion/Reopening"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("closure-method-stop-three-parameter-completion-reopening"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Termination/ClosureMethodStopThreeParameterCompletionReopening."
                        + "closure_method_stop_three_parameter_completion_reopening"),
                H("Closure, method stop, and three-parameter completion/reopening"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The package records five formalized assertions. Target closure uses "
                            + "the canonical `defectRelation`; approximate closure uses the supremum "
                            + "of metric target diameters over readout fibers against a finite "
                            + "nonnegative tolerance chosen by this formalization. Empty fibers "
                            + "contribute zero and unbounded diameters contribute top. Method stopping "
                            + "is the literal distinguished-value equation.")),
                    Paragraph(Text(
                        "Three-parameter local completion checks the supplied domain, target, and finite precision. "
                            + "A three-parameter reopening requires one of those parameters to change "
                            + "and a canonical defect pair above the next precision that was absent "
                            + "above the current precision.")),
                    Paragraph(Text(
                        "Unresolved source gaps: section 5 defines a language-blind residual and "
                            + "section 44 defines operation-induced observational equivalence, but "
                            + "section 43 does not identify either construction with its stage readout "
                            + "or residual, nor give a transition map to a new stage residual. This "
                            + "formalization covers only the object-domain, target, and precision "
                            + "triggers.")),
                    Paragraph(Text(
                        "Section 9.1 assumes a metric and explicitly uses tolerance zero, but it "
                            + "does not type the tolerance or decide whether negative tolerances are "
                            + "allowed. Lean conventionally uses `NNReal`; this is not presented as "
                            + "an exact source-domain match and must be reopened if the source later "
                            + "admits negative tolerance.")),
                    Paragraph(Text(
                        "No finiteness, decidable equality, measurability, nonempty-domain premise, "
                            + "monotonicity, or extra order law is added. The target metric is exactly "
                            + "the structure requested by approximate closure."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula Nonempty(Formula value) =>
        Call("Nonempty", value);

    private static Formula Defect(Formula readout, Formula target) =>
        Call("defectRelation", readout, target);

    private static Formula Restrict(Formula concept, Formula domain) =>
        Call("restrict", concept, domain);

    private static Formula DomainDefect(
        Formula readout,
        Formula target,
        Formula precision,
        Formula domain) =>
        Call(
            "inter",
            Call(
                "inter",
                Defect(readout, target),
                Call("distanceAbove", target, precision)),
            Call("square", domain));

    private static Formula SetDifference(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Setminus, Sp, Open, right, Close);

    private static Formula TheoremFormula()
    {
        Formula q = F.Id("q");
        Formula target = F.Id("T");
        Formula targetMetric = Typeclass("MetricSpace", target);
        Formula epsilon = Seq(
            Open, Varepsilon, Colon, Sp, Operatorname, Grp(F.Id("NNReal")), Close);
        Formula epsilonExtended = Call("coeENNReal", epsilon);
        Formula method = F.Id("M");
        Formula system = F.Id("S");
        Formula evidence = F.Id("E");
        Formula noProposal = F.Id("NoProposal");
        Formula parameters = F.Id("P");
        Formula current = F.Id("P0");
        Formula next = F.Id("P1");

        Formula clause1 = IffFormula(
            Call("Closed", q, target),
            Equal(Defect(q, target), Emptyset));

        Formula clause2 = ImpliesFormula(
            targetMetric,
            IffFormula(
                Call("ApproximatelyClosed", q, target, epsilon),
                LessOrEqual(Call("worstFiberDefect", q, target), epsilonExtended)));

        Formula clause3 = IffFormula(
            Call("MethodStopped", method, system, evidence, noProposal),
            Equal(Apply(method, system, evidence), noProposal));

        Formula clause4 = ImpliesFormula(
            targetMetric,
            IffFormula(
                Call("ThreeParameterLocallyComplete", parameters, q),
                Call(
                    "ApproximatelyClosed",
                    Restrict(q, Call("objectDomain", parameters)),
                    Restrict(Call("target", parameters), Call("objectDomain", parameters)),
                    Call("precision", parameters))));

        Formula reopeningChange = Or(
            NotEqual(Call("objectDomain", current), Call("objectDomain", next)),
            Or(
                NotEqual(Call("target", current), Call("target", next)),
                NotEqual(Call("precision", current), Call("precision", next))));
        Formula currentDomain = Call("objectDomain", current);
        Formula nextDomain = Call("objectDomain", next);
        Formula oldDefects = DomainDefect(
            q,
            Call("target", current),
            Call("precision", current),
            currentDomain);
        Formula newDefects = DomainDefect(
            q,
            Call("target", next),
            Call("precision", next),
            nextDomain);
        Formula newResidual = Nonempty(SetDifference(newDefects, oldDefects));
        Formula clause5 = ImpliesFormula(
            targetMetric,
            IffFormula(
                Call("ThreeParameterReopens", current, next, q),
                And(reopeningChange, newResidual)));

        return Disp(And(
            clause1,
            And(
                clause2,
                And(
                    clause3,
                    And(clause4, clause5)))));
    }
}
