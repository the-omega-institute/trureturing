using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;

internal sealed class NoncanonicalAgencyCountermodelsDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fair random choice and reason-sensitive deterministic choice separate canonicity "
            + "and determinism from internal authorship.",
        H("Noncanonical and Deterministic Agency Countermodels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("noncanonical-and-deterministic-agency-countermodels"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Agency/NoncanonicalAgencyCountermodels."
                        + "noncanonical_and_deterministic_agency_countermodels"),
                H("Two Boolean countermodels separate canonicity from authorship"),
                StatementSource.FromAuthor(CountermodelsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first model assigns the uniform Boolean law at every internal "
                            + "reason. Each action has mass one half and changing the reason "
                            + "does not change the law, so this randomized tie-break contains "
                            + "no internal authorship.")),
                    Paragraph(Text(
                        "Candidate exchange preserves the same fair law. A canonical "
                            + "deterministic selector would therefore have to be fixed by "
                            + "Boolean complement, which no Boolean action is.")),
                    Paragraph(Text(
                        "The second model is one shared Boolean process. At every external "
                            + "setting it is a functional future, while at one fixed setting "
                            + "false and true internal reasons lead to the distinct singleton "
                            + "actions false and true.")),
                    Paragraph(Text(
                        "All stochastic, deterministic, and reason-sensitivity clauses are "
                            + "public and use the same objects within each model. The canonical "
                            + "FunctionalFuture predicate and pinned probability-mass-function "
                            + "primitives are reused directly."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula.Not Not(Formula value) => new(value);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula CountermodelsFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula tieLaw = F.Id("tieLaw");
        Formula reason = F.Id("reason");
        Formula action = F.Id("action");
        Formula leftReason = F.Id("leftReason");
        Formula rightReason = F.Id("rightReason");
        Formula selector = F.Id("selector");
        Formula process = F.Id("process");
        Formula external = F.Id("external");
        Formula reasonOne = F.Id("reason1");
        Formula reasonTwo = F.Id("reason2");
        Formula actionOne = F.Id("action1");
        Formula actionTwo = F.Id("action2");
        Formula pmfBool = Call("PMF", boolean);
        Formula tieLawType = Arrow(boolean, pmfBool);
        Formula selectorType = Arrow(boolean, boolean);
        Formula processType = Arrow(boolean, Arrow(boolean, Call("Set", boolean)));
        Formula oneHalf = new Formula.Fraction(D(1), D(2));

        Formula fair = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("reason", boolean), Bound("action", boolean)],
            Equal(Apply(Apply(tieLaw, reason), action), oneHalf));
        Formula reasonIndependent = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("leftReason", boolean), Bound("rightReason", boolean)],
            Equal(Apply(tieLaw, leftReason), Apply(tieLaw, rightReason)));
        Formula candidateSymmetry = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("action"),
            boolean,
            Equal(
                Apply(Apply(tieLaw, reason), Call("not", action)),
                Apply(Apply(tieLaw, reason), action)));
        Formula fixedSelection = Equal(
            Call("not", Apply(selector, reason)),
            Apply(selector, reason));
        Formula canonicalSelector = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("selector"),
            selectorType,
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("reason"),
                boolean,
                new Formula.Logic(
                    candidateSymmetry,
                    FormulaLogicOperator.Implies,
                    fixedSelection)));
        Formula randomModel = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("tieLaw"),
            tieLawType,
            And(fair, And(reasonIndependent, Not(canonicalSelector))));

        Formula functional = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("external"),
            boolean,
            Call("FunctionalFuture", Apply(process, external)));
        Formula sharedContrast = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("external", boolean),
                Bound("reason1", boolean),
                Bound("reason2", boolean),
                Bound("action1", boolean),
                Bound("action2", boolean),
            ],
            And(
                new Formula.Relation(reasonOne, FormulaRelationOperator.NotEqual, reasonTwo),
                And(
                    Equal(
                        Apply(Apply(process, external), reasonOne),
                        new Formula.SetLiteral([actionOne])),
                    And(
                        Equal(
                            Apply(Apply(process, external), reasonTwo),
                            new Formula.SetLiteral([actionTwo])),
                        new Formula.Relation(
                            actionOne,
                            FormulaRelationOperator.NotEqual,
                            actionTwo)))));
        Formula deterministicModel = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("process"),
            processType,
            And(functional, sharedContrast));

        return Disp(And(randomModel, deterministicModel));
    }
}
