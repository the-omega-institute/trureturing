using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Evidence;

internal sealed class ActualEvidenceRefinementStabilityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Evidence/ActualEvidenceRefinementStability."
            + "actual_evidence_refinement_stability";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual evidence fibers are nonempty, stable truth and falsity persist under "
            + "refinement, and undecided evidence admits all three refinement outcomes.",
        H("Actual Evidence Refinement Stability"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-evidence-refinement-stability"),
            DeclarationHandle.Create(Declaration),
            H("Actual refinement preserves stable knowledge"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The public carrier has an admissibility predicate, coarse and refined "
                        + "concept readouts, a proposition on states, and an admissible actual "
                        + "anchor. Both actual fibers therefore expose their anchor witness "
                        + "and cannot be the impossible phase.")),
                Paragraph(Text(
                    "Stable truth and stable falsity are each written directly as universal "
                        + "claims on the admissible coarse fiber and transported to the "
                        + "admissible refined fiber. The proof applies the frozen robust-"
                        + "knowledge monotonicity theorem to the predicate and its negation.")),
                Paragraph(Text(
                    "For conflicting witnesses t and f in one coarse fiber, the displayed "
                        + "readouts pair the coarse evidence with x=t, x=f, or the always-true "
                        + "proposition. These shared constructions yield respectively a "
                        + "stably true, stably false, and still-undecided actual fiber.")),
                Paragraph(Text(
                    "Repository search found only the separate monotonicity, empty-fiber, and "
                        + "finite four-phase results. No exact theorem combined the unrestricted "
                        + "actual-anchor clauses and the three constructive outcomes."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(params Formula[] formulas)
    {
        Formula result = formulas[^1];
        for (var index = formulas.Length - 2; index >= 0; index--)
            result = new Formula.Logic(formulas[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula ExistsState(
        string name, Formula stateType, Formula membership, Formula fiberEquality) =>
        new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create(name),
            stateType,
            And(membership, fiberEquality));

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula prop = Call("Prop");
        Formula stateType = F.Id("X");
        Formula coarseType = F.Id("B");
        Formula refinedType = F.Id("BPrime");
        Formula admissible = F.Id("A");
        Formula coarse = F.Id("E");
        Formula refined = F.Id("D");
        Formula predicate = F.Id("P");
        Formula anchor = F.Id("a");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula trueWitness = F.Id("t");
        Formula falseWitness = F.Id("f");

        Formula actualCoarse = ExistsState(
            "x", stateType, Apply(admissible, x),
            EqualTo(Apply(coarse, x), Apply(coarse, anchor)));
        Formula actualRefined = ExistsState(
            "x", stateType, Apply(admissible, x),
            EqualTo(Apply(refined, x), Apply(refined, anchor)));

        Formula coarseFiberAtX = And(
            Apply(admissible, x),
            EqualTo(Apply(coarse, x), Apply(coarse, anchor)));
        Formula refinedFiberAtX = And(
            Apply(admissible, x),
            EqualTo(Apply(refined, x), Apply(refined, anchor)));
        Formula stableTrue = Implies(
            new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("x"), stateType,
                Implies(coarseFiberAtX, Apply(predicate, x))),
            new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("x"), stateType,
                Implies(refinedFiberAtX, Apply(predicate, x))));
        Formula stableFalse = Implies(
            new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("x"), stateType,
                Implies(coarseFiberAtX, new Formula.Not(Apply(predicate, x)))),
            new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("x"), stateType,
                Implies(refinedFiberAtX, new Formula.Not(Apply(predicate, x)))));

        Formula trueReadoutX = Call("pair", Apply(coarse, x), EqualTo(x, trueWitness));
        Formula trueReadoutT = Call("pair", Apply(coarse, trueWitness),
            EqualTo(trueWitness, trueWitness));
        Formula falseReadoutX = Call("pair", Apply(coarse, x), EqualTo(x, falseWitness));
        Formula falseReadoutF = Call("pair", Apply(coarse, falseWitness),
            EqualTo(falseWitness, falseWitness));
        Formula trueProposition = F.Id("True");
        Formula unresolvedX = Call("pair", Apply(coarse, x), trueProposition);
        Formula unresolvedY = Call("pair", Apply(coarse, y), trueProposition);
        Formula unresolvedT = Call("pair", Apply(coarse, trueWitness), trueProposition);

        Formula truePhase = And(
            ExistsState("x", stateType, Apply(admissible, x),
                EqualTo(trueReadoutX, trueReadoutT)),
            new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("x"), stateType,
                Implies(And(Apply(admissible, x), EqualTo(trueReadoutX, trueReadoutT)),
                    Apply(predicate, x))));
        Formula falsePhase = And(
            ExistsState("x", stateType, Apply(admissible, x),
                EqualTo(falseReadoutX, falseReadoutF)),
            new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("x"), stateType,
                Implies(And(Apply(admissible, x), EqualTo(falseReadoutX, falseReadoutF)),
                    new Formula.Not(Apply(predicate, x)))));
        Formula unresolvedPhase = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("x", stateType), Bound("y", stateType)],
            And(
                Apply(admissible, x), EqualTo(unresolvedX, unresolvedT),
                Apply(admissible, y), EqualTo(unresolvedY, unresolvedT),
                Apply(predicate, x), new Formula.Not(Apply(predicate, y))));
        Formula conflictPremises = And(
            Apply(admissible, trueWitness), Apply(admissible, falseWitness),
            EqualTo(Apply(coarse, trueWitness), Apply(coarse, falseWitness)),
            Apply(predicate, trueWitness),
            new Formula.Not(Apply(predicate, falseWitness)));
        Formula threeOutcomes = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", stateType), Bound("f", stateType)],
            Implies(conflictPremises, And(truePhase, falsePhase, unresolvedPhase)));

        Formula hypotheses = And(
            Apply(admissible, anchor), Call("Refines", coarse, refined));
        Formula conclusion = And(
            actualCoarse, actualRefined, stableTrue, stableFalse, threeOutcomes);
        Formula theorem = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type), Bound("B", type), Bound("BPrime", type),
                Bound("A", Arrow(stateType, prop)),
                Bound("E", Arrow(stateType, coarseType)),
                Bound("D", Arrow(stateType, refinedType)),
                Bound("P", Arrow(stateType, prop)), Bound("a", stateType),
            ],
            Implies(hypotheses, conclusion));

        return Disp(theorem);
    }
}
