using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interventions;

internal sealed class DynamicClosureMinimalityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite intervention traces form the least intervention-closed refinement of a concept.",
        H("Dynamic Closure Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-original-concept-factors-through-its-dynamic-closure"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "concept_refines_dynamic_closure"),
                H("The original concept factors through its dynamic closure"),
                StatementSource.FromAuthor(ConceptRefinementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The dynamic closure records the concept value reached after every "
                            + "finite intervention word. Its coordinate at the empty word is "
                            + "exactly the original concept readout.")),
                    Paragraph(Text(
                        "Projecting a complete trace to that empty-word coordinate therefore "
                            + "recovers the original concept, so the trace readout refines it."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("dynamic-closure-is-preserved-by-every-intervention"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "dynamic_closure_is_intervention_closed"),
                H("Every intervention preserves dynamic-closure fibers"),
                StatementSource.FromAuthor(DynamicClosureClosedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two states lie in the same dynamic-closure fiber when every finite "
                            + "intervention word produces the same concept value from them.")),
                    Paragraph(Text(
                        "Applying one intervention merely prefixes that intervention to each "
                            + "word being observed. Equality of all trace coordinates is therefore "
                            + "preserved, making every dynamic-closure fiber intervention-invariant."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("closed-concept-fibers-persist-along-finite-words"),
                DeclarationHandle.Create(DeclarationPrefix + "runWord_preserves_fiber"),
                H("Closed concept fibers persist along finite intervention words"),
                StatementSource.FromAuthor(RunWordPreservesFiberFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If every individual intervention preserves the fibers of a candidate "
                            + "concept, then every finite composition of interventions preserves "
                            + "those fibers as well.")),
                    Paragraph(Text(
                        "The empty word changes no state. Extending a word by one intervention "
                            + "first uses closure for that step and then preserves equality through "
                            + "the remaining word, yielding the finite-word invariance."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("dynamic-closure-is-the-least-closed-refinement"),
                DeclarationHandle.Create(DeclarationPrefix + "dynamic_closure_is_least"),
                H("Dynamic closure is the least intervention-closed refinement"),
                StatementSource.FromAuthor(DynamicClosureLeastFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a candidate concept refine the original readout and have fibers "
                            + "preserved by every intervention. Finite-word invariance then shows "
                            + "that each complete intervention trace depends only on the candidate "
                            + "concept value.")),
                    Paragraph(Text(
                        "Consequently the dynamic-closure readout factors through every such "
                            + "candidate. Together with recovery of the original readout and the "
                            + "closure of its own fibers, this makes dynamic closure the least "
                            + "intervention-closed refinement."))),
                DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        F.Seq(F.Operatorname, F.Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula DynamicClosure(Formula concept, Formula intervene) =>
        Call("DynClosure", concept, intervene);

    private static Formula Closed(Formula concept, Formula intervene) =>
        Call("InterventionClosed", concept, intervene);

    private static Formula ConceptRefinementFormula()
    {
        Formula state = F.Id("X");
        Formula value = F.Id("A");
        Formula intervention = F.Id("U");
        Formula concept = F.Id("concept");
        Formula intervene = F.Id("intervene");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", TypeUniverse()),
                Bound("A", TypeUniverse()),
                Bound("U", TypeUniverse()),
                Bound("concept", Arrow(state, value)),
                Bound("intervene", Arrow(intervention, Arrow(state, state))),
            ],
            Refines(concept, DynamicClosure(concept, intervene))));
    }

    private static Formula DynamicClosureClosedFormula()
    {
        Formula state = F.Id("X");
        Formula value = F.Id("A");
        Formula intervention = F.Id("U");
        Formula concept = F.Id("concept");
        Formula intervene = F.Id("intervene");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", TypeUniverse()),
                Bound("A", TypeUniverse()),
                Bound("U", TypeUniverse()),
                Bound("concept", Arrow(state, value)),
                Bound("intervene", Arrow(intervention, Arrow(state, state))),
            ],
            Closed(DynamicClosure(concept, intervene), intervene)));
    }

    private static Formula RunWordPreservesFiberFormula()
    {
        Formula state = F.Id("X");
        Formula value = F.Id("B");
        Formula intervention = F.Id("U");
        Formula candidate = F.Id("candidate");
        Formula intervene = F.Id("intervene");
        Formula word = F.Id("word");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula leftValue = Apply(candidate, left);
        Formula rightValue = Apply(candidate, right);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", TypeUniverse()),
                Bound("B", TypeUniverse()),
                Bound("U", TypeUniverse()),
                Bound("candidate", Arrow(state, value)),
                Bound("intervene", Arrow(intervention, Arrow(state, state))),
            ],
            Implies(
                Closed(candidate, intervene),
                new Formula.BindMany(
                    FormulaQuantifier.ForAll,
                    [
                        Bound("word", Call("List", intervention)),
                        Bound("x", state),
                        Bound("y", state),
                    ],
                    Implies(
                        Equal(leftValue, rightValue),
                        Equal(
                            Apply(
                                candidate,
                                Call("runWord", intervene, word, left)),
                            Apply(
                                candidate,
                                Call("runWord", intervene, word, right))))))));
    }

    private static Formula DynamicClosureLeastFormula()
    {
        Formula state = F.Id("X");
        Formula value = F.Id("A");
        Formula intervention = F.Id("U");
        Formula candidateValue = F.Id("B");
        Formula concept = F.Id("concept");
        Formula intervene = F.Id("intervene");
        Formula candidate = F.Id("candidate");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", TypeUniverse()),
                Bound("A", TypeUniverse()),
                Bound("U", TypeUniverse()),
                Bound("B", TypeUniverse()),
                Bound("concept", Arrow(state, value)),
                Bound("intervene", Arrow(intervention, Arrow(state, state))),
                Bound("candidate", Arrow(state, candidateValue)),
            ],
            Implies(
                And(
                    Refines(concept, candidate),
                    Closed(candidate, intervene)),
                Refines(DynamicClosure(concept, intervene), candidate))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
