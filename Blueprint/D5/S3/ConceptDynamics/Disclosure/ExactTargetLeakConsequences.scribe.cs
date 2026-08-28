using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Disclosure;

internal sealed class ExactTargetLeakConsequencesDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Disclosure/ExactTargetLeakConsequences."
            + "exact_target_leak_consequences";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact realization forces its sensitive part and obstructs zero new leakage.",
        H("Consequences of Exact Target Leakage"),
        Blocks(Describe.Lean(
            DescribeId.Create("exact-target-leak-consequences"),
            DeclarationHandle.Create(Declaration),
            H("Exact realization forces and enlarges sensitive disclosure"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The target factors through the join of the public and added concepts. "
                        + "The forced part is explicitly the meet of target and sensitive, "
                        + "while the leak is the meet of the augmented public concept and "
                        + "the same sensitive concept.")),
                Paragraph(Text(
                    "The first conjunct is the forced-refinement theorem. The second states "
                        + "that structural no-new-leak is impossible whenever the forced part "
                        + "does not refine the named prior common part; the canonical predicate "
                        + "itself requires that prior readout to be the public-sensitive meet."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula state = F.Id("X");
        Formula publicType = F.Id("P");
        Formula addedType = F.Id("M");
        Formula sensitiveType = F.Id("S");
        Formula targetType = F.Id("E");
        Formula forcedType = F.Id("K");
        Formula leakType = F.Id("L");
        Formula beforeType = F.Id("Before");
        Formula publicConcept = F.Id("p");
        Formula added = F.Id("m");
        Formula sensitive = F.Id("s");
        Formula target = F.Id("e");
        Formula forcedPart = F.Id("k");
        Formula leak = F.Id("l");
        Formula before = F.Id("before");
        Formula augmented = Call("conceptJoin", publicConcept, added);
        Formula hypotheses = And(
            Call("Refines", target, augmented),
            And(
                Call("IsConceptMeet", target, sensitive, forcedPart),
                Call("IsConceptMeet", augmented, sensitive, leak)));
        Formula noNewLeakImpossible = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Before", type),
                Bound("before", Arrow(state, beforeType)),
            ],
            Implies(
                new Formula.Not(Call("Refines", forcedPart, before)),
                new Formula.Not(Call("StructurallyNoNewLeak",
                    publicConcept, added, sensitive, before, leak))));
        Formula conclusion = And(
            Call("Refines", forcedPart, leak),
            noNewLeakImpossible);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("P", type),
                Bound("M", type),
                Bound("S", type),
                Bound("E", type),
                Bound("K", type),
                Bound("L", type),
                Bound("p", Arrow(state, publicType)),
                Bound("m", Arrow(state, addedType)),
                Bound("s", Arrow(state, sensitiveType)),
                Bound("e", Arrow(state, targetType)),
                Bound("k", Arrow(state, forcedType)),
                Bound("l", Arrow(state, leakType)),
            ],
            Implies(hypotheses, conclusion)));
    }
}
