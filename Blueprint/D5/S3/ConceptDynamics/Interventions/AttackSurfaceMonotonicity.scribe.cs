using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interventions;

internal sealed class AttackSurfaceMonotonicityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Interventions/AttackSurfaceMonotonicity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permission expansion enlarges reachable states, preserves bad-state inclusion, "
            + "and can enlarge both permissions and reachability strictly.",
        H("Attack Surface Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("permission-expansion-enlarges-reachability"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "reach_monotone_in_permissions"),
                H("Permission expansion enlarges reachability"),
                StatementSource.FromAuthor(ReachMonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a permission-indexed transition relation, the reachable set from "
                            + "a fixed start state contains every state connected by a finite "
                            + "chain whose permissions all lie in the allowed set.")),
                    Paragraph(Text(
                        "If one permission set is contained in another, every transition "
                            + "admitted by the smaller set remains admitted by the larger set. "
                            + "The same finite chains therefore witness inclusion of the two "
                            + "reachable sets.")),
                    Paragraph(Text(
                        "This is covariance of attack surface with permission: adding allowed "
                            + "actions cannot remove a state that was already reachable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bad-state-reachability-remains-monotone"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "bad_state_reach_monotone"),
                H("Bad-state reachability remains monotone"),
                StatementSource.FromAuthor(BadStateMonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix any collection of bad states. Expanding the allowed permissions "
                            + "preserves every previously reachable bad state, so intersecting "
                            + "both attack surfaces with that collection preserves inclusion.")),
                    Paragraph(Text(
                        "The bad-state predicate contributes no additional transition behavior; "
                            + "it simply filters the two reachable sets by the same criterion."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("boolean-negation-witnesses-strict-growth"),
                DeclarationHandle.Create(DeclarationPrefix + "strict_growth_witness"),
                H("Boolean negation witnesses strict growth"),
                StatementSource.FromAuthor(StrictGrowthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use Boolean functions as permissions and let a permitted function move "
                            + "a source state to its value. Starting from false, the empty "
                            + "permission set reaches only false, while the singleton permission "
                            + "set containing negation also reaches true.")),
                    Paragraph(Text(
                        "Thus the empty set is a proper subset of the negation permission set, "
                            + "and its reachable set is a proper subset of the enlarged reachable "
                            + "set. Permission growth and attack-surface growth can therefore both "
                            + "be strict."))),
                DescribeRole.Lemma))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula SetOf(Formula carrier) =>
        Call("Set", carrier);

    private static Formula Reach(Formula step, Formula allowed, Formula start) =>
        Call("Reach", step, allowed, start);

    private static Formula SubsetOf(Formula subset, Formula superset) =>
        new Formula.Relation(subset, FormulaRelationOperator.SubsetOf, superset);

    private static Formula StrictSubsetOf(Formula subset, Formula superset) =>
        Seq(subset, Sp, Subset, Sp, superset);

    private static Formula ImpliesFormula(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ReachMonotonicityFormula()
    {
        Formula stateType = F.Id("State");
        Formula permissionType = F.Id("Permission");
        Formula proposition = F.Id("Prop");
        Formula step = F.Id("step");
        Formula smaller = F.Id("P");
        Formula larger = F.Id("Q");
        Formula start = F.Id("start");
        Formula stepType = Arrow(
            permissionType,
            Arrow(stateType, Arrow(stateType, proposition)));
        Formula permissionSet = SetOf(permissionType);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("State", TypeUniverse()),
                Bound("Permission", TypeUniverse()),
                Bound("step", stepType),
                Bound("P", permissionSet),
                Bound("Q", permissionSet),
                Bound("start", stateType),
            ],
            ImpliesFormula(
                SubsetOf(smaller, larger),
                SubsetOf(
                    Reach(step, smaller, start),
                    Reach(step, larger, start)))));
    }

    private static Formula BadStateMonotonicityFormula()
    {
        Formula stateType = F.Id("State");
        Formula permissionType = F.Id("Permission");
        Formula proposition = F.Id("Prop");
        Formula step = F.Id("step");
        Formula smaller = F.Id("P");
        Formula larger = F.Id("Q");
        Formula start = F.Id("start");
        Formula bad = F.Id("bad");
        Formula stepType = Arrow(
            permissionType,
            Arrow(stateType, Arrow(stateType, proposition)));
        Formula permissionSet = SetOf(permissionType);
        Formula badStates = SetOf(stateType);
        Formula smallerBadReach = Call(
            "intersection",
            Reach(step, smaller, start),
            bad);
        Formula largerBadReach = Call(
            "intersection",
            Reach(step, larger, start),
            bad);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("State", TypeUniverse()),
                Bound("Permission", TypeUniverse()),
                Bound("step", stepType),
                Bound("P", permissionSet),
                Bound("Q", permissionSet),
                Bound("start", stateType),
                Bound("bad", badStates),
            ],
            ImpliesFormula(
                SubsetOf(smaller, larger),
                SubsetOf(smallerBadReach, largerBadReach))));
    }

    private static Formula StrictGrowthFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula permission = F.Id("permission");
        Formula source = F.Id("source");
        Formula target = F.Id("target");
        Formula smaller = F.Id("P");
        Formula larger = F.Id("Q");
        Formula start = F.Id("false");
        Formula booleanPermissions = SetOf(Arrow(boolean, boolean));
        Formula evaluationStep = Seq(
            Open,
            permission,
            Comma,
            Sp,
            source,
            Comma,
            Sp,
            target,
            Close,
            Sp,
            Mapsto,
            Sp,
            new Formula.Apply(permission, [source]),
            Sp,
            Eq,
            Sp,
            target);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("P", booleanPermissions), Bound("Q", booleanPermissions)],
            And(
                StrictSubsetOf(smaller, larger),
                StrictSubsetOf(
                    Reach(evaluationStep, smaller, start),
                    Reach(evaluationStep, larger, start)))));
    }
}
