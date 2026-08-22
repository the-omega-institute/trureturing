using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Rights;

internal sealed class ConflictRepairHittingSetDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Rights/ConflictRepairHittingSet.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every successful downward-closed conflict repair intersects every conflicting core "
            + "contained in the original rights.",
        H("Conflict Repairs Are Hitting Sets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-successful-repair-hits-a-conflict-core"),
                DeclarationHandle.Create(DeclarationPrefix + "repair_must_hit_conflict_core"),
                H("A successful repair hits a conflict core"),
                StatementSource.FromAuthor(RepairMustHitConflictCoreFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume satisfiability is preserved when rights are removed. If a "
                            + "conflicting core lies inside the original rights and deleting the "
                            + "modified rights leaves a satisfiable remainder, then at least one "
                            + "modified right belongs to that core.")),
                    Paragraph(Text(
                        "Indeed, if the modification missed the core, the entire core would remain "
                            + "inside the repaired set. Downward closure would then make the core "
                            + "satisfiable, contradicting its conflict. Neither finiteness nor "
                            + "minimality of the core is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-successful-repair-hits-every-conflict-core"),
                DeclarationHandle.Create(DeclarationPrefix + "repair_hits_every_conflict_core"),
                H("A successful repair hits every conflict core"),
                StatementSource.FromAuthor(RepairHitsEveryConflictCoreFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a modification whose removal makes the original rights satisfiable. For "
                        + "every unsatisfiable subset of the original rights, the single-core "
                        + "obstruction forces a nonempty intersection with the modification. Thus "
                        + "one successful repair is a hitting set for the entire family of conflict "
                        + "cores present in the original rights."))),
                DescribeRole.Lemma))));

    private static Formula RepairMustHitConflictCoreFormula()
    {
        Formula rightType = F.Id("Right");
        Formula satisfiable = F.Id("Satisfiable");
        Formula rights = F.Id("rights");
        Formula modified = F.Id("modified");
        Formula core = F.Id("core");
        Formula setOfRights = Call("Set", rightType);
        Formula hypotheses = And(
            Call("DownwardClosed", satisfiable),
            And(
                SubsetOf(core, rights),
                And(
                    new Formula.Not(Apply(satisfiable, core)),
                    Apply(satisfiable, Difference(rights, modified)))));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Right", F.Id("Type")),
                Bound("Satisfiable", Arrow(setOfRights, F.Id("Prop"))),
                Bound("rights", setOfRights),
                Bound("modified", setOfRights),
                Bound("core", setOfRights),
            ],
            Implies(hypotheses, Nonempty(Intersection(modified, core)))));
    }

    private static Formula RepairHitsEveryConflictCoreFormula()
    {
        Formula rightType = F.Id("Right");
        Formula satisfiable = F.Id("Satisfiable");
        Formula rights = F.Id("rights");
        Formula modified = F.Id("modified");
        Formula core = F.Id("core");
        Formula setOfRights = Call("Set", rightType);
        Formula hypotheses = And(
            Call("DownwardClosed", satisfiable),
            And(
                Apply(satisfiable, Difference(rights, modified)),
                And(
                    SubsetOf(core, rights),
                    new Formula.Not(Apply(satisfiable, core)))));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Right", F.Id("Type")),
                Bound("Satisfiable", Arrow(setOfRights, F.Id("Prop"))),
                Bound("rights", setOfRights),
                Bound("modified", setOfRights),
                Bound("core", setOfRights),
            ],
            Implies(hypotheses, Nonempty(Intersection(modified, core)))));
    }

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

    private static Formula SubsetOf(Formula subset, Formula superset) =>
        new Formula.Relation(subset, FormulaRelationOperator.SubsetOf, superset);

    private static Formula Difference(Formula source, Formula removed) =>
        Call("difference", source, removed);

    private static Formula Intersection(Formula left, Formula right) =>
        Call("intersection", left, right);

    private static Formula Nonempty(Formula set) =>
        Call("Nonempty", set);
}
