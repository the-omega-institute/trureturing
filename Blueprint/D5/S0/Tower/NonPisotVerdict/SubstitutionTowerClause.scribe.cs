using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisotVerdict;

internal sealed class SubstitutionTowerClauseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var sixty = Call("Nonempty",
            Call("tribonacciBackwardSurvivor",
                Id("tribonacciStrictSurvivorSet"), Num(60)));

        const string declarationPrefix =
            "D5/S0/Tower/NonPisotVerdict/SubstitutionTowerClause.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The substitution-tower clause, its assertions conjoined, including the refutation "
                + "of the one that is false.",
            H("Substitution Tower Clause"),
            Blocks(
                Paragraph(Text(
                    "The clause makes several assertions at once: that the gap refinement of a "
                        + "tower is that tower's own substitution, that the champion is the "
                        + "ergodic optimum of the corresponding expanding map, a closed form for "
                        + "the champion value with its numerics, the boundary limit, and the "
                        + "behaviour past the Pisot boundary. Each already had a proof somewhere "
                        + "in the tree. What did not exist was any statement that they hold "
                        + "together and stand for one clause.")),
                Paragraph(Text(
                    "One of the assertions is false. The clause claims the strict forbidden "
                        + "region empties by depth sixty; the backward survivor set at that very "
                        + "depth is nonempty. The conjunction carries the refutation rather than "
                        + "the claim, and rather than a weakened restatement that would be true. "
                        + "Rewriting that conjunct back into the clause's own wording makes this "
                        + "module fail to compile, which is the property a false sentence should "
                        + "have once it has been settled.")),
                Paragraph(Text(
                    "Assembling it also produced something no single module could see. This is "
                        + "the first module to bring two of the frontier modules into one scope, "
                        + "and doing so revealed that they define the same spectrum name with "
                        + "different underlying value maps. A consumer opening only one of them "
                        + "gets a different function under that name with no diagnostic.")),
                Describe.Lean(
                    DescribeId.Create("the-substitution-tower-clause"),
                    DeclarationHandle.Create(declarationPrefix + "substitution_tower_clause"),
                    H("The substitution tower clause"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(sixty)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The displayed conjunct is the refutation, shown because it is the one "
                            + "that contradicts the source. Nothing in this module is proved for "
                            + "the first time; every conjunct is an existing theorem applied "
                            + "without restatement."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/NonPisotVerdict/NotEventuallyPeriodic")),
            ]));
    }
}
