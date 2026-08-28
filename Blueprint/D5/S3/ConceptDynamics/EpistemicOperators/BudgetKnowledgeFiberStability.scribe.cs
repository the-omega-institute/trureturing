using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.EpistemicOperators;

internal sealed class BudgetKnowledgeFiberStabilityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/EpistemicOperators/BudgetKnowledgeFiberStability."
            + "budget_knowledge_fiber_stability";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Budget knowledge is exactly constancy on every joint-readout fiber.",
        H("Budget Knowledge Fiber Stability"),
        Blocks(Describe.Lean(
            DescribeId.Create("budget-knowledge-is-exactly-fiber-constant"),
            DeclarationHandle.Create(Declaration),
            H("Budget knowledge is characterized by fiber stability"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state anchor is part of the prime-observer model. It supplies "
                        + "an actual predicate value, so a fiber-constant predicate can be "
                        + "extended from the realized readouts to the full readout type.")),
                Paragraph(Text(
                    "Budget knowledge uses the source definition: there is an observable "
                        + "on the joint-readout type whose pullback is the predicate. The "
                        + "displayed equivalence has one clause in each direction and no "
                        + "admissibility or finiteness premise.")),
                Paragraph(Text(
                    "The proof applies the exact repository factorization criterion, whose "
                        + "factorization step in turn reuses pinned Mathlib's "
                        + "Function.factorsThrough_iff."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula state = F.Id("X");
        Formula observation = F.Id("O");
        Formula value = F.Id("B");
        Formula anchor = F.Id("anchor");
        Formula readout = F.Id("q");
        Formula predicate = F.Id("P");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula knows = Apply(
            Seq(Operatorname, Grp(F.Id("Knows"))), readout, predicate);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, observation, Comma, Sp, value,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            anchor, Colon, Sp, state, Comma, Sp,
            readout, Colon, Sp, state, Sp, To, Sp, observation, Comma, Sp,
            predicate, Colon, Sp, state, Sp, To, Sp, value, Comma, RowBreak, Grp(),
            knows, Sp, Leftrightarrow, Sp,
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            Apply(readout, x), Sp, Eq, Sp, Apply(readout, y), Sp,
            Rightarrow, Sp, Apply(predicate, x), Sp, Eq, Sp, Apply(predicate, y), Dot));
    }
}
