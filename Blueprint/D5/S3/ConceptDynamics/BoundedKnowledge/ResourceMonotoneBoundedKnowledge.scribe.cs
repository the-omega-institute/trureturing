using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.BoundedKnowledge;

internal sealed class ResourceMonotoneBoundedKnowledgeDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/BoundedKnowledge/ResourceMonotoneBoundedKnowledge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform bounded knowledge is monotone in resources and refines structural knowledge.",
        H("Resource-Monotone Bounded Knowledge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("resource-monotone-bounded-knowledge"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "resource_monotone_bounded_knowledge"),
                H("Bounded knowledge is monotone in the resource budget"),
                StatementSource.FromAuthor(ResourceMonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A budget r exposes a set P(r) of classifiers on evidence values. "
                            + "The hypothesis that P is monotone means that every classifier "
                            + "available at r remains available at each larger budget s.")),
                    Paragraph(Text(
                        "Bounded knowledge supplies an admissible true anchor and one classifier "
                            + "that decides the predicate uniformly from the evidence readout. "
                            + "When r is at most s, monotonicity transports that classifier to "
                            + "P(s), while the anchor and uniformity witnesses are unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-knowledge-implies-structural-knowledge"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "bounded_knowledge_implies_structural_knowledge"),
                H("Bounded knowledge implies structural knowledge"),
                StatementSource.FromAuthor(StructuralConsequenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A bounded classifier depends only on the evidence value. Two states in "
                            + "the same evidence fiber therefore receive the same classifier "
                            + "output, so the predicate has the same truth value at both states.")),
                    Paragraph(Text(
                        "The admissibility and truth clauses at the anchor pass through directly. "
                            + "The uniform classifier supplies the remaining fiber-constancy "
                            + "clause of structural knowledge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("structural-knowledge-not-bounded-counterexample"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "structural_knowledge_not_bounded_counterexample"),
                H("Structural knowledge need not be bounded knowledge"),
                StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The witness uses Boolean states, the one-point Unit evidence type, and "
                            + "constant-true admissibility and predicate functions. The predicate "
                            + "is constant on the sole evidence fiber, so structural knowledge "
                            + "holds at the anchor true.")),
                    Paragraph(Text(
                        "The resource type is Nat and every budget exposes the empty set of "
                            + "classifiers Unit -> Prop. In particular, budget zero has no uniform "
                            + "classifier, so bounded knowledge fails. This concrete witness "
                            + "disproves the converse implication."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula ResourceMonotonicityFormula()
    {
        Formula state = F.Id("X");
        Formula evidenceType = F.Id("B");
        Formula resource = F.Id("R");
        Formula programs = F.Id("P");
        Formula admissible = F.Id("A");
        Formula evidence = F.Id("e");
        Formula predicate = F.Id("K");
        Formula anchor = F.Id("a");
        Formula lower = F.Id("r");
        Formula upper = F.Id("s");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = F.Id("Prop");
        Formula classifier = Arrow(evidenceType, proposition);
        Formula programSet = Call("Set", classifier);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, evidenceType, Comma, Sp,
            resource, Colon, Sp, type, Comma, Esc,
            Call("Preorder", resource), Comma, Sp,
            programs, Colon, Sp, Arrow(resource, programSet), Comma, Esc,
            Call("Monotone", programs), Comma, Sp,
            admissible, Colon, Sp, Arrow(state, proposition), Comma, Sp,
            evidence, Colon, Sp, Arrow(state, evidenceType), Comma, Esc,
            predicate, Colon, Sp, Arrow(state, proposition), Comma, Sp,
            anchor, Colon, Sp, state, Comma, Sp,
            lower, Comma, Sp, upper, Colon, Sp, resource, Comma, Esc,
            lower, Sp, Leq, Sp, upper, Sp, Rightarrow, Sp,
            Bounded(programs, admissible, evidence, predicate, anchor, lower),
            Sp, Rightarrow, Sp,
            Bounded(programs, admissible, evidence, predicate, anchor, upper), Dot));
    }

    private static Formula StructuralConsequenceFormula()
    {
        Formula state = F.Id("X");
        Formula evidenceType = F.Id("B");
        Formula resource = F.Id("R");
        Formula programs = F.Id("P");
        Formula admissible = F.Id("A");
        Formula evidence = F.Id("e");
        Formula predicate = F.Id("K");
        Formula anchor = F.Id("a");
        Formula budget = F.Id("r");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = F.Id("Prop");
        Formula programSet = Call("Set", Arrow(evidenceType, proposition));

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, evidenceType, Comma, Sp,
            resource, Colon, Sp, type, Comma, Esc,
            programs, Colon, Sp, Arrow(resource, programSet), Comma, Sp,
            admissible, Colon, Sp, Arrow(state, proposition), Comma, Sp,
            evidence, Colon, Sp, Arrow(state, evidenceType), Comma, Esc,
            predicate, Colon, Sp, Arrow(state, proposition), Comma, Sp,
            anchor, Colon, Sp, state, Comma, Sp,
            budget, Colon, Sp, resource, Comma, Esc,
            Bounded(programs, admissible, evidence, predicate, anchor, budget),
            Sp, Rightarrow, Sp,
            Structural(admissible, evidence, predicate, anchor), Dot));
    }

    private static Formula CounterexampleFormula()
    {
        Formula state = F.Id("X");
        Formula evidenceType = F.Id("B");
        Formula resource = F.Id("R");
        Formula emptyPrograms = Call("const", Emptyset);
        Formula alwaysTrue = Call("const", F.Id("True"));
        Formula unitEvidence = Call("const", F.Id("unit"));
        Formula anchor = F.Id("true");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            state, Sp, Eq, Sp, F.Id("Bool"), Comma, Sp,
            evidenceType, Sp, Eq, Sp, F.Id("Unit"), Comma, Sp,
            resource, Sp, Eq, Sp, F.Id("Nat"), Comma, RowBreak, Grp(),
            Structural(alwaysTrue, unitEvidence, alwaysTrue, anchor), Sp, Land, Sp,
            Neg, Sp,
            Bounded(
                emptyPrograms,
                alwaysTrue,
                unitEvidence,
                alwaysTrue,
                anchor,
                D(0)),
            Dot, End, Grp(F.Id("gathered"))));
    }

    private static Formula Bounded(
        Formula programs,
        Formula admissible,
        Formula evidence,
        Formula predicate,
        Formula anchor,
        Formula budget) =>
        Call(
            "boundedKnowledge",
            programs,
            admissible,
            evidence,
            predicate,
            anchor,
            budget);

    private static Formula Structural(
        Formula admissible,
        Formula evidence,
        Formula predicate,
        Formula anchor) =>
        Call("structuralKnowledge", admissible, evidence, predicate, anchor);
}
