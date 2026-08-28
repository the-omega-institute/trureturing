using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class StrictRefinementCapabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Effective strict refinement creates a new question and a new differentiating policy.",
        H("Strict Refinement Capability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-refinement-capability"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/StrictRefinementCapability.strict_refinement_capability"),
                H("Strict refinement yields question and policy capability"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Effective concepts are represented by surjective readouts. Strict "
                            + "refinement is the public factorization relation from the existing "
                            + "ConceptDynamics order, together with failure of reverse refinement.")),
                    Paragraph(Text(
                        "The conclusion contains both source clauses: a Boolean question and a "
                            + "policy into the action set each have a unique factor through the finer "
                            + "readout and no factor through the coarser readout.")),
                    Paragraph(Text(
                        "The separating pair is obtained from strictness and effective readouts; the "
                            + "two distinct actions then provide the policy witnesses."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Compose(Formula left, Formula right) =>
        Seq(left, Sp, Circ, Sp, right);

    private static Formula Formula()
    {
        Formula source = F.Id("X");
        Formula coarseType = F.Id("C");
        Formula fineType = F.Id("D");
        Formula actionType = F.Id("U");
        Formula coarse = Subscript(F.Id("q"), F.Id("C"));
        Formula fine = Subscript(F.Id("q"), F.Id("D"));
        Formula question = F.Id("Q");
        Formula policy = F.Id("Pi");
        Formula factorQuestion = F.Id("a");
        Formula factorPolicy = F.Id("p");
        Formula actionZero = Subscript(F.Id("u"), D(0));
        Formula actionOne = Subscript(F.Id("u"), D(1));
        Formula strict = Call("StrictRefinement", coarse, fine);
        Formula questionCapability = Seq(
            Open, Exists, Sp, question, Colon, Sp, Arrow(source, F.Id("Bool")), Comma, Sp,
            Open,
            Seq(Open, Exists, Bang, Sp, factorQuestion, Colon, Sp, Arrow(fineType, F.Id("Bool")), Comma, Sp,
                question, Sp, Eq, Sp, Compose(factorQuestion, fine), Close),
            Sp, Land, Sp,
            Seq(Neg, Open, Exists, Sp, F.Id("b"), Colon, Sp, Arrow(coarseType, F.Id("Bool")), Comma, Sp,
                question, Sp, Eq, Sp, Compose(F.Id("b"), coarse), Close),
            Close, Close);
        Formula policyCapability = Seq(
            Open, Exists, Sp, policy, Colon, Sp, Arrow(source, actionType), Comma, Sp,
            Open,
            Seq(Open, Exists, Bang, Sp, factorPolicy, Colon, Sp, Arrow(fineType, actionType), Comma, Sp,
                policy, Sp, Eq, Sp, Compose(factorPolicy, fine), Close),
            Sp, Land, Sp,
            Seq(Neg, Open, Exists, Sp, F.Id("c"), Colon, Sp, Arrow(coarseType, actionType), Comma, Sp,
                policy, Sp, Eq, Sp, Compose(F.Id("c"), coarse), Close),
            Close, Close);

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, coarseType, Comma, Sp, fineType, Comma, Sp,
            actionType, Colon, Sp, F.Id("Type"), Comma, Esc,
            coarse, Colon, Sp, Arrow(source, coarseType), Comma, Sp,
            fine, Colon, Sp, Arrow(source, fineType), Comma, Sp,
            Call("Surjective", coarse), Sp, Land, Sp,
            Call("Surjective", fine), Sp, Land, Sp,
            strict, Sp, Land, Sp,
            Exists, Sp, actionZero, Colon, Sp, actionType, Comma, Sp,
            actionOne, Colon, Sp, actionType, Comma, Sp,
            actionZero, Sp, Neq, Sp, actionOne, Sp, Rightarrow, Sp,
            Open, questionCapability, Sp, Land, Sp, policyCapability, Close, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
