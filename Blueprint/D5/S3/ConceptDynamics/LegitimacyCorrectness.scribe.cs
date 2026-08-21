using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class LegitimacyCorrectnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Authorization provenance can pass while a result target fails.",
        H("Authorization and Factual Correctness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("authorized-process-can-fail-factually"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/LegitimacyCorrectness."
                        + "authorized_process_can_fail_factually"),
                H("Authorization does not imply factual correctness"),
                StatementSource.FromAuthor(SeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source separates two audits: authorization provenance checks "
                            + "the executed action against an authorization rule, while a result "
                            + "audit compares the actual result with its target.")),
                    Paragraph(Text(
                        "For every inhabited input, action, and pair of distinct results, the "
                            + "source primitives construct an authorized constant execution whose "
                            + "result audit fails. The authorization and result predicates are not "
                            + "defined from that failure.")),
                    Paragraph(Text(
                        "Repository searches found no exact separation theorem; the proof is the "
                            + "direct constant countermodel over the source carriers."))),
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

    private static Formula SeparationFormula()
    {
        Formula input = F.Id("I");
        Formula action = F.Id("A");
        Formula result = F.Id("R");
        Formula authorize = F.Id("authorize");
        Formula target = F.Id("target");
        Formula actual = F.Id("actual");
        Formula correctResult = new Formula.Subscript(F.Id("r"), F.Id("ok"));
        Formula incorrectResult = new Formula.Subscript(F.Id("r"), F.Id("bad"));
        Formula executed = Apply(
            Seq(Operatorname, Grp(F.Id("const"))), F.Id("a"));
        Formula audit = Apply(
            Seq(Operatorname, Grp(F.Id("authorizationAudit"))), authorize, executed);
        Formula resultAudit = Apply(
            Seq(Operatorname, Grp(F.Id("resultAudit"))), target, actual);
        Formula types = Seq(input, Comma, Sp, action, Comma, Sp, result,
            Colon, Sp, Operatorname, Grp(F.Id("Type")));
        Formula witness = Seq(
            Exists, Sp, authorize, Colon, Sp,
            Seq(input, Sp, To, Sp, action, Sp, To, Sp, Operatorname,
                Grp(F.Id("Prop"))), Comma, Sp,
            Exists, Sp, target, Comma, Sp, actual, Colon, Sp,
            Seq(input, Sp, To, Sp, result), Comma, Esc,
            audit, Sp, Land, Sp, Neg, Sp, resultAudit);
        return Disp(Seq(
            Forall, Sp, types, Comma, Sp,
            F.Id("i"), Colon, Sp, input, Comma, Sp,
            F.Id("a"), Colon, Sp, action, Comma, Sp,
            correctResult, Comma, Sp, incorrectResult, Colon, Sp, result, Comma, Sp,
            incorrectResult, Sp, Neq, Sp, correctResult, Sp, Rightarrow, Esc,
            witness, Dot));
    }
}
