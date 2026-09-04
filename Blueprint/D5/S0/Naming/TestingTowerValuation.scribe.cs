using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class TestingTowerValuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Naming/TestingTowerValuation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite tables and program codes receive the testing tower's concrete partial valuation.",
        H("Testing Tower Valuation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("program-definedness-is-halting"),
                DeclarationHandle.Create(Prefix + "program_assignment_defined_iff_halts"),
                H("Program-name definedness is halting"),
                StatementSource.FromAuthor(ProgramDomainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A natural-number program name is decoded by Mathlib's denumerable code "
                        + "bijection and evaluated by Nat.Partrec.Code.eval on the supplied input. Its "
                        + "assignment is present exactly on the evaluator's domain."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("program-definedness-is-not-computable"),
                DeclarationHandle.Create(Prefix + "program_name_domain_not_computable"),
                H("Program-name definedness is not computable"),
                StatementSource.FromAuthor(DomainNoncomputableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Restricting natural-number names along the canonical encoding of partial-"
                        + "recursive codes recovers Mathlib's halting predicate. A computable "
                        + "definedness test would contradict the pinned halting theorem."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Naming/Conservation/TestingTowerMembership"))]));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula PrefixFormula(Formula conclusion)
    {
        Formula output = F.Id("O");
        Formula defaultOutput = F.Id("o0");
        Formula decoder = F.Id("decode");
        Formula programInput = F.Id("input");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula sequenceType = Arrow(naturals, output);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, output, Colon, Sp, type, Comma, Sp,
            Forall, Sp, defaultOutput, Colon, Sp, output, Comma, RowBreak, Grp(),
            Forall, Sp, decoder, Colon, Sp, Arrow(naturals, sequenceType), Comma, RowBreak, Grp(),
            Forall, Sp, programInput, Colon, Sp, naturals, Comma, RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ProgramDomainFormula()
    {
        Formula defaultOutput = F.Id("o0");
        Formula decoder = F.Id("decode");
        Formula programInput = F.Id("input");
        Formula program = F.Id("p");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula assignment = Call(
            "testingAssignment", defaultOutput, decoder, programInput, Call("inr", program));
        Formula halting = Call(
            "Dom", Call("eval", Call("ofNatCode", program), programInput));

        return PrefixFormula(Seq(
            Forall, Sp, program, Colon, Sp, naturals, Comma, RowBreak, Grp(),
            Call("isSome", assignment), Sp, Iff, Sp, halting));
    }

    private static Formula DomainNoncomputableFormula()
    {
        Formula defaultOutput = F.Id("o0");
        Formula decoder = F.Id("decode");
        Formula programInput = F.Id("input");
        Formula code = F.Id("c");
        Formula encodedAssignment = Call(
            "testingAssignment", defaultOutput, decoder, programInput,
            Call("inr", Call("encodeCode", code)));
        Formula predicate = Seq(
            Open, code, Colon, Sp, F.Id("PartrecCode"), Sp, Mapsto, Sp,
            Call("isSome", encodedAssignment), Close);

        return PrefixFormula(Seq(
            Neg, Sp, Call("ComputablePred", predicate)));
    }
}
