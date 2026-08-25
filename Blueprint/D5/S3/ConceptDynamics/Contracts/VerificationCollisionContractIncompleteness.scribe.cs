using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Contracts;

internal sealed class VerificationCollisionContractIncompletenessDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Contracts/VerificationCollisionContractIncompleteness."
            + "verification_collision_contract_incomplete";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A verification interface cannot implement an ideal obligation that varies "
            + "inside one verification fiber.",
        H("Verification Collision Contract Incompleteness"),
        Blocks(Describe.Lean(
            DescribeId.Create("verification-collision-contract-incompleteness"),
            DeclarationHandle.Create(Declaration),
            H("Unverifiable states make exact contracts incomplete"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The public primitives are a state verification map V and an ideal "
                        + "obligation map O. A verifiable contract is a function on the "
                        + "verification output.")),
                Paragraph(Text(
                    "If x and y have the same verification output, every contract assigns "
                        + "them the same implemented obligation. That equality contradicts "
                        + "the supplied inequality between their ideal obligations.")),
                Paragraph(Text(
                    "The result formalizes an interface limitation rather than a missing "
                        + "contract clause: no function of the available verification "
                        + "output can equal O on every state.")),
                Paragraph(Text(
                    "The proof directly applies the arbitrary-carrier factorization half "
                        + "of the existing informed-disclosure theorem."))),
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
        Formula state = F.Id("State");
        Formula verificationValue = F.Id("Verification");
        Formula obligationValue = F.Id("Obligation");
        Formula verification = F.Id("V");
        Formula obligation = F.Id("O");
        Formula contract = F.Id("c");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, verificationValue, Comma, Sp,
            obligationValue, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            verification, Colon, Sp, state, Sp, To, Sp, verificationValue,
            Comma, Sp,
            obligation, Colon, Sp, state, Sp, To, Sp, obligationValue,
            Comma, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma,
            RowBreak, Grp(),
            Apply(verification, x), Sp, Eq, Sp, Apply(verification, y),
            Sp, Land, Sp,
            Apply(obligation, x), Sp, Neq, Sp, Apply(obligation, y),
            Sp, Rightarrow,
            RowBreak, Grp(),
            Neg, Sp, Exists, Sp, contract, Colon, Sp,
            verificationValue, Sp, To, Sp, obligationValue, Comma, Sp,
            obligation, Sp, Eq, Sp, contract, Sp, Circ, Sp, verification, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
