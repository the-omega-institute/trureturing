using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Revision;

internal sealed class RevisionConflictNoncommutationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Revision/RevisionConflictNoncommutation."
            + "revision_conflict_noncommutation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reset-on-conflict revision is order-dependent on a concrete three-world model.",
        H("Revision Conflict Noncommutation"),
        Blocks(Describe.Lean(
            DescribeId.Create("revision-conflict-noncommutation"),
            DeclarationHandle.Create(Declaration),
            H("Reset-on-conflict revision need not commute"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let revision intersect the current admissible worlds with compatible "
                        + "evidence and reset to the evidence set after a total conflict. On "
                        + "the three-world carrier, take A = {0}, P = {1, 2}, and Q = {0, 1}.")),
                Paragraph(Text(
                    "Revising first by P and then by Q yields {1}; reversing the order yields "
                        + "{1, 2}. The two update paths are therefore unequal."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("A");
        Formula p = F.Id("P");
        Formula q = F.Id("Q");
        Formula setA = new Formula.SetLiteral([Num(0)]);
        Formula setP = new Formula.SetLiteral([Num(1), Num(2)]);
        Formula setQ = new Formula.SetLiteral([Num(0), Num(1)]);
        Formula setOne = new Formula.SetLiteral([Num(1)]);
        Formula qp = Call("Rev", q, Call("Rev", p, a));
        Formula pq = Call("Rev", p, Call("Rev", q, a));

        return Disp(Seq(
            a, Sp, Eq, Sp, setA, Comma, Sp,
            p, Sp, Eq, Sp, setP, Comma, Sp,
            q, Sp, Eq, Sp, setQ, Esc,
            Rightarrow, Sp,
            qp, Sp, Eq, Sp, setOne, Sp, Land, Sp,
            pq, Sp, Eq, Sp, setP, Sp, Land, Sp,
            qp, Sp, Neq, Sp, pq, Dot));
    }
}
