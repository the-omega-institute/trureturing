using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ErrorExponents;

internal sealed class FiniteRepetitionLawKernelDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite independent repetition amplifies genuine differences without separating equal one-shot laws.",
        H("Finite Repetition Preserves the Law Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-repetition-amplifies-without-crossing-law-kernel"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/ErrorExponents/FiniteRepetitionLawKernel."
                        + "finite_repetition_amplifies_without_crossing_law_kernel"),
                H("Finite repetition amplifies without crossing the law kernel"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The repeated experiment is the repository's canonical independent "
                            + "product law. Exact multiplicativity turns its Bhattacharyya "
                            + "affinity into the n-th power of the one-copy affinity, which is "
                            + "strictly smaller when at least two copies are taken and the "
                            + "one-copy affinity lies strictly between zero and one.")),
                    Paragraph(Text(
                        "For the equality clause, summing a positive-copy product law over all "
                            + "tail coordinates recovers its first marginal because each tail "
                            + "law has total mass one. Equality of repeated laws therefore "
                            + "forces equality of the one-shot laws; the reverse direction is "
                            + "preserved by the same canonical product construction."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula>
        {
            Operatorname, Grp(F.Id(name)), Open
        };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("S");
        Formula outcome = F.Id("O");
        Formula law = F.Id("K");
        Formula firstState = F.Id("x");
        Formula secondState = F.Id("y");
        Formula copies = F.Id("n");
        Formula index = F.Id("i");
        Formula firstLaw = new Formula.Subscript(law, firstState);
        Formula secondLaw = new Formula.Subscript(law, secondState);
        Formula firstAt = Call("K", firstState, index);
        Formula secondAt = Call("K", secondState, index);
        Formula affinity = Call("Bhattacharyya", firstLaw, secondLaw);
        Formula firstPower = Call("IidPower", firstLaw, copies);
        Formula secondPower = Call("IidPower", secondLaw, copies);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, outcome, Colon, Sp, Call("Type"), Comma, Sp,
            OpenBracket, Call("Fintype", outcome), CloseBracket, Comma, RowBreak, Grp(),
            Forall, Sp, law, Colon, Sp, state, Sp, To, Sp, outcome, Sp, To, Sp,
            Mathbb, Grp(F.Id("R")), Comma, RowBreak, Grp(),
            Forall, Sp, firstState, Comma, Sp, secondState, Colon, Sp, state, Comma, Sp,
            copies, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, RowBreak, Grp(),
            Open,
            Open, Forall, Sp, index, Comma, Sp, D(0), Sp, Le, Sp, firstAt, Close,
            Sp, Land, Sp, Sum, Underscore, Grp(index), Sp, firstAt, Sp, Eq, Sp, D(1),
            Close, Sp, Land, RowBreak, Grp(),
            Open,
            Open, Forall, Sp, index, Comma, Sp, D(0), Sp, Le, Sp, secondAt, Close,
            Sp, Land, Sp, Sum, Underscore, Grp(index), Sp, secondAt, Sp, Eq, Sp, D(1),
            Close, Sp, Land, Sp, D(0), Sp, Lt, Sp, copies, Sp, Rightarrow, RowBreak, Grp(),
            OpenBracket,
            Open,
            Open, D(1), Sp, Lt, Sp, copies, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, affinity, Sp, Land, Sp, affinity, Sp, Lt, Sp, D(1), Close,
            Sp, Rightarrow, Sp,
            Call("Bhattacharyya", firstPower, secondPower), Sp, Lt, Sp, affinity,
            Close, Sp, Land, RowBreak, Grp(),
            Open, firstPower, Sp, Eq, Sp, secondPower, Sp, Iff, Sp,
            firstLaw, Sp, Eq, Sp, secondLaw, Close,
            CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
