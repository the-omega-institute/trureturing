using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteExhaustionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Boolean search results are reflected into exact universal "
            + "validity and unsatisfiability statements.",
        H("Finite Exhaustion Certificates"),
        Blocks(Describe.Lean(
            DescribeId.Create("successful-exhaustive-refutation-excludes-every-witness"),
            DeclarationHandle.Create(
                "D5/S0/Certificates/FiniteExhaustion.unsatisfiable_of_exhaustive_check"),
            H("A successful exhaustive refutation excludes every witness"),
            StatementSource.FromAuthor(Disp(Seq(
                Call("exhaustiveUnsatCheck", F.Id("P")),
                Sp, Eq, Sp, F.Id("true"), Sp, Rightarrow, Sp,
                Neg, Sp, Exists, Sp, F.Id("x"), Comma, Sp,
                F.Id("P"), Open, F.Id("x"), Close,
                Sp, Eq, Sp, F.Id("true"), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The checker uses the finite decidability instance to evaluate whether a Boolean predicate is false on every point of its finite domain.")),
                Paragraph(Text(
                    "The reflection theorem identifies the returned Boolean with the corresponding universal proposition.")),
                Paragraph(Text(
                    "A true refutation result can therefore be eliminated inside Lean as a proof that no satisfying assignment exists."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
