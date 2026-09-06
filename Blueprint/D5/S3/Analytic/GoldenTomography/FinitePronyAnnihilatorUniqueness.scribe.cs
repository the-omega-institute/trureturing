using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePronyAnnihilatorUniquenessDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The true finite Prony annihilator is uniquely determined by a full recurrence window.",
        H("Finite Prony Annihilator Uniqueness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-unique-prony-annihilator-from-window"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/GoldenTomography/FinitePronyAnnihilatorUniqueness."
                        + "existsUnique_prony_annihilator_from_window"),
                H("The bounded monic recurrence polynomial is unique"),
                StatementSource.FromAuthor(UniquenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite exponential moment sequence with pairwise distinct nodes "
                            + "and nonzero weights, there is exactly one monic polynomial of "
                            + "degree at most the number of modes whose coefficient recurrence "
                            + "holds on the first matching number of shifts. It is the product "
                            + "of the linear factors determined by the true nodes.")),
                    Paragraph(Text(
                        "The proof first uses the recurrence window to identify every true node "
                            + "as a root. Pairwise coprimality of the distinct linear factors "
                            + "makes their product divide the candidate. Monicity and the degree "
                            + "bound then force equality with the true annihilator.")),
                    Paragraph(Text(
                        "This theorem establishes exact structural identifiability of the "
                            + "annihilator. It does not provide a numerical coefficient solver, "
                            + "a root-finding algorithm, confluent-mode recovery, or a noisy "
                            + "conditioning estimate."))),
                DescribeRole.Theorem)),
        []));

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

    private static Formula UniquenessFormula() => Disp(Seq(
        Call("Monic", F.Id("q")),
        Sp, Land, Sp,
        Call("deg", F.Id("q")), Sp, Leq, Sp, F.Id("m"),
        Sp, Land, Sp,
        Call("Rec", F.Id("q"), F.Id("c")),
        Sp, Iff, Sp,
        F.Id("q"), Sp, Eq, Sp, Call("A", F.Id("x"))));
}
