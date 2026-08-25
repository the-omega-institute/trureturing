using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class FinitePrimePowerQuotientCompletenessDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite prime-power quotient completeness is equivalent to nilpotence.",
        H("Finite Prime-Power Quotient Completeness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prime-power-quotient-completeness-tfae"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/PrimePowers/"
                        + "FinitePrimePowerQuotientCompleteness."
                        + "finite_prime_power_quotient_completeness_tfae"),
                H("Finite prime-power quotient completeness characterizes nilpotence"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite group G, index the normal subgroups whose canonical "
                            + "quotients are p-groups for some prime p. Their quotient maps "
                            + "construct the joint observer, and their kernels construct the "
                            + "prime-power residual by intersection.")),
                    Paragraph(Text(
                        "The theorem states all five equivalent conditions publicly: joint "
                            + "faithfulness, trivial residual, an embedding into a finite "
                            + "product of finite p-groups, nilpotence, and decomposition as "
                            + "the product of the Sylow subgroups.")),
                    Paragraph(Text(
                        "The quotient observer has the displayed residual as its kernel. A "
                            + "faithful observer itself gives the finite product embedding; "
                            + "conversely, coordinate kernels turn any such embedding into "
                            + "joint quotient faithfulness.")),
                    Paragraph(Text(
                        "Finite products of p-groups are nilpotent and their subgroups remain "
                            + "nilpotent. Mathlib's finite nilpotence theorem supplies the exact "
                            + "equivalence with the Sylow direct-product decomposition."))),
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

    private static Formula TheoremFormula()
    {
        Formula group = F.Id("G");
        Formula observer = Call("primePowerQuotientObserver", group);
        Formula residual = Call("primePowerResidual", group);
        Formula trivial = Call("trivialSubgroup", group);
        Formula factors = Call("FinitePGroupFactors");

        return Disp(Seq(
            Operatorname, Grp(F.Id("TFAE")), Open,
            Call("Injective", observer), Comma, RowBreak, Grp(),
            Equal(residual, trivial), Comma, RowBreak, Grp(),
            Call("Embeds", group, Call("FiniteProduct", factors)),
            Comma, RowBreak, Grp(),
            Call("Nilpotent", group), Comma, RowBreak, Grp(),
            Equal(group, Call("SylowProduct", group)), Close, Dot));
    }
}
