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

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula group = F.Id("G");
        Formula observer = Call("primePowerQuotientObserver", group);
        Formula residual = Call("primePowerResidual", group);
        Formula trivial = Call("trivialSubgroup", group);
        Formula indexType = Iota;
        Formula factorFamily = F.Id("P");
        Formula factorIndex = F.Id("i");
        Formula prime = F.Id("prime");
        Formula embedding = F.Id("embedding");
        Formula factorAtIndex = Apply(factorFamily, factorIndex);
        Formula product = Seq(
            Prod, Underscore, Grp(Typed(factorIndex, indexType)), Sp, factorAtIndex);
        Formula factorStructures = Seq(
            Open, Forall, Sp, Typed(factorIndex, indexType), Comma, Sp,
            Call("Group", factorAtIndex), Close, Sp, Land, Sp,
            Open, Forall, Sp, Typed(factorIndex, indexType), Comma, Sp,
            Call("Finite", factorAtIndex), Close);
        Formula primeWitnesses = Seq(
            Forall, Sp, Typed(factorIndex, indexType), Comma, Sp,
            Call("Prime", Apply(prime, factorIndex)), Sp, Land, Sp,
            Call("IsPGroup", Apply(prime, factorIndex), factorAtIndex));
        Formula productClause = Seq(
            Exists, Sp, Typed(indexType, type), Comma, Sp,
            Typed(factorFamily, Arrow(indexType, type)), Comma, Sp,
            Typed(prime, Arrow(indexType, natural)), Comma, RowBreak, Grp(),
            Call("Finite", indexType), Sp, Land, Sp, factorStructures, Sp, Land,
            RowBreak, Grp(), Open, primeWitnesses, Close, Sp, Land,
            RowBreak, Grp(),
            Exists, Sp, Typed(embedding, Call("MonoidHom", group, product)), Comma, Sp,
            Call("Injective", embedding));

        Formula primeIndex = F.Id("p");
        Formula sylow = F.Id("S");
        Formula primeFactors = Call("primeFactors", Call("NatCard", group));
        Formula sylowProduct = Seq(
            Prod, Underscore, Grp(Typed(primeIndex, primeFactors)), Sp,
            Prod, Underscore,
            Grp(Typed(sylow, Call("Sylow", primeIndex, group))), Sp,
            Call("carrier", sylow));
        Formula sylowClause = Call(
            "Nonempty", Call("MonoidEquiv", sylowProduct, group));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(group, type), Comma, RowBreak, Grp(),
            Open, Call("Group", group), Sp, Land, Sp, Call("Finite", group), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Operatorname, Grp(F.Id("TFAE")), Open,
            Call("Injective", observer), Comma, RowBreak, Grp(),
            Equal(residual, trivial), Comma, RowBreak, Grp(),
            productClause, Comma, RowBreak, Grp(),
            Call("Nilpotent", group), Comma, RowBreak, Grp(),
            sylowClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
