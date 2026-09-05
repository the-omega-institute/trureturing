using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class FiniteCosetPartitionMaximalIndexMultiplicityDocument
    : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Factorization/PrimePowers/FiniteCosetPartitionMaximalIndexMultiplicity.";

    private static readonly LibraryNoteRef BergerFelzenbaumFraenkel =
        LibraryNoteRef.Create(
            "D5/L/Arith/bergerfelzenbaumfraenkel1986herzogschonheim");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-power group coset partitions have p-divisible maximal-index multiplicity.",
        H("Maximal-Index Multiplicity in Prime-Power Group Coset Partitions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximal-index-definition"),
                DeclarationHandle.Create(Handle + "maximalIndex"),
                H("The largest subgroup index in a finite indexed family"),
                StatementSource.FromAuthor(MaximalIndexDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "With {G : Type*} and [Group G], the Lean type is {r : Nat} -> "
                            + "(Fin r -> Subgroup G) -> Nat. "
                            + "It is defined exactly as maximalIndex H = Finset.univ.sup "
                            + "(fun i => (H i).index). When r is zero, Finset.univ is empty, "
                            + "so its natural-number supremum and maximalIndex H are zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("maximal-index-positions-definition"),
                DeclarationHandle.Create(Handle + "maximalIndexPositions"),
                H("The positions attaining the largest subgroup index"),
                StatementSource.FromAuthor(MaximalIndexPositionsDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "With {G : Type*} and [Group G], the Lean type is {r : Nat} -> "
                            + "(Fin r -> Subgroup G) -> Finset (Fin r). It is defined exactly "
                            + "as maximalIndexPositions H = "
                            + "Finset.univ.filter (fun i => (H i).index = maximalIndex H). "
                            + "When r is zero, Finset.univ is empty, so the filtered finset is "
                            + "empty."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-divides-maximal-index-multiplicity"),
                DeclarationHandle.Create(Handle + "prime_dvd_card_maximalIndex"),
                H("The maximal-index multiplicity is divisible by the underlying prime"),
                StatementSource.FromAuthor(DivisibilityFormula()),
                AssessedProvenance.FromRepo(BergerFelzenbaumFraenkel),
                Blocks(
                    Paragraph(Text(
                        "Let G be a finite group of order p^N, where p is prime, and let "
                            + "the r left-coset sets g_i H_i be pairwise disjoint and cover G, "
                            + "with r at least two. Here [G:H_i] is the subgroup index, d is "
                            + "literally the maximum of these indices, and the displayed set "
                            + "contains exactly the positions where [G:H_i] equals d. Then p "
                            + "divides the cardinality of that set.")),
                    Paragraph(Text(
                        "The proof first counts the arbitrary disjoint left-coset cover as "
                            + "|G| = sum_i |H_i|. Because all subgroup indices divide the same "
                            + "prime power, each index divides d; cancelling |G|/d gives the "
                            + "natural-number identity d = sum_i d/[G:H_i]. Reduction modulo p "
                            + "makes a maximal ratio equal to one and every nonmaximal ratio "
                            + "equal to zero. A nontrivial partition forces p to divide d, so p "
                            + "divides the surviving maximal-position count. Every slash in "
                            + "this description denotes natural-number Euclidean division, not "
                            + "a field fraction.")),
                    Paragraph(Text(
                        "Berger, Felzenbaum, and Fraenkel prove the qualitative repeated-index "
                            + "Herzog-Schonheim conclusion for finite nilpotent groups. The "
                            + "p-divisibility refinement asserted here is independently derived "
                            + "in this repository, so the paper is acknowledged rather than used "
                            + "as attestation for this stronger statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-lower-bound-and-repeated-index"),
                DeclarationHandle.Create(Handle + "prime_le_card_maximalIndex"),
                H("At least p maximal positions yield two equal subgroup indices"),
                StatementSource.FromAuthor(LowerBoundAndRepetitionFormula()),
                AssessedProvenance.FromLiterature(BergerFelzenbaumFraenkel),
                Blocks(
                    Paragraph(Text(
                        "Under exactly the same hypotheses and with exactly the same literal "
                            + "maximum d, the maximal-index position set has cardinality at least "
                            + "p, and there are distinct positions i and j whose subgroup indices "
                            + "are equal. Both clauses form one public theorem, matching the whole "
                            + "companion statement.")),
                    Paragraph(Text(
                        "This declaration is bind-only: divisibility from the preceding theorem "
                            + "and positivity of the maximal-position set give the lower bound; "
                            + "primality gives p at least two, and the finite-cardinality witness "
                            + "then supplies distinct positions. Its dependency direction is the "
                            + "consumer edge 9.20 to prerequisite 9.19.")),
                    Paragraph(Text(
                        "The cited paper proves the Herzog-Schonheim repeated-index conclusion "
                            + "for all finite nilpotent groups. The displayed lower bound is the "
                            + "quantitative p-group form obtained here from the stronger preceding "
                            + "divisibility theorem."))),
                DescribeRole.Theorem))));

    private static Formula DivisibilityFormula() =>
        Statement(Divides(Prime(), MaximalPositionCount()));

    private static Formula LowerBoundAndRepetitionFormula()
    {
        Formula r = F.Id("r");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula lowerBound = LessThanOrEqual(Prime(), MaximalPositionCount());
        Formula repeatedIndex = ExistsMany(
            [Bound("i", Fin(r)), Bound("j", Fin(r))],
            And(NotEqual(i, j), Equal(Index(i), Index(j))));
        return Statement(And(lowerBound, repeatedIndex));
    }

    private static Formula MaximalIndexDefinitionFormula()
    {
        Formula group = F.Id("G");
        Formula r = F.Id("r");
        Formula h = F.Id("H");
        Formula i = F.Id("i");
        Formula finR = Fin(r);
        Formula familyType = Parenthesized(
            new Formula.TypeArrow(finR, Call("Subgroup", group)));
        Formula supremum = Apply(
            Qualified("Finset", "univ", "sup"),
            Seq(i, Sp, Mapsto, Sp, Index(i)));

        Formula body = ForAllMany(
            [Bound("r", Naturals()), Bound("H", familyType)],
            Equal(Call("maximalIndex", h), supremum));
        return Disp(ForAllMany(
            [Bound("G", F.Id("Type"))],
            Implies(Call("Group", group), body)));
    }

    private static Formula MaximalIndexPositionsDefinitionFormula()
    {
        Formula group = F.Id("G");
        Formula r = F.Id("r");
        Formula h = F.Id("H");
        Formula i = F.Id("i");
        Formula finR = Fin(r);
        Formula familyType = Parenthesized(
            new Formula.TypeArrow(finR, Call("Subgroup", group)));
        Formula predicate = Seq(
            i, Sp, Mapsto, Sp, Equal(Index(i), Call("maximalIndex", h)));
        Formula positions = Apply(Qualified("Finset", "univ", "filter"), predicate);

        Formula body = ForAllMany(
            [Bound("r", Naturals()), Bound("H", familyType)],
            Equal(Call("maximalIndexPositions", h), positions));
        return Disp(ForAllMany(
            [Bound("G", F.Id("Type"))],
            Implies(Call("Group", group), body)));
    }

    private static Formula Statement(Formula conclusion)
    {
        Formula group = F.Id("G");
        Formula r = F.Id("r");
        Formula p = Prime();
        Formula exponent = F.Id("N");
        Formula h = F.Id("H");
        Formula g = F.Id("g");
        Formula naturals = Naturals();
        Formula finR = Fin(r);

        Formula structure = And(Call("Group", group), Call("Finite", group));
        Formula hypotheses = All(
            LessThanOrEqual(D(2), r),
            Call("Prime", p),
            Equal(Call("NatCard", group), new Formula.Power(p, exponent)),
            PairwiseDisjointLeftCosets(),
            Equal(Call("iUnionLeftCosetSets", g, h), Call("univ", group)));

        Formula body = ForAllMany(
            [
                Bound("r", naturals),
                Bound("p", naturals),
                Bound("N", naturals),
                Bound("H", Parenthesized(
                    new Formula.TypeArrow(finR, Call("Subgroup", group)))),
                Bound("g", Parenthesized(new Formula.TypeArrow(finR, group))),
            ],
            Implies(hypotheses, conclusion));

        return Disp(ForAllMany(
            [Bound("G", F.Id("Type"))],
            Implies(structure, body)));
    }

    private static Formula PairwiseDisjointLeftCosets()
    {
        Formula r = F.Id("r");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        return ForAllMany(
            [Bound("i", Fin(r)), Bound("j", Fin(r))],
            Implies(
                NotEqual(i, j),
                Call("Disjoint", LeftCosetSet(i), LeftCosetSet(j))));
    }

    private static Formula MaximalPositionCount()
    {
        Formula r = F.Id("r");
        Formula i = F.Id("i");
        Formula positions = Seq(
            OpenBrace,
            i, Sp, InMacro, Sp, Fin(r), Sp, Mid, Sp,
            Equal(Index(i), MaximalIndex()),
            CloseBrace);
        return Call("card", positions);
    }

    private static Formula MaximalIndex()
    {
        Formula r = F.Id("r");
        Formula j = F.Id("j");
        return Seq(
            Max, Underscore,
            Grp(j, Sp, InMacro, Sp, Fin(r)),
            Sp, Index(j));
    }

    private static Formula Index(Formula position)
    {
        Formula group = F.Id("G");
        Formula h = F.Id("H");
        return Seq(
            OpenBracket, group, Colon,
            new Formula.Apply(h, [position]),
            CloseBracket);
    }

    private static Formula LeftCosetSet(Formula position)
    {
        Formula h = F.Id("H");
        Formula g = F.Id("g");
        return Call(
            "leftCosetSet",
            new Formula.Apply(g, [position]),
            Call("carrier", new Formula.Apply(h, [position])));
    }

    private static Formula Prime() => F.Id("p");

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Fin(Formula size) => Call("Fin", size);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Qualified(params string[] names)
    {
        Formula result = F.Id(names[0]);
        foreach (var name in names[1..])
            result = Seq(result, Dot, F.Id(name));
        return Seq(Operatorname, Grp(result));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula ForAllMany(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula ExistsMany(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }
}
