using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class TransversalProbabilityMonotoneDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/aivazidis2023commontransversal");

    private const string Question =
        @"Suppose that H ≤ G and N ⊴ G, where G is finite. "
        + @"Is it then always true that P_G(H) ≤ P_G(HN) "
        + @"(GAP computations confirm this up to |G| = 200)?";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common transversal probability increases when a subgroup is enlarged by a normal subgroup.",
        H("Normal extensions and common transversals"),
        Blocks(
            Node("DT", "Two-sided transversal subsets", DtFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Definition 3.1(i), printed p. 8: “We denote by DT_G(H, K) the set "
                + "of all left transversals for H in G, which are also right transversals for "
                + "K in G.” The carrier is a subtype of Set G. Subgroup.IsComplement means "
                + "that multiplication of the two subsets is bijective; T is not required to be a subgroup."),
            Node("commonTransversalProbability", "The normalized number of common transversals",
                ProbabilityFormula(), AssessedProvenance.FromLiterature(Source),
                "Definition 3.1(ii), printed p. 8: “We let P_G(H,K) ≔ "
                + "|DT_G(H, K)|/|H|ⁿ, so that "
                + "P_G(H, K) is the (Laplacian) probability that a left transversal for H "
                + "in G is also a right transversal for K in G." + "” "
                + "Here n = H.index = K.index. Nat.card counts subsets, and the quotient is rational."),
            Node("orbitWeight", "The arithmetic orbit factor", WeightFormula(),
                AssessedProvenance.FromLiterature(Source),
                "For every natural number n, orbitWeight n is the rational number n!/n^n. "
                + "For positive n this is the factor f(n) appearing in Proposition 3.2 "
                + "and Problem 5.6. The definition also fixes a total value at zero. "
                + "Using orbitWeight (n+1)=orbitWeight n*((n:Q)/(n+1))^n, positivity and strict decrease hold on positive arguments. "
                + "The total function is not globally strict because orbitWeight 0=orbitWeight 1=1. "
                + "Consequently, for coordinate-comparable increasing lists of integers greater than one, the product is antitone coordinatewise "
                + "and equality occurs exactly when every coordinate agrees; the empty product is 1 at length zero."),
            Node("P", "The probability for one specified subgroup", PFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Definition 3.1(ii), printed p. 8: “If H = K, we let P_G(H) ≔ "
                + "P_G(H, H) be the probability that a left transversal for H in G is a "
                + "two-sided one.” This quantity belongs to H; it is not the minimum over all subgroups."),
            Node("claim", "Problem 5.2", Disp(Equal(F.Id("claim"), ClaimBody())),
                AssessedProvenance.FromLiterature(Source),
                "Problem 5.2, printed p. 37: “" + Question + "” The group G is arbitrary and finite. "
                + "The product HN is H ⊔ N because N is normal. The equality question and the "
                + "homomorphism consequence are separate from this inequality."),
            Describe.Lean(
                DescribeId.Create("common-transversal-normal-extension-result"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/TransversalProbabilityMonotone.result"),
                H("The normal-extension inequality"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For each double coset, let t be its number of left H-cosets. Its contribution "
                    + "to the transversal count is t! times (|H|/t)^t. Normalizing gives the factor "
                    + "t!/t^t. This factor is nonnegative, at most one, and decreases with t. "
                    + "The quotient map from G/H to G/(H ⊔ N) maps every H-component onto the "
                    + "corresponding component for H ⊔ N: normality lets the N-factor pass through "
                    + "a group representative. Thus each upstairs component has at least the "
                    + "downstairs size. Comparing the factors within each nonempty fibre, and "
                    + "then multiplying, proves the displayed inequality. This finite-surjection chain is the reusable comparison "
                    + "for the factorial-product application; it does not itself assert the ALM counterexample, its common extensions, "
                    + "or an equality classification. The separate ALM source keeps Theorem 4.6's distinct-prime hypothesis and leaves "
                    + "Problems 5.1-5.5 and 5.7-5.8, group realization and related extremal claims outside the factorial-product return."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alm2024"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string heading, Formula formula,
        AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create(name == "DT" ? "common-transversal-subsets"
                : name == "P" ? "common-transversal-single-probability"
                : name == "orbitWeight" ? "common-transversal-orbit-weight"
                : name == "claim" ? "common-transversal-normal-extension-claim"
                : "common-transversal-pair-probability"),
            DeclarationHandle.Create("D5/S3/FiniteGroups/TransversalProbabilityMonotone." + name),
            H(heading), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Qualified(string owner, string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name))))
            : new Formula.Apply(Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name)))), [.. arguments]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Instances(bool finite, Formula body) => finite
        ? Seq(OpenBracket, Call("Group", F.Id("G")), CloseBracket, Sp,
            OpenBracket, Call("Finite", F.Id("G")), CloseBracket, Sp, body)
        : Seq(OpenBracket, Call("Group", F.Id("G")), CloseBracket, Sp, body);

    private static Formula GroupBinders(bool finite, Formula body) =>
        All("G", F.Id("Type"), Instances(finite, body));

    private static Formula SubgroupType() => Call("Subgroup", F.Id("G"));

    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));

    private static Formula DtFormula()
    {
        var t = F.Id("T");
        var set = Call("Set", F.Id("G"));
        var predicate = new Formula.Logic(
            Qualified("Subgroup", "IsComplement", t, Cast(F.Id("H"), set)),
            FormulaLogicOperator.And,
            Qualified("Subgroup", "IsComplement", Cast(F.Id("K"), set), t));
        var lambda = Seq(Operatorname, Grp(F.Id("fun")), Sp, t, Sp, Colon, Sp, set,
            Sp, Mapsto, Sp, predicate);
        return Disp(GroupBinders(false, All("H", SubgroupType(), All("K", SubgroupType(),
            Equal(Call("DT", F.Id("H"), F.Id("K")), Call("Subtype", lambda))))));
    }

    private static Formula ProbabilityFormula()
    {
        var h = F.Id("H");
        var k = F.Id("K");
        var rationals = Seq(Mathbb, Grp(F.Id("Q")));
        var numerator = Cast(Qualified("Nat", "card", Call("DT", h, k)), rationals);
        var denominator = new Formula.Power(Cast(Qualified("Nat", "card", h), rationals),
            Qualified("H", "index"));
        var equality = Equal(Call("commonTransversalProbability", h, k, F.Id("sameIndex")),
            new Formula.Fraction(numerator, denominator));
        return Disp(GroupBinders(true, All("H", SubgroupType(), All("K", SubgroupType(),
            All("sameIndex", Equal(Qualified("H", "index"), Qualified("K", "index")), equality)))));
    }

    private static Formula WeightFormula()
    {
        var n = F.Id("n");
        var q = Seq(Mathbb, Grp(F.Id("Q")));
        return Disp(All("n", Seq(Mathbb, Grp(F.Id("N"))),
            Equal(Call("orbitWeight", n), new Formula.Fraction(
                Cast(Seq(n, Bang), q), new Formula.Power(Cast(n, q), n)))));
    }

    private static Formula PFormula() => Disp(GroupBinders(true,
        All("H", SubgroupType(), Equal(Call("P", F.Id("H")),
            Call("commonTransversalProbability", F.Id("H"), F.Id("H"), F.Id("rfl"))))));

    private static Formula ClaimBody()
    {
        var h = F.Id("H");
        var n = F.Id("N");
        var join = Qualified("Max", "max", h, n);
        var inequality = new Formula.Relation(Call("P", h), FormulaRelationOperator.LessThanOrEqual,
            Call("P", join));
        return GroupBinders(true, All("H", SubgroupType(), All("N", SubgroupType(),
            new Formula.Logic(Qualified("N", "Normal"), FormulaLogicOperator.Implies, inequality))));
    }
}
