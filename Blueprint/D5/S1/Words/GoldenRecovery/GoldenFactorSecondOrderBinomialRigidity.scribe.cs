using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.GoldenRecovery;

internal sealed class GoldenFactorSecondOrderBinomialRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/rigosalimov2015binomial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At a fixed length, the true count and scattered true-before-false count determine a consecutive golden factor. Prefix counts compare in one orientation, so equality of their total area forces equality of every letter.",
        H("Second-order binomial recovery of golden factors"),
        Blocks(
            Paragraph(Text("Write W(n,i) for goldenFactor(n,i), the list of goldenWord(i+k) for zero through n minus one, and R(i,m) for goldenWindowTrueCount(i,m). Both indices and lengths are arbitrary naturals. The count R(i,m) is the natural number of true letters in that prefix.")),
            Node("prefix-area", "The sum of all prefix counts", "goldenPrefixArea", DescribeRole.Definition,
                AreaFormula(),
                "The area A(i,n) abbreviates goldenPrefixArea(i,n). It includes every prefix length from zero through n, so the empty prefix contributes zero."),
            Node("golden-pairs", "Scattered true-before-false pairs", "goldenTrueFalseCount", DescribeRole.Definition,
                PairsFormula(),
                "B(i,n) abbreviates goldenTrueFalseCount(i,n). At each false letter in the window, add the number of true letters in the preceding prefix. A true letter contributes zero, and intervening letters are unrestricted."),
            Node("profile", "The reduced binomial profile", "goldenBinomialProfile", DescribeRole.Definition,
                ProfileFormula(),
                "The profile records the final true count and the scattered-pair count, in that order. The length n is a fixed parameter, rather than a third coordinate."),
            Node("comparable-prefixes", "A common order for every prefix", "golden_prefix_counts_comparable", DescribeRole.Theorem,
                ComparableFormula(),
                "The Beatty formula writes the integer cast of R(i,m) as floor(fract((i+1)/phi)+m/phi), with phi the golden ratio. Ordering the two intercept phases orders all their prefix counts in the same direction, simultaneously for every natural m."),
            Node("area-recovery", "Prefix area determines the word", "golden_factor_eq_of_prefix_area_eq", DescribeRole.Theorem,
                AreaRecoveryFormula(),
                "For a fixed n, comparable nonnegative summands with equal total area are equal at every prefix length up to n. Successive prefix-count differences are the true-letter indicators, so equality of the prefixes recovers every letter of W(n,i). No positivity assumption on n is required.", literature: true),
            Node("area-identity", "The exact binomial area identity", "golden_prefix_area_binomial_identity", DescribeRole.Theorem,
                IdentityFormula(),
                "Appending false adds the old true count to B and leaves the final true count unchanged. Appending true raises the true count by one and adds no pair. These two cases give the integral identity by induction; using twice the area avoids division."),
            Node("count-recovery", "Two counts recover a fixed-length factor", "golden_factor_eq_of_second_order_counts", DescribeRole.Theorem,
                CountRecoveryFormula(),
                "Equal true counts and equal scattered-pair counts give equal prefix areas by the identity, and hence equal words. The conclusion recovers word content, without identifying the absolute occurrence indices i and j.", literature: true),
            Node("profile-kernel", "Exactly the same observation fibers", "golden_factor_eq_iff_second_order_profile_eq", DescribeRole.Theorem,
                EquivalenceFormula(),
                "Conversely, equal words have equal counts in every prefix and equal letters at every position, hence equal B. Thus word equality is equivalent to profile equality at each specified length. For n equal to zero, every word is empty and every profile is (0,0). Pure-letter windows require no separate guard.", literature: true)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, Formula formula, string prose, bool literature = false) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nat(string name, Formula body) => All(name, F.Id("Nat"), body);
    private static Formula Three(Formula body) => Nat("n", Nat("i", Nat("j", body)));
    private static Formula Word(Formula n, Formula i) => Call("W", n, i);
    private static Formula Count(Formula i, Formula n) => Call("R", i, n);
    private static Formula Area(Formula i, Formula n) => Call("A", i, n);
    private static Formula Pairs(Formula i, Formula n) => Call("B", i, n);

    private static Formula AreaFormula()
    {
        Formula i = F.Id("i"), n = F.Id("n"), m = F.Id("m");
        Formula sum = Seq(Sum, Underscore, Grp(m, InMacro, Sp, Call("range", Add(n, D(1)))), Count(i, m));
        return Disp(Nat("i", Nat("n", Equal(Area(i, n), sum))));
    }

    private static Formula PairsFormula()
    {
        Formula i = F.Id("i"), n = F.Id("n"), k = F.Id("k");
        Formula sum = Seq(Sum, Underscore, Grp(k, InMacro, Sp, Call("range", n)),
            Call("if", Equal(Call("goldenWord", Add(i, k)), F.Id("true")), D(0), Count(i, k)));
        return Disp(Nat("i", Nat("n", Equal(Pairs(i, n), sum))));
    }

    private static Formula ProfileFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i");
        return Disp(Nat("n", Nat("i", Equal(Call("goldenBinomialProfile", n, i),
            Seq(Open, Count(i, n), Comma, Pairs(i, n), Close)))));
    }

    private static Formula ComparableFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j"), m = F.Id("m");
        return Disp(Nat("i", Nat("j", Or(Nat("m", AtMost(Count(i, m), Count(j, m))),
            Nat("m", AtMost(Count(j, m), Count(i, m)))))));
    }

    private static Formula AreaRecoveryFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), j = F.Id("j");
        return Disp(Three(Implies(Equal(Area(i, n), Area(j, n)), Equal(Word(n, i), Word(n, j)))));
    }

    private static Formula IdentityFormula()
    {
        Formula i = F.Id("i"), n = F.Id("n"), r = Count(i, n);
        return Disp(Nat("i", Nat("n", Equal(Mul(D(2), Area(i, n)),
            Add(Mul(D(2), Pairs(i, n)), Mul(r, Add(r, D(1))))))));
    }

    private static Formula CountRecoveryFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), j = F.Id("j");
        return Disp(Three(Implies(Equal(Count(i, n), Count(j, n)),
            Implies(Equal(Pairs(i, n), Pairs(j, n)), Equal(Word(n, i), Word(n, j))))));
    }

    private static Formula EquivalenceFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), j = F.Id("j");
        return Disp(Three(Equivalent(Equal(Word(n, i), Word(n, j)),
            Equal(Call("goldenBinomialProfile", n, i), Call("goldenBinomialProfile", n, j)))));
    }
}
