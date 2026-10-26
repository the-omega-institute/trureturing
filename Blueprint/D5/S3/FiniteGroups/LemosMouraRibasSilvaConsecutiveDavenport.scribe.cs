using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class LemosMouraRibasSilvaConsecutiveDavenportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/lemos2024consecutivedavenport");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The consecutive Davenport constant of every finite group equals its order.",
        H("Consecutive Davenport constants of finite groups"),
        Blocks(
            Node("consecutive-product-one", "A consecutive product-one subsequence",
                "HasConsecutiveProductOne", ProductOneFormula(),
                "Printed p. 1 states: “An ordered subsequence T of S is an ordered sequence of the "
                    + "form T = gᵢ · gᵢ₊₁ · … · gⱼ₋₁ · gⱼ for some 1 ≤ i ≤ j ≤ k.” "
                    + "Printed p. 2 states: “When A = {1}, we call S a consecutive product-one sequence "
                    + "and a consecutive product-one free sequence, respectively.” "
                    + "Ordered sequences are List G. The condition T ≠ [] excludes the empty block, "
                    + "List.IsInfix T S specifies contiguity, and List.prod T multiplies letters in their given order. "
                    + "The definition also makes sense for a monoid.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("consecutive-davenport-constant", "The unweighted consecutive Davenport constant",
                "C", ConstantFormula(),
                "Printed p. 2 states: “Let C_A(G) be the smallest positive integer ℓ such that every "
                    + "sequence over G, with length at least ℓ, has an A-weighted consecutive product-one "
                    + "subsequence.” “For A = {1}, we omit the index A.” "
                    + "Here C G is sInf in the natural numbers of the positive thresholds with this property. "
                    + "The threshold set is nonempty for every finite group by the prefix-product pigeonhole principle; "
                    + "thus its infimum is its least element. The natural infimum of an empty threshold set is zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-three-four", "Conjecture 3.4",
                "claim", Disp(IffFormula(F.Id("claim"), Parenthesized(ClaimBody()))),
                "Printed p. 3 states: “For every finite group G, it holds C(G) = |G|.” "
                    + "The carrier G has Group and Finite instances, and Nat.card G denotes its order. "
                    + "This includes the trivial group.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-three-four-result", "Conjecture 3.4 holds",
                "result", Disp(ClaimBody()),
                "A word of length at least Nat.card G has two equal prefix products, so the intervening "
                    + "nonempty contiguous block has product one. For the converse, enumerate the group "
                    + "as e(0), …, e(n−1) and take successive letters e(i)⁻¹e(i+1). "
                    + "The prefix products are e(0)⁻¹e(i), which are pairwise distinct. "
                    + "Consequently this word of length n−1 has no nonempty product-one block. "
                    + "These upper and lower bounds identify the least positive threshold. "
                    + "The argument uses arbitrary finite groups and does not require commutativity or metacyclic structure. "
                    + "Larger weight sets and the enumeration of extremal words are outside this statement.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "lemos-moura-ribas-silva-2024-consecutive-davenport-conjecture-3-4"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Qualified(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name)))), [.. arguments]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Instance(string name, Formula g, Formula body) =>
        Seq(OpenBracket, Call(name, g), CloseBracket, Sp, body);

    private static Formula ProductOneFormula()
    {
        var g = F.Id("G");
        var s = F.Id("S");
        var t = F.Id("T");
        var nonempty = new Formula.Relation(t, FormulaRelationOperator.NotEqual,
            Seq(OpenBracket, CloseBracket));
        var block = Exists("T", Call("List", g),
            And(nonempty, Parenthesized(And(Qualified("List", "IsInfix", t, s),
                Equal(Qualified("List", "prod", t), D(1))))));
        return Disp(All("G", F.Id("Type"), Instance("Monoid", g,
            All("S", Call("List", g), IffFormula(Call("HasConsecutiveProductOne", s),
                Parenthesized(block))))));
    }

    private static Formula ConstantFormula()
    {
        var g = F.Id("G");
        var l = F.Id("l");
        var s = F.Id("S");
        var large = new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual,
            Qualified("List", "length", s));
        var positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, l);
        var condition = And(positive, Parenthesized(All("S", Call("List", g),
            Imp(large, Call("HasConsecutiveProductOne", s)))));
        var thresholds = Seq(OpenBrace, Sp, l, Sp, Colon, Sp, F.Id("Nat"), Sp,
            Mid, Sp, condition, Sp, CloseBrace);
        return Disp(All("G", F.Id("Type"), Instance("Monoid", g,
            Equal(Call("C", g), Call("sInf", thresholds)))));
    }

    private static Formula ClaimBody()
    {
        var g = F.Id("G");
        return All("G", F.Id("Type"), Instance("Group", g, Instance("Finite", g,
            Equal(Call("C", g), Qualified("Nat", "card", g)))));
    }
}
