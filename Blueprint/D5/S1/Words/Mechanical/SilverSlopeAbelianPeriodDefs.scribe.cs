using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class SilverSlopeAbelianPeriodDefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/peltomaki2020abelianperiods");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal definitions and the silver-slope abelian-period conjecture.",
        H("Silver-Slope Abelian Periods"),
        Blocks(
            Paragraph(Text(
                "The definitions below use Boolean Parikh vectors, the contained-head and "
                    + "contained-tail convention, lower mechanical factors, and the Pell recurrence "
                    + "P₀=0, P₁=1, Pₖ₊₂=2Pₖ₊₁+Pₖ. The source denominators "
                    + "are P(k+1), and their predecessors are P(k).")),
            Describe.Lean(
                DescribeId.Create("silver-slope"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.silverSlope"),
                H("The silver slope"),
                StatementSource.FromAuthor(SilverSlopeFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The slope is the positive quadratic irrational √2−1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("abelian-decomposition"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.AbelianDecomposition"),
                H("An abelian block decomposition with contained ends"),
                StatementSource.FromAuthor(AbelianDecompositionFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Quote("Verbatim source (arXiv v3, p. 7): If 𝒫 and 𝒬 are two Parikh vectors and 𝒫 is componentwise less than or equal to 𝒬 but is not equal to 𝒬, then we say that 𝒫 is contained in 𝒬."), Quote("Verbatim Definition 2.4 (arXiv v3, p. 8): An abelian decomposition of a word w is a factorization w = u₀u₁⋯uₙ₋₁uₙ such that n ≥ 2, the words u₁, …, uₙ₋₁ have a common Parikh vector 𝒫 (i.e., they are abelian equivalent), and the Parikh vectors of u₀ and uₙ are contained in 𝒫."),Paragraph(Text(
                    "The word has a positive block length, a nonempty list of equal-length blocks "
                        + "with a common Parikh vector, and head and tail vectors properly contained "
                        + "in that common vector. The symbol < is the componentwise strict order on ℕ × ℕ: "
                        + "both coordinates are bounded and the vectors are unequal. This is the source's contained relation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("abelian-period"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.AbelianPeriod"),
                H("An abelian period"),
                StatementSource.FromAuthor(AbelianPeriodFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Quote("Verbatim Definition 2.4 (arXiv v3, p. 8): The common length m of the words u₁, …, uₙ₋₁ is called an abelian period of w."),Paragraph(Text(
                    "An abelian period is exactly an abelian decomposition at that block length."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("minimum-abelian-period"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.minAbelianPeriod"),
                H("The least abelian period when one exists"),
                StatementSource.FromAuthor(MinAbelianPeriodFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Quote("Verbatim Definition 2.4 (arXiv v3, p. 8): The minimum abelian period (i.e., the shortest) of w is denoted by μw."),Paragraph(Text(
                    "Nat.find selects the least abelian period, with value zero for a word having "
                        + "no abelian period."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("abelian-period-set"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.abelianPeriodSet"),
                H("Minimum periods of nonempty lower mechanical factors"),
                StatementSource.FromAuthor(AbelianPeriodSetFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Quote("Verbatim source (arXiv v3, p. 2): The abelian period set of an infinite word w is defined as the set of minimum abelian periods of its nonempty factors."),Paragraph(Text(
                    "The set contains exactly the minimum periods of factors with positive length."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("silver-abelian-period-set"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.silverAbelianPeriodSet"),
                H("The silver-slope period set"),
                StatementSource.FromAuthor(SilverAbelianPeriodSetFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This specializes the period-set definition to the silver slope and zero intercept."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("silver-candidate-set"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodDefs.silverCandidateSet"),
                H("The three silver-slope candidate families"),
                StatementSource.FromAuthor(SilverCandidateSetFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The candidate periods are P(k+1), 2P(k+1), and P(k+1)+P(k) for k≥1 in the last family."))),
                DescribeRole.Definition)),
        []));
    private static DocumentBlock Quote(string text) => Paragraph(Text(text));
    private static Formula SilverSlopeFormula() => Disp(Seq(
        Call("silverSlope"), Sp, Eq, Sp, Sqrt, Grp(D(2)), Sp, Minus, Sp, D(1), Dot));

    private static Formula AbelianDecompositionFormula()
    {
        Formula w = F.Id("w"), m = F.Id("m"), head = F.Id("head"), tail = F.Id("tail");
        Formula blocks = F.Id("blocks"), common = F.Id("p"), a = F.Id("a"), b = F.Id("b");
        Formula bMember = Rel(b, FormulaRelationOperator.MemberOf, blocks);
        Formula aMember = Rel(a, FormulaRelationOperator.MemberOf, blocks);
        Formula lengths = All("b", ListBoolType(), Imply(bMember,
            Rel(Call("length", b), FormulaRelationOperator.Equal, m)));
        Formula equalParikh = All("a", ListBoolType(), Imply(aMember,
            All("b", ListBoolType(), Imply(bMember,
                Rel(Call("parikh", a), FormulaRelationOperator.Equal, Call("parikh", b))))));
        Formula commonParikh = Ex("p", ProdNat(), Conjoin(
            All("b", ListBoolType(), Imply(bMember,
                Rel(Call("parikh", b), FormulaRelationOperator.Equal, common))),
            Rel(Call("parikh", head), FormulaRelationOperator.LessThan, common),
            Rel(Call("parikh", tail), FormulaRelationOperator.LessThan, common)));
        Formula body = Conjoin(Rel(D(0), FormulaRelationOperator.LessThan, m),
            Ex("head", ListBoolType(), Ex("tail", ListBoolType(),
                Ex("blocks", Call("List", ListBoolType()), Conjoin(
                    Rel(blocks, FormulaRelationOperator.NotEqual, Seq(OpenBracket, CloseBracket)),
                    Rel(w, FormulaRelationOperator.Equal,
                        Call("append", Call("append", head, Call("flatten", blocks)), tail)),
                    lengths, equalParikh, commonParikh)))));
        return Disp(All("w", ListBoolType(), All("m", Naturals(),
            new Formula.Logic(Call("AbelianDecomposition", w, m), FormulaLogicOperator.Iff, body))));
    }

    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Imply(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula body = clauses[^1];
        for (int index = clauses.Length - 2; index >= 0; index--)
            body = new Formula.Logic(clauses[index], FormulaLogicOperator.And, body);
        return body;
    }

    private static Formula AbelianPeriodFormula() => Disp(All("w", ListBoolType(), All("m", Naturals(),
        new Formula.Relation(Call("AbelianPeriod", F.Id("w"), F.Id("m")),
            FormulaRelationOperator.Equal, Call("AbelianDecomposition", F.Id("w"), F.Id("m"))))));

    private static Formula MinAbelianPeriodFormula() => Disp(All("w", ListBoolType(),
        new Formula.Relation(Call("minAbelianPeriod", F.Id("w")), FormulaRelationOperator.Equal,
            Call("if", Seq(F.Id("h"), Colon, Sp, ExistsAbelianPeriod(F.Id("w"))),
                Apply(Seq(F.Id("Nat"), Dot, F.Id("find")), F.Id("h")), D(0)))));

    private static Formula AbelianPeriodSetFormula() => Disp(All("alpha", Reals(), All("rho", Reals(),
        new Formula.Relation(Call("abelianPeriodSet", F.Id("alpha"), F.Id("rho")), FormulaRelationOperator.Equal,
            SetOf(F.Id("m"), Naturals(), Ex("n", Naturals(), Ex("i", Naturals(),
                Parenthesized(Seq(D(0), Sp, Lt, Sp, F.Id("n"), Sp, Land, Sp,
                    Call("minAbelianPeriod", Call("lowerMechanicalFactor", F.Id("alpha"), F.Id("rho"), F.Id("n"), F.Id("i"))),
                    Sp, Eq, Sp, F.Id("m"))))))))));

    private static Formula SilverAbelianPeriodSetFormula() => Disp(Seq(
        Call("silverAbelianPeriodSet"), Sp, Eq, Sp,
        Call("abelianPeriodSet", Call("silverSlope"), D(0)), Dot));

    private static Formula SilverCandidateSetFormula()
    {
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        Formula current = Call("P", Seq(k, Sp, Plus, Sp, D(1)));
        Formula previous = Call("P", k);
        Formula body = Seq(
            Parenthesized(Ex("k", Naturals(), Parenthesized(Seq(m, Sp, Eq, Sp, current)))), Sp, Lor, Sp,
            Parenthesized(Ex("k", Naturals(), Parenthesized(Seq(m, Sp, Eq, Sp, D(2), Sp, Times, Sp, current)))), Sp, Lor, Sp,
            Parenthesized(Ex("k", Naturals(), Parenthesized(Seq(D(1), Sp, Leq, Sp, k, Sp, Land, Sp,
                m, Sp, Eq, Sp, current, Sp, Plus, Sp, previous)))));
        return Disp(Seq(Call("silverCandidateSet"), Sp, Eq, Sp,
            SetOf(m, Naturals(), body), Dot));
    }

    private static Formula ExistsAbelianPeriod(Formula word) =>
        Ex("m", Naturals(), Call("AbelianPeriod", word, F.Id("m")));

    private static Formula SetOf(Formula variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, variable, Sp, InMacro, Sp, domain, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula ProdNat() => Call("Prod", Naturals(), Naturals());

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        return Seq(Operatorname, Grp(F.Id(name)), Parenthesized(Seq([.. items])));
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        return Seq(function, Parenthesized(Seq([.. items])));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ListBoolType() => Call("List", Call("Bool"));}
