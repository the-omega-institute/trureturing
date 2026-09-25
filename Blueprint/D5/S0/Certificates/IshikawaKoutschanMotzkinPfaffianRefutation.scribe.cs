using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class IshikawaKoutschanMotzkinPfaffianRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/IshikawaKoutschanMotzkinPfaffianRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/ishikawa2012holonomic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At k = n = 2 the Pfaffian of the matrix of the second column of the Motzkin triangle is -8, while the printed product in part (i) of Ishikawa and Koutschan's Conjecture conj.gen is 8.",
        H("Part (i) of Ishikawa and Koutschan's Pfaffian conjecture is false as printed"),
        Blocks(
            Node("motzkin-triangle", "Columns of the Motzkin triangle", TriangleFormula(),
                "A step word of length i - 1 over U = (1,1), H = (1,0) and D = (1,-1) is a Motzkin path from (0,0) to (i - 1, k - 1) when its height never falls below zero and ends at k - 1; heightAfter(w,t) is the height after the first t steps and stepRise maps U, H, D to 1, 0, -1. The count is the entry M^(k)_i of the source. At i = 0 it enters the matrix only on the diagonal, where the factor j - i vanishes.",
                "motzkinTriangle", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pfaffian-matrix", "The Hankel-type skew matrix", MatrixFormula(),
                "The entry in row p and column q, indexed from zero, is (q - p) M^(k)_(p+q); with i = p + 1 and j = q + 1 this is the source's entry (j - i) M^(k)_(i+j-2) for 1 <= i, j <= 2n.",
                "pfaffianMatrix", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pfaffian", "The Pfaffian", PfaffianFormula(),
                "The source defines Pf(A) as the sum over the partitions of [2n] into two-element subsets of the sign of the listing permutation times the product of the paired entries. The formal sum lists each partition once, by the permutations sigma whose pairs {sigma(2i), sigma(2i+1)} are increasing and ordered by their first elements.",
                "pfaffian", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("printed-value", "The printed right-hand side", PrintedFormula(),
                "The first branch is the product for m = n/k when k divides n; the second is the product for odd k with m = (n + floor(k/2))/k when k divides n + floor(k/2); all other cases give zero. Natural-number division and remainder are written NatDiv and NatMod.",
                "printedValue", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Part (i) of Conjecture conj.gen", ClaimDefinitionFormula(),
                "For all positive integers k and n the Pfaffian of the matrix equals the printed value. At k = 1 this is the source's Theorem thm.pfMotz. Part (ii) of the conjecture is not part of this statement.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A sign counterexample at k = n = 2", Disp(new Formula.Not(F.Id("claim"))),
                "The column M^(2)_1, ..., M^(2)_5 is 0, 1, 2, 5, 12, so the upper entries of the 4 x 4 matrix are a12 = 0, a13 = 2, a14 = 6, a23 = 2, a24 = 10, a34 = 12, and its Pfaffian is a12 a34 - a13 a24 + a14 a23 = 0 - 20 + 12 = -8. Since 2 divides 2 with m = 1, the printed value is the product of 4km + 2j + k over m = 0 and j = 0, 1, namely 2 times 4, which is 8. The kernel evaluates both sides.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ishikawa-koutschan-2012-motzkin-triangle-pfaffian-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("ik-pfaffian-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Card(Formula s) => Call("card", s);
    private static Formula Range(Formula n) => Call("Finset.range", n);
    private static Formula Icc(Formula a, Formula b) => Call("Finset.Icc", a, b);
    private static Formula ProdOver(string variable, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(F.Id(variable), Sp, InMacro, Sp, domain)), Sp, body);
    private static Formula SumOver(string variable, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(variable), Sp, InMacro, Sp, domain)), Sp, body);

    private static Formula TriangleFormula()
    {
        Formula k = F.Id("k"), i = F.Id("i"), w = F.Id("w"), t = F.Id("t");
        Formula words = new Formula.TypeArrow(Fin(Subtract(i, D(1))), Fin(D(3)));
        Formula above = All("t", Range(i), AtMost(D(0), Call("heightAfter", w, t)));
        Formula ends = Equal(Call("heightAfter", w, Subtract(i, D(1))), Subtract(k, D(1)));
        Formula paths = Seq(OpenBrace, Member(w, words), Sp, Mid, Sp, And(above, ends), CloseBrace);
        return Disp(All("k", Naturals(), All("i", Naturals(),
            Equal(Call("motzkinTriangle", k, i), Card(paths)))));
    }

    private static Formula MatrixFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n"), p = F.Id("p"), q = F.Id("q");
        Formula entry = Times(Parenthesized(Subtract(q, p)), Call("motzkinTriangle", k, Add(p, q)));
        return Disp(All("k", Naturals(), All("n", Naturals(), All("p", Fin(Times(D(2), n)),
            All("q", Fin(Times(D(2), n)),
                Equal(new Formula.Apply(Call("pfaffianMatrix", k, n), [p, q]), entry))))));
    }

    private static Formula PfaffianFormula()
    {
        Formula a = F.Id("A"), sigma = F.Id("sigma"), i = F.Id("i"), j = F.Id("j"), n = F.Id("n");
        Formula first = Call("sigma", Times(D(2), i));
        Formula second = Call("sigma", Add(Times(D(2), i), D(1)));
        Formula canonical = And(All("i", Fin(n), Less(first, second)),
            All("i", Fin(n), All("j", Fin(n),
                Implies(Less(i, j), Less(first, Call("sigma", Times(D(2), j)))))));
        Formula pairings = Seq(OpenBrace, Member(sigma, Call("Equiv.Perm", Fin(Times(D(2), n)))),
            Sp, Mid, Sp, canonical, CloseBrace);
        Formula term = Times(Call("sign", sigma),
            ProdOver("i", Fin(n), new Formula.Apply(a, [first, second])));
        return Disp(All("n", Naturals(), All("A", Call("Matrix", Fin(Times(D(2), n)),
            Fin(Times(D(2), n)), Integers()),
            Equal(Call("pfaffian", a), SumOver("sigma", pairings, term)))));
    }

    private static Formula PrintedFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n"), i = F.Id("i"), j = F.Id("j");
        Formula half = Call("NatDiv", k, D(2));
        Formula firstProduct = ProdOver("i", Range(Call("NatDiv", n, k)),
            ProdOver("j", Range(k), Parenthesized(Add(Add(Times(Times(D(4), k), i), Times(D(2), j)), k))));
        Formula prefactor = ProdOver("j", Icc(D(1), half),
            new Formula.Fraction(D(1), Subtract(Times(D(2), j), k)));
        Formula secondProduct = ProdOver("i", Range(Call("NatDiv", Add(n, half), k)),
            ProdOver("j", Icc(D(1), k), Parenthesized(Subtract(Add(Times(Times(D(4), k), i), Times(D(2), j)), k))));
        Formula oddCase = And(Equal(Call("NatMod", k, D(2)), D(1)),
            new Formula.Relation(k, FormulaRelationOperator.Divides, Add(n, half)));
        Formula value = Call("ite", new Formula.Relation(k, FormulaRelationOperator.Divides, n),
            firstProduct, Call("ite", oddCase, Times(prefactor, secondProduct), D(0)));
        return Disp(All("k", Naturals(), All("n", Naturals(),
            Equal(Call("printedValue", k, n), value))));
    }

    private static Formula ClaimBody()
    {
        Formula k = F.Id("k"), n = F.Id("n");
        return All("k", Naturals(), All("n", Naturals(),
            Implies(And(Less(D(0), k), Less(D(0), n)),
                Equal(Call("pfaffian", Call("pfaffianMatrix", k, n)), Call("printedValue", k, n)))));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));
}
