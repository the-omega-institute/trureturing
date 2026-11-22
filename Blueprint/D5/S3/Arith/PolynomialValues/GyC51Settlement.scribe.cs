using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PolynomialValues;

internal sealed class GyC51SettlementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PolynomialValues/GyC51Settlement.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Arith/gy2026stirling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common affine input family gives two symmetric triple-product differences whose coefficients fail log-concavity.",
        H("Gy's coefficient log-concavity question"),
        Blocks(
            Definition("inputPrefix", "The first m inputs",
                WithSequence(All("m", Nat(), All("i", Call("Fin", V("m")),
                    Equal(Call("inputPrefix", V("x"), V("m"), V("i")),
                        App(V("x"), Add(Call("val", V("i")), D(1))))))),
                "The prefix of size m is indexed by Fin m and begins at the sequence term x₁."),
            Definition("qLe", "Coefficientwise order",
                All("f", Poly(), All("g", Poly(), Iff(Call("qLe", V("f"), V("g")),
                    All("k", Nat(), Le(D(0), Call("coeff", Subtract(V("g"), V("f")), V("k"))))))),
                "The order compares every coefficient of the difference g − f."),
            Definition("StronglyQLogConcave", "Strong q-log-concavity", StrongBody(),
                "The source's left index is i + 1. Its predecessor is i, and r = i is the equality case."),
            Definition("e", "The elementary symmetric sum", SymmetricEvaluation("e", "esymm"),
                "The sum is over subsets of size d of the first m input terms."),
            Definition("h", "The complete homogeneous symmetric sum", SymmetricEvaluation("h", "hsymm"),
                "The sum is over multisets of size d of the first m input terms."),
            Definition("E", "The elementary triple-product difference", Difference(true),
                "Both products use elementary symmetric sums on the indicated prefixes."),
            Definition("H", "The complete homogeneous triple-product difference", Difference(false),
                "Both products use complete homogeneous symmetric sums on the indicated prefixes."),
            Definition("CoeffLogConcave", "Log-concavity of the coefficients", CoeffBody(),
                "Each determinant uses the coefficient at one interior index and the coefficients at its two neighbors."),
            Definition("claim", "Gy's affirmative assertion", Iff(V("claim"), ClaimBody()),
                "Gy asks in Section 5, printed page 16, whether strong q-log-concavity of a sequence in R[q] "
                + "forces log-concavity of the coefficients of both E and H at each allowed triple. "
                + "Conjecture 5.1 on printed page 15 asks for coefficient nonnegativity of E and H."),
            Describe.Lean(DescribeId.Create("gy26c51-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Both outputs can fail coefficient log-concavity"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Set gₜ = 1 + q + tq² and xₖ = (k + a)gₜ for every k ≥ 0. The strong q-log-concavity "
                    + "difference is (r − i)gₜ² for every i ≤ r, so the premise holds for t ≥ 0.")),
                    Paragraph(Text(
                    "For n = j + 2 and p = j + 1, each output equals Cgₜ⁴, where "
                    + "C = j(j + 1)²(j + 2)(2a + j + 2)(4a + j + 3)/48 is positive for a > 0 and j ≥ 1. "
                    + "The first three coefficients are C, 4C and (6 + 4t)C. At t > 5/2, index one is interior "
                    + "and its determinant (10 − 4t)C² is negative.")),
                    Paragraph(Text(
                    "The choice a = 1, t = 3 and j = 1 gives (n, p, j) = (3, 2, 1). Each output has first "
                    + "coefficients 10, 40 and 180 and determinant −200. Both polynomials have nonnegative coefficients."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("gy26c51-" + (name switch
            {
                "e" => "elementary-sum",
                "h" => "homogeneous-sum",
                "E" => "elementary-difference",
                "H" => "homogeneous-difference",
                _ => name.ToLowerInvariant(),
            })),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Poly() => Seq(Mathbb, Grp(V("R")), OpenBracket, V("q"), CloseBracket);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [..args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula WithSequence(Formula body) => All("x", Seq(Nat(), Sp, To, Sp, Poly()), body);
    private static Formula WithTriple(Formula body) => All("n", Nat(), All("p", Nat(), All("j", Nat(), body)));

    private static Formula StrongBody()
    {
        var x = V("x");
        var i = V("i");
        var r = V("r");
        return WithSequence(Iff(Call("StronglyQLogConcave", x), All("i", Nat(), All("r", Nat(),
            Imp(Le(i, r), Call("qLe", Multiply(App(x, i), App(x, Add(r, D(1)))),
                Multiply(App(x, Add(i, D(1))), App(x, r))))))));
    }

    private static Formula SymmetricEvaluation(string name, string operation)
    {
        var x = V("x");
        var m = V("m");
        var d = V("d");
        return WithSequence(All("m", Nat(), All("d", Nat(), Equal(Call(name, x, m, d),
            Call("eval", Call("inputPrefix", x, m), Call(operation, Call("Fin", m), Poly(), d))))));
    }

    private static Formula Difference(bool elementary)
    {
        var x = V("x");
        var n = V("n");
        var p = V("p");
        var j = V("j");
        var np = Subtract(n, p);
        var pj = Subtract(p, j);
        var nj = Subtract(n, j);
        Formula E(Formula m, Formula d) => Call("e", x, m, d);
        Formula Hs(Formula m, Formula d) => Call("h", x, m, d);
        var em = elementary
            ? Subtract(Multiply(Multiply(E(n, np), E(p, pj)), E(Subtract(n, D(1)), nj)),
                Multiply(Multiply(E(Subtract(n, D(1)), np), E(Subtract(p, D(1)), pj)), E(n, nj)))
            : Subtract(Multiply(Multiply(Hs(p, np), Hs(j, pj)), Hs(Add(j, D(1)), nj)),
                Multiply(Multiply(Hs(Add(p, D(1)), np), Hs(Add(j, D(1)), pj)), Hs(j, nj)));
        return WithSequence(WithTriple(Equal(Call(elementary ? "E" : "H", x, n, p, j), em)));
    }

    private static Formula CoeffBody()
    {
        var f = V("f");
        var k = V("k");
        Formula Coeff(Formula index) => Call("coeff", f, index);
        var determinant = Subtract(new Formula.Power(Coeff(k), D(2)),
            Multiply(Coeff(Add(k, D(1))), Coeff(Subtract(k, D(1)))));
        return All("f", Poly(), Iff(Call("CoeffLogConcave", f), All("k", Nat(),
            Imp(Le(D(1), k), Imp(Less(k, Call("natDegree", f)),
                Le(D(0), determinant))))));
    }

    private static Formula ClaimBody()
    {
        var x = V("x");
        var n = V("n");
        var p = V("p");
        var j = V("j");
        return WithSequence(Imp(Call("StronglyQLogConcave", x), WithTriple(Imp(Le(D(1), j),
            Imp(Le(j, p), Imp(Le(p, n), And(Call("CoeffLogConcave", Call("E", x, n, p, j)),
                Call("CoeffLogConcave", Call("H", x, n, p, j)))))))));
    }
}
