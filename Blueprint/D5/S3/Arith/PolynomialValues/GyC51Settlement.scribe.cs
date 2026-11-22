using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PolynomialValues;

internal sealed class GyC51SettlementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PolynomialValues/GyC51Settlement.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/gy2026stirling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An affine input family refutes Gy's joint coefficient log-concavity assertion through the elementary difference.",
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
                Blocks(Paragraph(Text("Gy asks in Section 5, printed page 16.")), PublishedQuestion(),
                    Paragraph(Text("The triple ranges over 1 ≤ j ≤ p ≤ n. The premise includes the predecessor x₀, "
                        + "while each symmetric polynomial starts at x₁. Conjecture 5.1 on printed page 15 asks for "
                        + "coefficient nonnegativity of E and H.")))),
            Describe.Lean(DescribeId.Create("gy26c51-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Gy's joint coefficient log-concavity assertion is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Set gₜ = 1 + q + tq² and xₖ = (k + a)gₜ for every k ≥ 0. The strong q-log-concavity "
                    + "difference is (r − i)gₜ² for every i ≤ r, so the premise holds for t ≥ 0.")),
                    Paragraph(Text(
                    "For n = j + 2 and p = j + 1, the elementary difference E equals Cgₜ⁴, where "
                    + "C = j(j + 1)²(j + 2)(2a + j + 2)(4a + j + 3)/48 is positive for a > 0 and j ≥ 1. "
                    + "The first three coefficients are C, 4C and (6 + 4t)C. At t > 5/2, index one is interior "
                    + "and its determinant (10 − 4t)C² is negative.")),
                    Paragraph(Text(
                    "The choice a = 1, t = 3 and j = 1 gives (n, p, j) = (3, 2, 1). The first three coefficients of E "
                    + "are 10, 40 and 180, with determinant −200. This failure of E proves ¬claim for the joint assertion.")),
                    Paragraph(Text(
                    "A separate kernel-checked calculation gives H = Cgₜ⁴ for the same family. At the same triple "
                    + "it gives the same determinant −200. Both polynomials have nonnegative coefficients."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("gy26c51"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string name, string title, Formula statement, string prose) =>
        Definition(name, title, statement, Blocks(Paragraph(Text(prose))));

    private static DocumentBlock Definition(string name, string title, Formula statement, BlockSequence prose) =>
        Describe.Lean(DescribeId.Create("gy26c51-" + (name switch
            {
                "e" => "elementary-sum",
                "h" => "homogeneous-sum",
                "E" => "elementary-difference",
                "H" => "homogeneous-difference",
                _ => name.ToLowerInvariant(),
            })),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromLiterature(Source), prose, DescribeRole.Definition);

    private static DocumentBlock PublishedQuestion()
    {
        var k = V("k");
        var sequence = new Formula.Subscript(Seq(Open, new Formula.Subscript(V("x"), k), Close),
            Seq(k, Ge, D(1)));
        var indices = Seq(V("n"), Comma, V("p"), Comma, V("j"));
        Formula Output(string name) => Seq(new Formula.Subscript(V(name), V("x")), Caret, Grp(indices),
            Open, V("q"), Close);

        return Paragraph(Text("“More generally, one may ask whether it holds that if "), Math(sequence),
            Text(" is a strongly "), Math(V("q")), Text("-log-concave sequence of polynomials in "), Math(Poly()),
            Text(", then, for each particular choice of "), Math(V("n")), Text(", "), Math(V("p")),
            Text(", and "), Math(V("j")), Text(", the sequences of coefficients of the polynomials "),
            Math(Output("E")), Text(" and "), Math(Output("H")), Text(" are themselves log-concave.”"));
    }

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
