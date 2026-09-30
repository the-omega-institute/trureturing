using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class TorpedoGamePerfectClassicalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/TorpedoGamePerfectClassical.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/emeriau2020torpedo");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every d >= 5, the dimension-d Torpedo Game has a perfect classical strategy: the classical value, the greatest winning probability of a one-dit prepare-and-measure strategy with shared randomness, equals 1. This is the conjecture theta^C_(d>=5) = 1 of P.-E. Emeriau, M. Howard and S. Mansfield (arXiv:2007.15643, PRX Quantum 3, 020307 (2022)), who found perfect strategies for 5 <= d <= 23.",
        H("A perfect classical strategy for the Torpedo Game"),
        Blocks(
            Node("label", "The answer to avoid", LabelFormula(),
                "Alice receives x and z in Z/d and Bob a question q in {infinity, 0, ..., d - 1}, written none for infinity and some(q) for q in Z/d. Bob wins when his answer is not label(q, x, z): the winning relations of eq. (2) are w_infinity(x, z) = {a | a != x} and w_q(x, z) = {a | a != q x - z}.",
                "label", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("win", "Winning probability", WinFormula(),
                "The winning probability with uniform referee inputs, as in eq. (cval): shared randomness l in Fin(n) drawn from mu, Alice sends j with probability e(l, x, z, j), Bob answers c to question q on message j with probability f(l, j, q, c), and the probability of a winning answer is averaged over the d^2 (d + 1) triples (x, z, q).",
                "winProb", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("values", "Classical winning probabilities", ValuesFormula(),
                "The winning probabilities of all classical strategies: finite shared randomness with a probability vector mu, and encodings and decodings that are probability vectors for every value of the randomness and every input or question. Here stdSimplex(R, X) is Mathlib's standard simplex, the functions X -> R with nonnegative values summing to 1.",
                "classicalValues", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "Eq. (11) of the paper, theta^C_(d>=5) = 1: for every d >= 5 the classical value, the greatest classical winning probability, is 1. The hypothesis NeZero(d), that d is nonzero, makes Z/d finite and holds for every d >= 5.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture", Disp(F.Id("claim")),
                "Every classical winning probability is at most 1, since each term is a probability. For the lower bound it suffices to give a deterministic strategy that wins on every input and question. For d = 5 the colouring of the paper's Fig. 9 with a tabulated decoding is checked on all 150 cases. For d >= 6, rows 2i and 2i + 1 carry two classes, {(2i, 0), (2i, 1)} together with row 2i + 1 outside columns 0 and 2, and the rest of row 2i together with (2i + 1, 0) and (2i + 1, 2); for odd d the last three rows r, r + 1, r + 2 carry three classes, row r outside -1, -2, -3 with row r + 1 at 0, 1, 3, the rest of row r + 1 with row r + 2 at 0, 2, 3, and row r at -1, -2, -3 with the rest of row r + 2. For each class and question, Bob answers an explicit value that no point of the class has as its label: the labels q x - z of a row part missing columns F miss exactly q x - F, and the chosen value in that gap avoids the labels of the other row part once d >= 6 separates the small constants involved. The strategy with one-point shared randomness and 0/1 encoding and decoding then wins with probability 1.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("torpedo-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(F.Id(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula AndAll(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula SomeOver(Formula variables, Formula domain, Formula body) =>
        Seq(Exists, Sp, variables, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Div(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, index), Sp, body);
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula ZModD() => Seq(Mathbb, Grp(F.Id("Z")), Slash, F.Id("d"));
    private static Formula Questions() => Call("Option", ZModD());
    private static Formula FinN() => Call("Fin", F.Id("n"));
    private static Formula Arrow(params Formula[] parts)
    {
        var items = new List<Formula> { parts[0] };
        foreach (var part in parts[1..])
            items.AddRange([Sp, To, Sp, part]);
        return Seq([.. items]);
    }
    private static Formula At(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Simplex(Formula index) => Call("stdSimplex", Reals(), index);
    private static Formula EType() => Arrow(FinN(), ZModD(), ZModD(), ZModD(), Reals());
    private static Formula FType() => Arrow(FinN(), ZModD(), Questions(), ZModD(), Reals());

    private static Formula LabelFormula()
    {
        Formula x = F.Id("x"), z = F.Id("z"), q = F.Id("q");
        Formula atInfinity = Equal(Call("label", Call("none"), x, z), x);
        Formula atQ = All("q", ZModD(), Equal(Call("label", Call("some", q), x, z), Sub(Mul(q, x), z)));
        return Disp(All("x", ZModD(), All("z", ZModD(), AndAll(atInfinity, atQ))));
    }

    private static Formula WinFormula()
    {
        Formula x = F.Id("x"), z = F.Id("z"), q = F.Id("q"), l = F.Id("l"), j = F.Id("j"), c = F.Id("c");
        Formula d = F.Id("d");
        Formula inner = SumOver(
            Seq(Member(c, ZModD()), Comma, Sp, Rel(c, FormulaRelationOperator.NotEqual, Call("label", q, x, z))),
            At("f", l, j, q, c));
        Formula body = SumOver(Member(x, ZModD()), SumOver(Member(z, ZModD()), SumOver(Member(q, Questions()),
            SumOver(Member(l, FinN()), Mul(At("mu", l),
                Parenthesized(SumOver(Member(j, ZModD()), Mul(At("e", l, x, z, j), Parenthesized(inner)))))))));
        Formula normaliser = Div(D(1), Mul(Pow(d, D(2)), Parenthesized(Add(d, D(1)))));
        return Disp(Equal(Call("winProb", F.Id("mu"), F.Id("e"), F.Id("f")), Mul(normaliser, Parenthesized(body))));
    }

    private static Formula ValuesFormula()
    {
        Formula v = F.Id("v"), l = F.Id("l"), x = F.Id("x"), z = F.Id("z"), j = F.Id("j"), q = F.Id("q");
        Formula conditions = AndAll(
            Member(F.Id("mu"), Simplex(FinN())),
            All("l", FinN(), All("x", ZModD(), All("z", ZModD(), Member(At("e", l, x, z), Simplex(ZModD()))))),
            All("l", FinN(), All("j", ZModD(), All("q", Questions(), Member(At("f", l, j, q), Simplex(ZModD()))))),
            Equal(Call("winProb", F.Id("mu"), F.Id("e"), F.Id("f")), v));
        Formula witnesses = SomeOver(F.Id("n"), Nats(), SomeOver(F.Id("mu"), Arrow(FinN(), Reals()),
            SomeOver(F.Id("e"), EType(), SomeOver(F.Id("f"), FType(), conditions))));
        return Disp(Equal(Call("classicalValues", F.Id("d")),
            Seq(OpenBrace, v, Sp, Mid, Sp, witnesses, CloseBrace)));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d");
        Formula body = Implies(Call("NeZero", d), Implies(Rel(D(5), FormulaRelationOperator.LessThanOrEqual, d),
            Call("IsGreatest", Call("classicalValues", d), D(1))));
        return Disp(Iff(F.Id("claim"), All("d", Nats(), body)));
    }
}
