using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class TriangleSymmetricLocalRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/baumer2024trianglelocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "There is a distribution that is local in the triangle network and fully symmetric, with four outcomes per party, such that p(A = B = C) = 41/144 > 1/4. This answers yes the open problem of E. B\u00e4umer, V. Gitton, T. Kriv\u00e1chy, N. Gisin and R. Renner (arXiv:2405.08939), whose best local construction reached 1/4.",
        H("A fully symmetric triangle-local distribution with p(A = B = C) above 1/4"),
        Blocks(
            Node("local", "Locality in the triangle network", LocalFormula(),
                "Eq. (trilocal) of the paper: the three sources are uniform on [0, 1], Alice's output depends on the sources beta and gamma, Bob's on gamma and alpha, and Charlie's on alpha and beta. The responses p_A, p_B and p_C are measurable conditional distributions over the four outcomes; the conditions displayed for p_A are imposed on p_B and p_C as well.",
                "IsTriangleLocal", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("symmetric", "Fully symmetric distributions", SymmetricFormula(),
                "Invariance under every permutation of the three parties and under every joint relabelling of the four outcomes.",
                "FullySymmetric", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("s111", "Probability that all outputs agree", S111Formula(),
                "The quantity s_111 = p(A = B = C) of the paper.",
                "s111", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The bound one quarter", ClaimFormula(),
                "The negative answer to the open problem: every local fully symmetric distribution has p(A = B = C) at most 1/4.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A local fully symmetric distribution above one quarter",
                Disp(new Formula.Not(F.Id("claim"))),
                "Let each source send one of the 12 ordered pairs x = (x_1, x_2) of distinct outcomes, uniformly, and let every party apply the rule f(x, y) = x_2 if x_2 is one of y_1, y_2, and x_1 otherwise, to its two sources in cyclic order: A = f(beta, gamma), B = f(gamma, alpha), C = f(alpha, beta). Cutting [0, 1] into 12 equal cells turns this into responses on [0, 1]; each cell has measure 1/12 and the integral factorises over the cells, so p(a, b, c) is the number of source triples with outputs (a, b, c) divided by 12^3 = 1728. A kernel-checked count over the 1728 triples gives 123 when a = b = c, 19 when exactly two outputs agree and 23 when all differ. This depends only on how many outputs are distinct, which neither a relabelling of the outcomes nor a permutation of the parties changes, so p is fully symmetric, and p(A = B = C) = 4 * 123 / 1728 = 41/144 > 1/4.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("triangle-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula AllOver(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, index), Sp, body);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(byte n) => Call(F.Id("Fin"), D(n));
    private static Formula PermOf(byte n) => Call(F.Id("Perm"), FinOf(n));
    private static Formula Quarter() => Seq(Frac, Grp(D(1)), Grp(D(4)));
    private static Formula P(params Formula[] arguments) => new Formula.Apply(F.Id("p"), [.. arguments]);
    private static Formula Response(string party, params Formula[] arguments) =>
        new Formula.Apply(new Formula.Subscript(F.Id("p"), F.Id(party)), [.. arguments]);

    private static Formula LocalFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), x = F.Id("x"), y = F.Id("y");
        Formula responseType = Seq(FinOf(4), Sp, To, Sp, Reals(), Sp, To, Sp, Reals(), Sp, To, Sp, Reals());
        Formula nonnegative = All("a", FinOf(4), All("x", Reals(), All("y", Reals(),
            Rel(D(0), FormulaRelationOperator.LessThanOrEqual, Response("A", a, x, y)))));
        Formula normalised = All("x", Reals(), All("y", Reals(),
            Equal(SumOver(a, Response("A", a, x, y)), D(1))));
        Formula cube = Seq(OpenBracket, D(0), Comma, D(1), CloseBracket, Caret, Grp(D(3)));
        Formula integrand = Times(Times(Response("A", a, Beta, GammaLower),
            Response("B", b, GammaLower, Alpha)), Response("C", c, Alpha, Beta));
        Formula integral = Seq(Int, Underscore, Grp(cube), Sp, integrand, Sp,
            F.Id("d"), Alpha, Sp, F.Id("d"), Beta, Sp, F.Id("d"), GammaLower);
        Formula trilocal = All("a", FinOf(4), All("b", FinOf(4), All("c", FinOf(4),
            Equal(P(a, b, c), integral))));
        Formula responses = Seq(new Formula.Subscript(F.Id("p"), F.Id("A")), Comma, Sp,
            new Formula.Subscript(F.Id("p"), F.Id("B")), Comma, Sp,
            new Formula.Subscript(F.Id("p"), F.Id("C")));
        Formula body = Seq(Exists, Sp, responses, Sp, Colon, Sp, responseType, Comma, Sp,
            And(nonnegative, And(normalised, trilocal)));
        return Disp(Iff(Call(F.Id("IsTriangleLocal"), F.Id("p")), body));
    }

    private static Formula SymmetricFormula()
    {
        Formula o = F.Id("o"), a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula pi = Pi, sigma = SigmaLower;
        Formula oOf(Formula i) => new Formula.Apply(o, [i]);
        Formula oPi(byte i) => oOf(new Formula.Apply(pi, [D(i)]));
        Formula parties = AllOver(pi, PermOf(3), All("o", Seq(FinOf(3), Sp, To, Sp, FinOf(4)),
            Equal(P(oPi(0), oPi(1), oPi(2)), P(oOf(D(0)), oOf(D(1)), oOf(D(2))))));
        Formula sigmaOf(Formula z) => new Formula.Apply(sigma, [z]);
        Formula outcomes = AllOver(sigma, PermOf(4), All("a", FinOf(4), All("b", FinOf(4), All("c", FinOf(4),
            Equal(P(sigmaOf(a), sigmaOf(b), sigmaOf(c)), P(a, b, c))))));
        return Disp(Iff(Call(F.Id("FullySymmetric"), F.Id("p")), And(parties, outcomes)));
    }

    private static Formula S111Formula()
    {
        Formula k = F.Id("k");
        return Disp(Equal(Call(F.Id("s111"), F.Id("p")), SumOver(k, P(k, k, k))));
    }

    private static Formula ClaimFormula()
    {
        Formula p = F.Id("p");
        Formula bound = Rel(Call(F.Id("s111"), p), FormulaRelationOperator.LessThanOrEqual, Quarter());
        Formula body = All("p", Seq(FinOf(4), Sp, To, Sp, FinOf(4), Sp, To, Sp, FinOf(4), Sp, To, Sp, Reals()),
            Implies(Call(F.Id("IsTriangleLocal"), p), Implies(Call(F.Id("FullySymmetric"), p), bound)));
        return Disp(Iff(F.Id("claim"), body));
    }
}
