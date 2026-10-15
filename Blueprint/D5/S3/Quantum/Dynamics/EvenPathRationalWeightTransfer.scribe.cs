using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class EvenPathRationalWeightTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/EvenPathRationalWeightTransfer.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/kirkland2019rationalweightspst");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kirkland, McLaren, Pereira, Plosker and Zhang (arXiv:1708.03283) conjecture that a weighted path on at least four vertices, with or without potentials, whose edge weights are all rational has no perfect state transfer between its end vertices at readout time pi, and prove it for n = 4 and for n congruent to 3 or 5 modulo 8. The statement holds for every even number of vertices n = 2m with m congruent to 2 modulo 4 or to 3 or 5 modulo 8, that is for n congruent to 4 modulo 8 or to 6 or 10 modulo 16, with arbitrary real potentials and in both directions. The conjecture is not settled for n congruent to 0 modulo 8 or to 2 or 14 modulo 16.",
        H("No perfect state transfer at time pi on rational paths with 2m vertices, m = 2 mod 4 or m = 3, 5 mod 8"),
        Blocks(
            Node("residue", "Residue modulo 4 of the second Hankel determinant of the nodal moments", ResidueFormula(),
                "Let C p be the nodal moment of order p and degree k of A against B, the coefficient of X^k in the remainder of X^p P_B modulo P_A, for the monic polynomials P_A and P_B whose roots are the k + 1 even integers z l, l in A, and the k + 1 odd integers z l, l in B. Modulo 4 a product of k + 1 factors y + 2 e_l equals y^k (y + 2 sum_l e_l), because 2 * 2 = 0; hence P_A reduces to X^k (X + c) and P_B to (X + 1)^k (X + 1 + d) with c and d even residues, so that c^2 = d^2 = 0. Since (X - c) X^k (X + c) = X^(k+2), the coefficient of X^k in the remainder of a polynomial g modulo X^k (X + c) is the coefficient of X^(k+1) in (X - c) g. For g = X^p (X + 1)^k (X + 1 + d) and p <= k + 1 this is the coefficient of X^(p+1) in the reflected polynomial (1 - c X)(1 + X)^k (1 + X + d X), the factor (X + 1)^k being palindromic. Therefore, modulo 4, C 0 = k + (1 + d - c), C 1 = C(k, 2) + (1 + d - c) k - c (1 + d) and C 2 = C(k, 3) + (1 + d - c) C(k, 2) - c (1 + d) k. By the Vandermonde identity and the divisibility of C(8, i) by 4 for 1 <= i <= 3, the binomial coefficients C(k, j) with j <= 3 depend modulo 4 only on k modulo 8. The hypothesis on k + 1 says that k is congruent to 1, 5, 2 or 4 modulo 8, and evaluating the three expressions for the residues c, d with c^2 = d^2 = 0 in each of the four cases gives C 0 C 2 - (C 1)^2 = 3 when k + 1 is congruent to 2 modulo 4 and C 0 C 2 - (C 1)^2 = 2 when k + 1 is congruent to 3 or 5 modulo 8. In the formal statement the congruence is the equality of the image of the integer C 0 C 2 - (C 1)^2 in the integers modulo 4 with the conditional value 3 or 2, mod is the remainder of the division of natural numbers, and A and B are arbitrary finite sets of indices with the stated sizes and parities. For n = 4 the source shows that an explicit integer attached to the weight next to the middle edge is congruent to 3 or 7 modulo 8; the residues for general k are derived here.",
                "nodalMoment_det_mod_four", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The rational weights statement on 2m vertices, m = 2 mod 4 or m = 3, 5 mod 8", ClaimFormula(),
                "For m >= 2 with m congruent to 2 modulo 4 or to 3 or 5 modulo 8, and the path on n = 2m vertices with edge weights r in Fin(2m - 1) -> R and potentials q in Fin(2m - 1 + 1) -> R: if every weight is rational and positive, there is no perfect state transfer at time pi from the first vertex 0 to the last vertex 2m - 1, nor from the last vertex to the first. The rationality hypothesis is written as the existence of a rational number equal to each weight, and mod is the remainder of the division of natural numbers. The source states its conjecture for all n >= 4; the statement is the restriction of that conjecture to the sizes n = 2m with m in these residue classes.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "Rational paths with 2m vertices, m = 2 mod 4 or m = 3, 5 mod 8, have no transfer at time pi", Disp(F.Id("claim")),
                "By the reduction of end-to-end transfer to phase one, it suffices to show that for every choice of the potentials the entry of exp(i pi H) at the last and first vertices is not 1: the propagator is symmetric, and an entry gamma = exp(i pi theta) of modulus one becomes 1 after subtracting theta from every potential. Write m = k + 1 and suppose that this entry is 1. Then H is invariant under the reversal of the vertices. Let rho be the weight of the middle edge, r' the weight of the edge following it, and S p the moment of H^p at the sum of the two middle basis vectors. The numbers C p = rho S p are the integer nodal moments of the even spectral class against the odd one, each of k + 1 eigenvalues, and by the Gram identity C 0 C 2 - (C 1)^2 = rho^2 (S 0 S 2 - (S 1)^2) = (2 rho r')^2. If rho and r' are rational, this integer is the square of a rational number, hence the square of an integer, hence congruent to 0 or 1 modulo 4. But it is congruent to 3 modulo 4 when m is congruent to 2 modulo 4 and to 2 modulo 4 when m is congruent to 3 or 5 modulo 8. Only the rationality of the middle weight and of the weight next to it is used. The source proves the conjecture for n = 4 and for n congruent to 3 or 5 modulo 8, and for n = 4 it does so by showing that the weight next to the middle edge is irrational; m = 2 is that case. This is partial progress on the conjecture of the source: beyond n = 4 the sizes covered are n = 12, 20, 28, ... and n = 6, 10, 22, 26, ...; the sizes n congruent to 0 modulo 8 and to 2 or 14 modulo 16 are not addressed.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("evenpath-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula App(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula PathH(Formula r, Formula q) => Call("pathHamiltonian", r, q);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Residue(Formula value, byte modulus, byte residue) =>
        Equal(new Formula.Modulo(value, D(modulus)), D(residue));
    private static Formula Classes(Formula m) =>
        Or(Residue(m, 4, 2), Or(Residue(m, 8, 3), Residue(m, 8, 5)));

    private static Formula ResidueFormula()
    {
        Formula iota = F.Id("iota"), z = F.Id("z"), sa = F.Id("A"), sb = F.Id("B"), k = F.Id("k"),
            l = F.Id("l");
        Formula size = Add(k, D(1));
        Formula determinant = Sub(
            Mul(Call("nodalMoment", z, sa, sb, k, D(0)), Call("nodalMoment", z, sa, sb, k, D(2))),
            new Formula.Power(Call("nodalMoment", z, sa, sb, k, D(1)), D(2)));
        Formula residues = Call("ZMod", D(4));
        Formula value = Call("ite", Residue(Parenthesized(size), 4, 2), D(3), D(2));
        Formula conclusion = Equal(Cast(Cast(determinant, Integers()), residues), value);
        Formula evenOn = All("l", sa, Call("Even", App(z, l)));
        Formula oddOn = All("l", sb, Call("Odd", App(z, l)));
        Formula body = Implies(Equal(Call("card", sa), size), Implies(Equal(Call("card", sb), size),
            Implies(Parenthesized(evenOn), Implies(Parenthesized(oddOn),
                Implies(Parenthesized(Classes(Parenthesized(size))), conclusion)))));
        return Disp(All("iota", F.Id("Type"), All("z", Arrow(iota, Integers()),
            All("A", Call("Finset", iota), All("B", Call("Finset", iota),
                All("k", Naturals(), body))))));
    }

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("m"), r = F.Id("r"), q = F.Id("q"), j = F.Id("j"), x = F.Id("x");
        Formula h = PathH(r, q);
        Formula edgeCount = Sub(Mul(D(2), m), D(1));
        Formula edges = FinOf(edgeCount);
        Formula vertices = FinOf(Add(edgeCount, D(1)));
        Formula last = Call("last", edgeCount);
        Formula rational = All("j", edges, Some("x", Rationals(), Equal(App(r, j), x)));
        Formula positive = All("j", edges, Less(D(0), App(r, j)));
        Formula noTransfer = And(new Formula.Not(Call("HasPST", h, Pi, D(0), last)),
            new Formula.Not(Call("HasPST", h, Pi, last, D(0))));
        Formula body = All("m", Naturals(), Implies(LessEq(D(2), m), Implies(Parenthesized(Classes(m)),
            All("r", Arrow(edges, Reals()), All("q", Arrow(vertices, Reals()),
                Implies(Parenthesized(rational), Implies(Parenthesized(positive), noTransfer)))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
