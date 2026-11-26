using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaChebyshevHeckeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaChebyshevHecke";

    public DocumentDefinition Create()
    {
        Formula x = F.Id("x"), n = F.Id("n"), k = F.Id("k"), a = F.Id("a");
        Formula zero = D(0), one = D(1), two = D(2);
        Formula integers = Seq(Mathbb, Grp(F.Id("Z"))), rationals = Seq(Mathbb, Grp(F.Id("Q")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula phi = Varphi, phiHalf = Div(phi, two);
        Formula dx = Call("deletedShell", F.Id("x")), dy = Call("deletedShell", F.Id("y"));
        Formula g = F.Id("g"), j = F.Id("j"), b = F.Id("b");
        Formula v = F.Id("v"), l = F.Id("l"), line = Call("vector", l);
        Formula dz = Call("deletedShell", F.Id("z"));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact Chebyshev and spherical character identities for Chapter 32, section 32.8, and Appendix Q.",
            H("Chebyshev identities and rational harmonics"),
            Blocks(
                Law("pell-chebyshev", "pell_chebyshev", "The Pell–Chebyshev identity",
                    Bound(integers, Bound(naturals, Eq(Sub(Sq(Call("T", Add(n, one), x)),
                        Mul(Sub(Sq(x), one), Sq(Call("U", n, x)))), one), "n"), "x"),
                    "The recurrence preserves the quadratic norm of the first-kind and shifted second-kind coordinates."),
                Law("chebyshev-doubling", "chebyshev_doubling", "Doubling the Chebyshev index",
                    Bound(integers, Bound(naturals, Eq(Call("T", Mul(two, n), x),
                        Sub(Mul(two, Sq(Call("T", n, x))), one)), "n"), "x"),
                    "The addition formula at two equal indices and the Pell identity give the displayed square."),
                Law("even-chebyshev", "even_chebyshev", "Even characters depend on the squared input",
                    Bound(integers, Bound(naturals, Eq(Call("E", n, Sq(x)), Call("U", Mul(two, n), x)), "n"), "x"),
                    "The even-index subsequence satisfies a recurrence with multiplier four times the squared input minus two. This gives the integer-spin spherical characters."),
                Law("odd-chebyshev", "odd_chebyshev", "Odd characters retain the signed input",
                    Bound(integers, Bound(naturals, Eq(Mul(x, Call("oddFactor", n, Sq(x))),
                        Call("U", Add(Mul(two, n), one), x)), "n"), "x"),
                    "The polynomial multiplying the argument only depends on its square. The signed factor distinguishes opposite arguments."),
                Law("spin-two-character", "spin_two_character", "The rational spin-two character",
                    Bound(rationals, Eq(Call("E", two, k), Add(Sub(Mul(D(1,6), Sq(k)), Mul(D(1,2), k)), one)), "k"),
                    "The second term of the even character recurrence is a degree-two polynomial in the squared input."),
                Law("pentagonal-chebyshev", "pentagonal_chebyshev", "Exact pentagonal closures",
                    And(Eq(Call("T", D(5), phiHalf), Seq(Minus, one)), And(
                        Eq(Call("T", D(1,0), phiHalf), one),
                        Eq(Call("T", D(5), Div(Sub(phi, one), two)), one))),
                    "Doubling each evaluation gives a recurrence entirely in integral golden coefficients."),
                Law("orbital-quadrupole", "orbital_quadrupole", "Closed and depleted orbital shells",
                    And(Bound(F.Id("Axes"), Eq(Call("closedShell", a), zero), "a"),
                        And(Eq(dx, Div(Seq(Minus, D(4)), D(7))), And(
                            Eq(dy, Div(Seq(Minus, D(4)), D(7))), And(
                            Eq(dz, Div(D(8), D(7))), Eq(Add(Add(dx, dy), dz), zero))))),
                    "Axes are the three Cartesian directions. The five real d orbitals have a vanishing total diagonal quadrupole. Deleting both electrons in the d orbital with angular polynomial x squared minus y squared leaves the displayed diagonal and zero trace."),
                Law("full-orbital-quadrupole", "full_orbital_quadrupole", "The five orbital diagonals sum to zero",
                    Bound(F.Id("Axes"), Eq(Call("fullShell", a), zero), "a"),
                    "This sum counts each real orbital once. Counting each twice gives the doubly occupied closed shell."),
                Law("lps-norm-five-overlap", "lps_norm_five", "Norm and overlap of the six generators",
                    Bound(F.Id("Generators"), And(Eq(Call("normSq", g), D(5)),
                        Eq(Call("kappa", g), Div(one, D(5)))), "g"),
                    "The generator set consists of the six quaternions with scalar part one and exactly one nonzero vector coordinate equal to plus or minus two."),
                Law("lps-hecke-trace-formula", "lps_hecke_trace_formula", "Character of the six-generator average",
                    Bound(naturals, Eq(Call("averageCharacter", n),
                        Div(Call("traceNumerator", n), new Formula.Power(D(5), n))), "n"),
                    "The rotation-character model assigns each summand E evaluated at one fifth. Its average has the same character value, with denominator five to the degree in the displayed representative."),
                Law("lps-hecke-traces", "lps_hecke_traces", "The first six exact character trace values",
                    And(Eq(Call("traceRepresentative", one), Div(Seq(Minus, one), D(5))),
                        And(Eq(Call("traceRepresentative", two), Div(Seq(Minus, D(1,9)), D(2,5))),
                        And(Eq(Call("traceRepresentative", D(3)), Div(D(1,3,9), D(1,2,5))),
                        And(Eq(Call("traceRepresentative", D(4)), Div(Seq(Minus, D(3,5,9)), D(6,2,5))),
                        And(Eq(Call("traceRepresentative", D(5)), Div(Seq(Minus, D(1,3,2,1)), D(3,1,2,5))),
                            Eq(Call("traceRepresentative", D(6)), Div(D(1,6,9,0,1), D(1,5,6,2,5)))))))),
                    "These fractions are the scaled representatives in the preceding character trace formula. Their numerators start at one and minus one, then satisfy a recurrence with coefficients minus six and minus twenty-five."),
                Law("lps-ramanujan-margins", "lps_ramanujan_margins", "Positive Ramanujan margins in the four spin shells",
                    Bound(F.Id("Shells"), Bound(F.Id("Branches"),
                        And(Eq(Call("substitutionMatrix", j), Call("integerMatrix", j)),
                            Lt(zero, Sub(D(2,0), Call("lambdaSquared", j, b)))), "b"), "j"),
                    "The first equality compares each monomial coefficient against the displayed integer matrix of the six-generator sum. Dividing each generator by the positive square root of five before taking its symmetric power gives the squared-eigenvalue denominator five to the degree. The first three integer matrices are scalar and the spin-two shell has two eigenvalue branches."),
                Law("lps-degree-four-eigenbasis", "lps_degree_four_eigenbasis", "Eigenbasis for spin two",
                    And(Bound(F.Id("Lines"), Eq(Call("action", line),
                            Mul(Call("scaledEigenvalue", Call("branch", l)), line)), "l"),
                        Bound(F.Id("Vectors"), And(
                            Eq(Call("fromEigen", Call("doubledEigen", v)), Mul(two, v)),
                            Eq(Call("doubledEigen", Call("fromEigen", v)), Mul(two, v))), "v")),
                    "The action here is the degree-four integer matrix matched in the Ramanujan margin theorem. Its two branch values 54 and −74 give squared eigenvalues 54²/625 and 74²/625 in that theorem. The five eigenlines are the sum and difference of the two outer monomials and the three interior monomials. The basis changes compose to twice the identity in both orders, giving a basis over the rationals."))));

    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Bound(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Sq(Formula term) => new Formula.Power(term, D(2));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static DocumentBlock.Describe Law(string id, string selector, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Module}.{selector}"),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
