using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaLambertCubeModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaLambertCubeModThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a382318");
    private static readonly LibraryNoteRef RelatedSource =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2025a382319");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Lambert transform connects Hanna's two cubic equations; cubic Frobenius gives their coefficient congruences modulo three.",
        H("Hanna's Lambert-Cube Congruences Modulo Three"),
        Blocks(
            Paragraph(Text("The series have rational coefficients and constant coefficient zero. "
                + "PowerSeries.coeff extracts a coefficient, X is the indeterminate, and "
                + "Nat.div is Euclidean division on natural numbers. Integer coefficients are "
                + "cast to the rationals in coefficient equalities. Int.ModEq(3,u,v) means "
                + "that u and v have the same residue modulo three.")),
            Node("lambertSum", "The coefficientwise Lambert sum", LambertFormula(),
                "For a series F with constant coefficient zero, Sum_{n>=1} F(x^n) has at "
                + "degree m the sum of coeff(m/n,F) over positive divisors n of m. The empty "
                + "sum at m=0 is zero; each other coefficient is a finite sum.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsA382318", "The A382318 equation", AFormula(),
                "OEIS A382318, Name (unpaginated): \"G.f. A(x) satisfies A(x) = x + "
                + "( Sum_{n>=1} A(x^n) )^3.\" The series A has zero constant coefficient, "
                + "as specified by the entry's offset one. The displayed cube is an ordinary ring power.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsA382319", "The A382319 equation", BFormula(),
                "OEIS A382319, Name (unpaginated): \"G.f. A(x) satisfies A(x) = x/(1-x) "
                + "+ Sum_{n>=1} A(x^n)^3.\" Here B denotes that entry's series. The term "
                + "x/(1-x) is X times the ring inverse of 1-X, and Sum_{n>=1} B(x^n)^3 "
                + "is lambertSum(B^3). The constant coefficient is zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(RelatedSource)),
            Node("claim", "The two coefficient congruences", Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                "OEIS A382318, Comments (unpaginated): \"Conjectures: a(3*n) == A382319(n) "
                + "(mod 3) for n >= 0; a(3*n+1) == 0 (mod 3) and a(3*n+2) == 0 (mod 3) "
                + "for n >= 1.\" In the formula A is the A382318 series and B the A382319 "
                + "series. Both exist, and every such pair has integer coefficients at the "
                + "displayed indices with the stated residues. Indices include zero in the "
                + "first congruence. The latter two start at n=1, leaving a(1)=1 unrestricted.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Hanna's congruences hold", Disp(ClaimBody()),
                "The transformation F maps to X plus the cube of its Lambert sum preserves "
                + "zero constant coefficient and improves finite coefficient agreement by one "
                + "degree. Iteration from zero therefore stabilizes coefficient by coefficient "
                + "over every commutative ring, and the fixed point is unique. Mapping the "
                + "integer fixed point into the rationals gives the rational solution. "
                + "Linearity of the Lambert sum and lambertSum(X)=X*(1-X) inverse show that "
                + "B=lambertSum(A) and A=X+B^3 for every pair of solutions. Reducing this "
                + "identity modulo three and applying cubic Frobenius gives A=X+B(X^3). "
                + "Extracting coefficients proves all three residue assertions.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hanna-a382318-a382319-lambert-cube-mod-three"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hanna318-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Rationals());
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula And(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula ImpliesTo(Formula premise, Formula conclusion) => Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Coeff(Formula index, Formula series) => Call("coeff", index, series);
    private static Formula RationalCast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Rationals()));
    private static Formula ModEq(Formula left, Formula right) => App(Qualified("Int", "ModEq"), D(3), left, right);

    private static Formula LambertFormula()
    {
        Formula f = F.Id("F");
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula summand = Call("ite", Seq(n, Sp, Mid, Sp, m),
            Coeff(App(Qualified("Nat", "div"), m, n), f), D(0));
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(n, Sp, InMacro, Sp,
            App(Qualified("Finset", "Icc"), D(1), m))), Sp, summand);
        Formula body = Call("mk", Parenthesized(Seq(m, Colon, Sp, Naturals(), Sp, Mapsto, Sp, sum)));
        return Disp(All("F", Series(), Equal(Call("lambertSum", f), body)));
    }

    private static Formula AFormula()
    {
        Formula a = F.Id("A");
        return Disp(All("A", Series(), Equal(Call("IsA382318", a), Parenthesized(And(
            Equal(Call("constantCoeff", a), D(0)), Equal(a,
                Add(F.Id("X"), Power(Call("lambertSum", a), D(3)))))))));
    }

    private static Formula BFormula()
    {
        Formula b = F.Id("B");
        Formula oneMinusX = new Formula.Binary(D(1), FormulaBinaryOperator.Subtract, F.Id("X"));
        Formula inverse = Power(Parenthesized(oneMinusX), Seq(Minus, D(1)));
        return Disp(All("B", Series(), Equal(Call("IsA382319", b), Parenthesized(And(
            Equal(Call("constantCoeff", b), D(0)), Equal(b,
                Add(Mul(F.Id("X"), inverse), Call("lambertSum", Power(b, D(3))))))))));
    }

    private static Formula ClaimBody()
    {
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        Formula n = F.Id("n");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula threeN = Mul(D(3), n);
        Formula pair = And(Call("IsA382318", a), Call("IsA382319", b));
        Formula exists = Some("A", Series(), Some("B", Series(), pair));
        Formula multiples = All("n", Naturals(), Some("u", Integers(), Some("v", Integers(),
            And(Equal(Coeff(threeN, a), RationalCast(u)),
                And(Equal(Coeff(n, b), RationalCast(v)), ModEq(u, v))))));
        Formula others = All("n", Naturals(), ImpliesTo(Seq(D(1), Sp, Le, Sp, n),
            Some("u", Integers(), Some("v", Integers(),
                And(Equal(Coeff(Add(threeN, D(1)), a), RationalCast(u)),
                    And(Equal(Coeff(Add(threeN, D(2)), a), RationalCast(v)),
                        And(ModEq(u, D(0)), ModEq(v, D(0)))))))));
        Formula universal = All("A", Series(), All("B", Series(),
            ImpliesTo(Call("IsA382318", a), ImpliesTo(Call("IsA382319", b), And(multiples, others)))));
        return And(exists, universal);
    }
}
