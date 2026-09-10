using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class SignedCatalanCubicSubstitutionModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2025a386666");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A386666 satisfy Hanna's ternary residue conjecture.",
        H("Signed Catalan Cubic Substitution Modulo Three"),
        Blocks(
            Paragraph(Text(
                "The equation and conjecture are recorded in hanna2025a386666. All indices "
                + "are natural numbers. A denotes generatingSeries and has integer coefficients a; "
                + "S denotes signedCatalanSeries over ZMod 3. The function p denotes distinctPowersOfThree. "
                + "The operation subst(f,u) means composition f(u). All remainders in the "
                + "conjecture are integer remainders.")),
            Node("generatingSeries", "The integral generating series", GeneratingFormula(),
                "Choose an integer series satisfying the displayed normalization and equation. "
                + "Existence follows by constructing its compositional inverse B=XH. The "
                + "normalized equation is H(X^2)=H^2+4X with H(0)=1. Frobenius modulo two "
                + "makes every coefficient correction divisible by two, and each correction "
                + "improves agreement by one degree.", DescribeRole.Definition),
            Node("a", "The coefficient sequence", CoefficientFormula(),
                "The sequence consists of the coefficients of A, including a(0)=0.",
                DescribeRole.Definition),
            Node("generating_equation", "The OEIS equation", Disp(NormalizedEquation(A())),
                "Composing the equation for B with its two-sided compositional inverse gives "
                + "A^2=A(X^2+4A^3). Reversion preserves the specified linear coefficient.",
                DescribeRole.Theorem),
            Node("generating_unique", "Uniqueness with the specified normalization", UniqueFormula(),
                "For two normalized inverse factors, their first differing coefficient "
                + "contributes twice to the difference of their squares. Substitution by X^2 "
                + "uses only earlier coefficients. Cancellation of two forces agreement, "
                + "and composing back proves uniqueness of A.", DescribeRole.Theorem),
            Node("distinctPowersOfThree", "Distinct powers of three", PartitionsFormula(),
                "The Boolean all test excludes the digit two from Nat.digits 3 n. The resulting "
                + "indicator is the A039966 characterization in hanna2025a386666, including "
                + "the empty digit list at zero.", DescribeRole.Definition),
            Node("signedCatalanSeries", "The signed Catalan series", SignedFormula(),
                "The coefficientwise series with coefficients p(n) is denoted D in the proof. "
                + "Thus S=1-(1+X)D over ZMod 3.", DescribeRole.Definition),
            Node("signed_catalan_mod_three", "The signed Catalan identity and residues", SignedTheoremFormula(),
                "Ternary digits give p(3n)=p(n), p(3n+1)=p(n), and p(3n+2)=0. Hence "
                + "D=(1+X)D(X^3). Frobenius and cancellation of the unit D imply "
                + "(1+X)D^2=1, which yields S+S^2=X. Quadratic uniqueness then proves "
                + "the cubic substitution identity. Reading coefficients of 1-(1+X)D "
                + "gives the three residue formulas for positive n.", DescribeRole.Theorem),
            Node("hanna_conjecture", "Hanna's conjecture", ConjectureFormula(),
                "Reduction of the integral equation modulo three replaces four by one. "
                + "Uniqueness identifies this reduction with S. Its coefficient formulas "
                + "give each of the three asserted integer remainders.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a386666-signed-catalan-cubic-substitution-mod-three"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula ModThree() => Call("ZMod", D(3));
    private static Formula Series(Formula ring) => Call("PowerSeries", ring);
    private static Formula N() => F.Id("n");
    private static Formula X() => F.Id("X");
    private static Formula A() => F.Id("A");
    private static Formula S() => F.Id("S");
    private static Formula P(Formula n) => Call("p", n);
    private static Formula Coeff(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula Equal(Formula lhs, Formula rhs) => Seq(lhs, Sp, Eq, Sp, rhs);
    private static Formula Add(Formula lhs, Formula rhs) =>
        new Formula.Binary(lhs, FormulaBinaryOperator.Add, rhs);
    private static Formula Subtract(Formula lhs, Formula rhs) =>
        new Formula.Binary(lhs, FormulaBinaryOperator.Subtract, rhs);
    private static Formula Mul(Formula lhs, Formula rhs) =>
        new Formula.Binary(lhs, FormulaBinaryOperator.Multiply, rhs);
    private static Formula Power(Formula value, byte exponent) =>
        new Formula.Power(Parenthesized(value), D(exponent));
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lambda(string name, Formula body) => Parenthesized(Seq(
        F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula And(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));
    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; i--) result = And(clauses[i], result);
        return result;
    }
    private static Formula Positive() => Seq(D(0), Sp, Lt, Sp, N());
    private static Formula CubicEquation(Formula f, bool reduced = false) => Equal(Power(f, 2),
        Call("subst", f, Parenthesized(Add(Power(X(), 2),
            reduced ? Power(f, 3) : Mul(D(4), Power(f, 3))))));
    private static Formula NormalizedEquation(Formula f) => All(
        Equal(Call("constantCoeff", f), D(0)), Equal(Coeff(D(1), f), D(1)), CubicEquation(f));

    private static Formula GeneratingFormula() => Disp(Equal(Cast(A(), Series(Integers())),
        Call("choose", Seq(Exists, Sp, F.Id("f"), Colon, Sp, Series(Integers()), Comma, Sp,
            Parenthesized(NormalizedEquation(F.Id("f")))))));
    private static Formula CoefficientFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Call("a", N()), Coeff(N(), A()))));
    private static Formula UniqueFormula() => Disp(Seq(Bound("f", Series(Integers())),
        Implication(Equal(Call("constantCoeff", F.Id("f")), D(0)),
            Implication(Equal(Coeff(D(1), F.Id("f")), D(1)),
                Implication(CubicEquation(F.Id("f")), Equal(F.Id("f"), A()))))));
    private static Formula PartitionsFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(P(N()), Seq(Named("if"), Sp,
            Call("all", Call("digits", D(3), N()),
                Lambda("d", Seq(F.Id("d"), Sp, Neq, Sp, D(2)))), Sp,
            Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(0)))));
    private static Formula SignedFormula() => Disp(Equal(Cast(S(), Series(ModThree())),
        Subtract(D(1), Mul(Parenthesized(Add(D(1), X())),
            Call("mk", Lambda("n", Cast(P(N()), ModThree())))))));
    private static Formula SignedTheoremFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Positive(), All(
            Equal(Call("constantCoeff", S()), D(0)), Equal(Coeff(D(1), S()), D(1)),
            Equal(Add(S(), Power(S(), 2)), X()), CubicEquation(S(), true),
            Equal(Coeff(Mul(D(3), N()), S()), Mul(D(2), Cast(P(N()), ModThree()))),
            Equal(Coeff(Add(Mul(D(3), N()), D(1)), S()), Cast(P(N()), ModThree())),
            Equal(Coeff(Add(Mul(D(3), N()), D(2)), S()), Mul(D(2), Cast(P(N()), ModThree())))))));
    private static Formula Remainder(Formula value) => new Formula.Modulo(value, D(3));
    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Positive(), All(
            Equal(Remainder(Call("a", Mul(D(3), N()))), Remainder(Mul(D(2), Cast(P(N()), Integers())))),
            Equal(Remainder(Mul(D(2), Call("a", Add(Mul(D(3), N()), D(1))))),
                Remainder(Mul(D(2), Cast(P(N()), Integers())))),
            Equal(Remainder(Call("a", Add(Mul(D(3), N()), D(2)))),
                Remainder(Mul(D(2), Cast(P(N()), Integers()))))))));
}
