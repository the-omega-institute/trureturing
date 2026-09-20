using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class SharmaPrimitivePolynomialRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/sharma2026primitivepolynomials");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A degree-41 finite-field certificate refutes Sharma's full primitive-polynomial conjecture.",
        H("Sharma's primitive-polynomial Conjecture 4.2 is false"),
        Blocks(
            Node("SourcePrimitivePolynomial", "The source multiplicative-generator property",
                SourcePrimitiveFormula(),
                "SourcePrimitivePolynomial is the source meaning of monic minimal polynomial: "
                    + "there must be an extension L of degree p containing an element alpha whose "
                    + "minimal polynomial is the displayed polynomial and whose multiplicative order "
                    + "is card(L)-1. This is not Polynomial.IsPrimitive, which is the unrelated "
                    + "coefficient-content predicate.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("PrimitiveLambda", "A multiplicative generator in the base field",
                PrimitiveLambdaFormula(),
                "PrimitiveLambda(lam) means orderOf lam equals card(K)-1. The source quantifies "
                    + "over every such lambda in every finite field of cardinality p squared.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("SourceLeadingCoefficient", "The source leading coefficient",
                Equal(F.Id("SourceLeadingCoefficient"), F.D(1)),
                "The actual source coefficient is 1 in Fin 2. This constant occurs in the "
                    + "original public theorem statement and fixes the monic source polynomial.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("sourcePolynomial", "The coefficient-parameterized source polynomial",
                SourcePolynomialFormula(),
                "For a coefficient c, sourcePolynomial is C(val(c)) X^p + X + C(lam). "
                    + "The actual source coefficient is the Fin 2 value 1; the coefficient parameter "
                    + "is retained in the full polynomial family.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("claimFor", "The complete universal source claim at one coefficient",
                Iff(Call("claimFor", F.Id("c")), ClaimForFormula(F.Id("c"))),
                "The quantifier order is the source order: every natural odd prime p, every finite "
                    + "field K of cardinality p squared and characteristic p, and every multiplicative "
                    + "generator lambda. No coefficient-content interpretation or finite-prime weakening "
                    + "is substituted.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("fullClaim", "Sharma's full Conjecture 4.2",
                new Formula.Logic(F.Id("fullClaim"), FormulaLogicOperator.Iff,
                    ClaimForFormula(F.D(1))),
                "This is the literal global conjecture with SourcePrimitivePolynomial as its "
                    + "conclusion. Its negation is the public result below.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("publicResult", "The public negation target", null,
                "publicResult is definitionally the negation of claimFor SourceLeadingCoefficient. "
                    + "The Lean theorem result proves this proposition unconditionally.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("QuadraticField41", "The executable quadratic field at p equals 41", null,
                "The counterexample field is QuadraticAlgebra (ZMod 41) 3 0, with the nonsquare "
                    + "witness and finite cardinality supplied in Lean. Its cardinality is 41 squared.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("lambda41", "The primitive lambda certificate", null,
                "lambda41 is the element 5 + u in the quadratic algebra. The kernel-checked power "
                    + "chain proves order 1680, which is the nonzero-group order 1681 minus one.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("certificateCoefficients", "The dense coefficient list", null,
                "The eight-product certificate starts from the explicit 41-entry coefficient list. "
                    + "Every list entry is a concrete element of the quadratic field and is consumed "
                    + "by the kernel-checked coefficient reducer.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("certificatePolynomial", "The certificate polynomial", null,
                "certificatePolynomial is the Horner polynomial reconstructed from the full coefficient "
                    + "list. Its product identities are checked in the kernel rather than imported as a "
                    + "numeric assertion.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("certificateN", "The hypothetical extension group order",
                Equal(F.Id("certificateN"),
                    Subtract(new Formula.Power(F.D(1, 6, 8, 1), F.D(4, 1)), F.D(1))),
                "The hypothetical degree-41 extension has this nonzero-group order. It is "
                    + "divisible by 83, and its quotient by 83 is positive and strictly smaller.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("denseCertificateIdentityFor", "The universal root certificate",
                DenseCertificateFormula(),
                "This predicate states that, for every field extension L and every root alpha of the "
                    + "coefficient-dependent source polynomial, evaluating the certificate polynomial "
                    + "gives z with z^83 = alpha. The private certificate_evaluation theorem proves "
                    + "this property at SourceLeadingCoefficient, and result uses that theorem.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Definition),
            Node("result", "The full source conjecture is false", ResultFormula(),
                "At p=41 take K = QuadraticAlgebra (ZMod 41) 3 0 and lambda = 5 + u. The "
                    + "certificate proves lambda has full multiplicative order 1680. If the source "
                    + "claim supplied an extension L of degree 41 with a primitive root alpha of the "
                    + "polynomial X^41 + X + lambda, the eight exact product identities would give "
                    + "z^83 = alpha. Since L has cardinality 1681^41, the finite-field exponent gives "
                    + "z^(card(L)-1)=1, hence alpha^((1681^41-1)/83) = 1. This forces the claimed order "
                    + "card(L)-1 to divide a strict smaller positive exponent, a contradiction. Thus "
                    + "the full universal conjecture is negated unconditionally. The certificate is for "
                    + "the source multiplicative-generator/minimal-polynomial meaning, not a polynomial "
                    + "coefficient-content surrogate.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string name, string title, Formula? formula, string prose,
        AssessedProvenance provenance, DescribeRole role) => Describe.Lean(
        DescribeId.Create("sharma-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(formula)),
        provenance,
        Blocks(Paragraph(Text(prose))), role);

    private static Formula SourcePrimitiveFormula()
    {
        var p = F.Id("p"); var K = F.Id("K"); var f = F.Id("f");
        var L = F.Id("L"); var alpha = F.Id("alpha");
        var extension = And(Call("Field", L), And(Call("Fintype", L), Call("Algebra", K, L)));
        var witness = And(Equal(Call("finrank", K, L), p),
            And(Equal(Call("minpoly", K, alpha), f),
                Equal(Call("orderOf", alpha), Subtract(Call("card", L), F.D(1)))));
        return Iff(Call("SourcePrimitivePolynomial", p, K, f),
            Exists("L", F.Id("Type"), And(extension, Exists("alpha", L, witness))));
    }

    private static Formula PrimitiveLambdaFormula() =>
        Iff(Call("PrimitiveLambda", F.Id("lambda")),
            Equal(Call("orderOf", F.Id("lambda")),
                Subtract(Call("card", F.Id("K")), F.D(1))));

    private static Formula SourcePolynomialFormula() =>
        Equal(Call("sourcePolynomial", F.Id("p"), F.Id("c"), F.Id("lambda")),
            Add(Multiply(Call("C", Call("val", F.Id("c"))),
                    new Formula.Power(F.Id("X"), F.Id("p"))),
                Add(F.Id("X"), Call("C", F.Id("lambda")))));

    private static Formula ClaimForFormula(Formula coefficient)
    {
        var p = F.Id("p"); var K = F.Id("K"); var lambda = F.Id("lambda");
        var hypotheses = And(Call("Prime", p), Call("Odd", p));
        var fieldHypotheses = And(Call("Field", K),
            And(Call("Fintype", K), Call("CharP", K, p)));
        var conclusion = Implies(Equal(Call("card", K), new Formula.Power(p, F.D(2))),
            ForAll("lambda", Call("Element", K), Implies(
                Call("PrimitiveLambda", lambda),
                Call("SourcePrimitivePolynomial", p, K,
                    Call("sourcePolynomial", p, coefficient, lambda)))));
        return ForAll("p", F.Id("Nat"), Implies(hypotheses,
            ForAll("K", F.Id("Type"), Implies(fieldHypotheses, conclusion))));
    }

    private static Formula DenseCertificateFormula()
    {
        var L = F.Id("L"); var alpha = F.Id("alpha"); var c = F.Id("c");
        return ForAll("L", F.Id("Type"), Implies(
            And(Call("Field", L),
                Call("Algebra", F.Id("QuadraticField41"), L)),
            ForAll("alpha", L, Implies(Equal(Call("aeval", alpha,
                    Call("sourcePolynomial", F.D(4, 1), c, F.Id("lambda41"))), F.D(0)),
                Equal(new Formula.Power(Call("aeval", alpha,
                        F.Id("certificatePolynomial")), F.D(8, 3)), alpha)))));
    }

    private static Formula ResultFormula() => new Formula.Not(F.Id("fullClaim"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesize(left), FormulaLogicOperator.And, Parenthesize(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesize(left), FormulaLogicOperator.Implies, Parenthesize(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesize(left), FormulaLogicOperator.Iff, Parenthesize(right));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Parenthesize(Formula value) => Seq(Open, value, Close);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
}
