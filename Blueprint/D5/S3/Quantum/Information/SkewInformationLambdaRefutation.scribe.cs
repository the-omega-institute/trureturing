using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class SkewInformationLambdaRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/SkewInformationLambdaRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/yu2013skewinformation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A regular symmetric operator monotone function has a skew-information integrand below both endpoint values, refuting the proposed formula for its least value.",
        H("The skew-information endpoint formula fails"),
        Blocks(
            Node("lambdaIntegrand", "The skew-information integrand", IntegrandFormula(),
                "Appendix 2 of Yu and Oh defines lambda_f as the least value of F_f(x) for x at least zero. Here F_f(x) denotes lambdaIntegrand(f,x). The scalar definition itself accepts every real function and every real x; admissibility is imposed separately.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Admissible", "Regular symmetric operator monotone functions", AdmissibleFormula(),
                "Yu and Oh consider functions nonnegative on the nonnegative real axis, operator monotone, symmetric, normalized and regular. Operator monotonicity means that f(A) is at most f(B) whenever A and B are positive semidefinite complex matrices of any finite size and A is at most B. The order is the Loewner order, and cfc(f,A) is the continuous functional calculus. The size n ranges over all natural numbers, including zero. Symmetry is required for every positive real x; normalization is f(1) = 1 and regularity is f(0) > 0.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed least value", ClaimFormula(),
                "Appendix 2 conjectures that lambda_f = min{1, 1/(4f(0))} always holds. IsLeast(S,c) means that c belongs to S and is at most every element of S, so the formula asserts both attainment and the lower-bound property for every admissible f. The source obtains the endpoint upper bound from F_f(1) = 1 and F_f(0) = 1/(4f(0)); the conjecture asserts equality with that bound.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("yu-oh-lambda-result"), DeclarationHandle.Create(Prefix + "result"),
                H("An interior value below the endpoint bound"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take f(x) = (2/9)(1 + x) + (10/3)·x/(11x + 1) + (10/3)·x/(x + 11). For a,b > 0 and x at least zero, x/(ax + b) = 1/a − (b/a)(ax + b)⁻¹. Matrix inversion reverses order on positive definite matrices, so this identity makes each rational term operator monotone on positive semidefinite matrices of every finite size. Positive linear combinations and the affine term preserve that order. All three terms are nonnegative on the nonnegative real axis. Direct calculation gives f(0) = 2/9, f(1) = 1 and x f(1/x) = f(x) for x > 0: the two rational terms are exchanged by the symmetry and the affine term is fixed. Thus f is admissible. At x = 1/4, f(1/4) = 31/54 and F_f(1/4) = 7641/7688 < 1 = min{1, 9/8}. The proposed least value is therefore not a lower bound of the integrand, contradicting claim."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("yu-oh-2013-skew-information-lambda-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("yu-oh-lambda-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula At(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula EqTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeqTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Both(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffTo(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula RealFunction => Parenthesized(new Formula.TypeArrow(Reals, Reals));
    private static Formula IntegrandAt(Formula f, Formula x) => At(new Formula.Subscript(F.Id("F"), f), x);

    private static Formula IntegrandFormula()
    {
        Formula f = F.Id("f"), x = F.Id("x");
        Formula denominator = Multiply(D(2), At(f, x));
        Formula correction = Divide(Multiply(At(f, D(0)),
            new Formula.Power(Parenthesized(Subtract(D(1), x)), D(2))), denominator);
        Formula value = Divide(Parenthesized(Subtract(Add(D(1), x), correction)), denominator);
        return All("f", RealFunction, All("x", Reals, EqTo(IntegrandAt(f, x), value)));
    }

    private static Formula OperatorMonotone(Formula f)
    {
        Formula n = F.Id("n"), a = F.Id("A"), b = F.Id("B");
        Formula matrix = Call("Matrix", Call("Fin", n), Call("Fin", n), Complexes);
        return All("n", Naturals, All("A", matrix, All("B", matrix,
            Imp(Call("PosSemidef", a), Imp(Call("PosSemidef", b),
                Imp(LeqTo(a, b), LeqTo(Call("cfc", f, a), Call("cfc", f, b))))))));
    }

    private static Formula AdmissibleFormula()
    {
        Formula f = F.Id("f"), x = F.Id("x");
        Formula nonnegative = All("x", Reals, Imp(LeqTo(D(0), x), LeqTo(D(0), At(f, x))));
        Formula symmetric = All("x", Reals, Imp(Less(D(0), x),
            EqTo(Multiply(x, At(f, Divide(D(1), x))), At(f, x))));
        Formula body = Both(nonnegative, Both(OperatorMonotone(f),
            Both(symmetric, Both(EqTo(At(f, D(1)), D(1)), Less(D(0), At(f, D(0)))))));
        return All("f", RealFunction, IffTo(Call("Admissible", f), body));
    }

    private static Formula ClaimFormula()
    {
        Formula f = F.Id("f"), x = F.Id("x");
        Formula interval = Seq(OpenBracket, D(0), Comma, Sp, Infty, Close);
        Formula values = new Formula.SetBuilder(IntegrandAt(f, x), x, interval);
        Formula endpoint = Seq(Min, OpenBrace, D(1), Comma, Sp,
            Divide(D(1), Multiply(D(4), At(f, D(0)))), CloseBrace);
        Formula body = All("f", RealFunction,
            Imp(Call("Admissible", f), Call("IsLeast", values, endpoint)));
        return IffTo(F.Id("claim"), body);
    }
}
