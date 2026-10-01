using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GradedCongruenceSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Linear/GradedCongruenceSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive normalized congruence has uniformly graded canonical spectrum.",
        H("Graded Congruence Spectrum"),
        Blocks(Describe.Lean(
            DescribeId.Create("graded-congruence-spectrum"),
            DeclarationHandle.Create(Prefix + "graded_congruence_spectrum"),
            H("Uniform graded bounds for the canonical decreasing spectrum"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For arbitrary n, a real matrix family H tending to a positive-definite "
                        + "H₀ from the positive side, and a monotone integer grade w, form the "
                        + "actual congruence G(T) = diag(T^(wᵢ)√T) H(T) diag(T^(wᵢ)√T). "
                        + "The hypothesis requires this same G(T) to be positive definite for "
                        + "every positive T.")),
                Paragraph(Text(
                    "The theorem derives common positive c, C and δ such that every actual "
                        + "canonical decreasing eigenvalue₀ coordinate lies between c T^(2wᵢ+1) "
                        + "and C T^(2wᵢ+1) whenever 0 < T < δ. The coordinate is transported "
                        + "only through the standard Fin cardinal order isomorphism; no supplied "
                        + "eigenvalue list, permutation, eigengap or simple-spectrum premise is "
                        + "used.")),
                Paragraph(Text(
                    "In the displayed formula, λ(T,i) is notation for the same actual coordinate "
                        + "(hG(T,p)).isHermitian.eigenvalues₀ "
                        + "((Fin.castOrderIso (Fintype.card_fin n)).symm i), where p is the "
                        + "displayed proof that T>0 and hG(T,p) is the positive-definiteness "
                        + "proof for the displayed congruence. In the formula, A denotes H₀ "
                        + "and d denotes δ. "
                        + "The convergence hypothesis is right-sided: H tends to H₀ along "
                        + "nhdsWithin(0, Ioi(0)).")),
                Paragraph(Text(
                    "The argument takes a genuine finite minimum of all "
                        + "positive H₀ principal determinants, obtains simultaneous local minor "
                        + "bounds from convergence, scales each actual principal minor, and uses "
                        + "monotone grades to compare every subset exponent with the initial "
                        + "prefix. The characteristic-polynomial coefficient/principal-minor "
                        + "identity and the actual "
                        + "Hermitian characteristic-polynomial identity identify coefficients "
                        + "with elementary symmetric sums of the same canonical spectrum. "
                        + "A zero-safe prefix-product sandwich and adjacent positive ratios "
                        + "finish the uniform powers.")),
                Paragraph(Text(
                    "The n = 0 branch, empty principal minor and empty prefix are retained; "
                        + "repeated grades and empty grade layers are allowed. This abstract "
                        + "interface does not construct the physical trajectory or moment "
                        + "Gramian, its orthonormal graded coordinates, determinant leading term, "
                        + "statistical risk, or the remaining original 5.2/5.3/6.2/6.3 clauses."))),
            DescribeRole.Theorem))));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Fin(Formula n) => Call("Fin", n);

    private static Formula MatrixReal(Formula n) =>
        Call("Matrix", Fin(n), Fin(n), Reals());

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Lambda(Formula variable, Formula body) =>
        Seq(Open, variable, Sp, Mapsto, Sp, body, Close);

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Multiply(Formula left, Formula right) =>
        Seq(left, Sp, Times, Sp, right);

    private static Formula Add(Formula left, Formula right) =>
        Seq(left, Sp, Plus, Sp, right);

    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
        {
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        }

        return result;
    }

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, conclusion);

    private static Formula Scale(Formula t) =>
        Call("diag", Lambda(F.Id("i"), Multiply(
            Power(t, Apply(F.Id("w"), F.Id("i"))), SqrtValue(t))));

    private static Formula SqrtValue(Formula value) => Seq(Sqrt, Open, value, Close);

    private static Formula Congruence(Formula t) =>
        Multiply(Multiply(Scale(t), Apply(F.Id("H"), t)), Scale(t));

    private static Formula CanonicalLambda(Formula t, Formula i) =>
        new Formula.Apply(F.LambdaLower, [t, i]);

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula h = F.Id("H");
        Formula h0 = F.Id("A");
        Formula w = F.Id("w");
        Formula t = F.Id("T");
        Formula i = F.Id("i");
        Formula c = F.Id("c");
        Formula upper = F.Id("C");
        Formula delta = F.Id("d");
        Formula real = Reals();
        Formula nat = Naturals();
        Formula fin = Fin(n);
        Formula hType = new Formula.TypeArrow(real, MatrixReal(n));
        Formula wType = new Formula.TypeArrow(fin, nat);

        Formula q(Formula index) => Add(
            Multiply(D(2), Apply(w, index)), D(1));

        Formula lower = Relation(
            Multiply(c, Power(t, q(i))),
            FormulaRelationOperator.LessThanOrEqual,
            CanonicalLambda(t, i));
        Formula upperBound = Relation(
            CanonicalLambda(t, i),
            FormulaRelationOperator.LessThanOrEqual,
            Multiply(upper, Power(t, q(i))));

        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("T"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("i"), fin),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("p"),
                    Relation(t, FormulaRelationOperator.GreaterThan, D(0))),
            ],
            Implies(
                Relation(t, FormulaRelationOperator.LessThan, delta),
                And(lower, upperBound)));

        Formula witnesses = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("c"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("C"), real),
                new Formula.BoundVariable(FormulaIdentifier.Create("d"), real),
            ],
            And(
                Relation(c, FormulaRelationOperator.GreaterThan, D(0)),
                Relation(upper, FormulaRelationOperator.GreaterThan, D(0)),
                Relation(delta, FormulaRelationOperator.GreaterThan, D(0)),
                conclusion));

        Formula positivity = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("T"),
            real,
            Implies(
                Relation(t, FormulaRelationOperator.GreaterThan, D(0)),
                Call("PosDef", Congruence(t))));

        Formula hypotheses = And(
            Call("Monotone", w),
            Call("Tendsto", h,
                Call("nhdsWithin", D(0), Call("Ioi", D(0))),
                Call("nhds", h0)),
            Call("PosDef", h0),
            positivity);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("n"), nat),
                new Formula.BoundVariable(FormulaIdentifier.Create("H"), hType),
                new Formula.BoundVariable(FormulaIdentifier.Create("A"), MatrixReal(n)),
                new Formula.BoundVariable(FormulaIdentifier.Create("w"), wType),
            ],
            Implies(hypotheses, witnesses)));
    }
}
