using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class ApproximateOrientedAnchorRepairDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/ApproximateOrientedAnchorRepair.";

    public DocumentDefinition Create()
    {
        Formula h = F.Id("H"), w = F.Id("W"), d = F.Id("d"), a = F.Id("a");
        Formula f = F.Id("F"), delta = F.Id("delta"), x = F.Id("x"), j = F.Id("j");
        Formula k = F.Id("k"), u = F.Id("U");
        Formula real = F.Id("Real"), complex = F.Id("Complex");
        Formula B = Call("basisExtension", a, f);
        Formula G = Call("compose", Call("adjoint", B), B);
        Formula kap = Call("kappa", d, delta), et = Call("eta", d, delta);
        Formula Aj = Call("apply", a, j);
        Formula Phase(Formula z) => Call("smul", Call("pow", F.Id("i"), k), z);
        Formula Fx(Formula z) => Call("apply", f, z);
        Formula Norm(Formula z) => Call("norm", z);
        Formula Sq(Formula z) => Call("pow", z, Num(2));
        Formula Unit(Formula z) => Eqn(Norm(z), Num(1));
        Formula rootGap = Sub(Num(1), Call("sqrt", Sub(Num(1), kap)));
        Formula bound = Call("min", Num(2), Add(Call("sqrt", Add(kap, Mul(Num(2), et))), rootGap));
        Formula normLaw = All([Bound("x", h)], Implies(Unit(x), Unit(Fx(x))));
        Formula phaseLaw = All([Bound("j", Call("Fin", d)), Bound("k", Call("Fin", Num(4)))],
            Eqn(Fx(Phase(Aj)), Phase(Fx(Aj))));
        Formula comparisons = All([Bound("x", h)], Implies(Unit(x),
            All([Bound("j", Call("Fin", d)), Bound("k", Call("Fin", Num(4)))],
                Le(Sq(Norm(Sub(Fx(x), Fx(Phase(Aj))))),
                    Add(Sq(Norm(Sub(x, Phase(Aj)))), delta)))));
        Formula conclusion = And(Call("IsStrictlyPositive", G),
            Exists([Bound("U", Call("ComplexLinearIsometry", h, w))],
                And(Eqn(Call("toContinuousLinearMap", u),
                        Call("compose", B, Call("ringInverse", Call("positiveSqrt", G)))),
                    And(Le(Norm(Sub(G, Call("identity", h))), kap),
                        And(Le(Norm(Sub(B, Call("toContinuousLinearMap", u))), rootGap),
                            All([Bound("x", h)], Implies(Unit(x),
                                Le(Norm(Sub(Fx(x), Call("apply", u, x))), bound))))))));
        Formula telescope = All(
            [Bound("H", F.Id("FiniteComplexHilbertSpace")),
                Bound("W", F.Id("FiniteComplexHilbertSpace")), Bound("d", F.Id("Natural")),
                Bound("a", Call("OrthonormalBasis", Call("Fin", d), complex, h)),
                Bound("F", Call("Function", h, w)), Bound("delta", real)],
            Implies(And(Le(Num(1), d), And(Le(Num(0), delta),
                And(normLaw, And(phaseLaw, And(comparisons, Lt(kap, Num(1))))))), conclusion));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Uniform polar isometric repair from finite oriented approximate comparisons.",
            H("Approximate Oriented Anchor Repair"),
            Blocks(
                Paragraph(Text(
                    "H and W are complex finite-dimensional inner-product spaces in independent "
                    + "universes; finite dimension supplies completeness. The orthonormal basis a "
                    + "has d entries, with d at least one. W is the same complete all-outcome, "
                    + "shared-reference output used by the actual arbitrary map F. The theorem "
                    + "assumes neither linearity nor unit-sphere surjectivity of F, and no "
                    + "orthogonality of its output anchors. Every norm on a vector is its genuine "
                    + "Hilbert norm; every norm on an operator is the induced operator norm.")),
                Item("basisExtension", "Actual linear basis extension", All(
                    [Bound("H", F.Id("FiniteComplexHilbertSpace")),
                        Bound("W", F.Id("FiniteComplexHilbertSpace")), Bound("d", F.Id("Natural")),
                        Bound("a", Call("OrthonormalBasis", Call("Fin", d), complex, h)),
                        Bound("F", Call("Function", h, w))],
                    Eqn(B, Call("continuousLinearBasisExtension", a, Call("compose", f, a)))), true),
                Item("eta", "Coordinate error scale", All(
                    [Bound("d", F.Id("Natural")), Bound("delta", real)],
                    Eqn(et, Mul(Call("sqrt", Div(d, Num(2))), delta))), true),
                Item("kappa", "Gram perturbation scale", All(
                    [Bound("d", F.Id("Natural")), Bound("delta", real)],
                    Eqn(kap, Mul(Div(Sub(d, Num(1)), Call("sqrt", Num(2))), delta))), true),
                Paragraph(Text(
                    "Natural numbers in real formulas are cast to the reals before subtraction "
                    + "or division. In the four-direction formulas, i is the complex imaginary "
                    + "unit and k is coerced from Fin(4) to a natural exponent. The anchors are "
                    + "exactly a(j), i a(j), -a(j), -i a(j). The norm and phase calibration are "
                    + "exact. Only their squared-distance comparisons carry the common additive "
                    + "error delta, uniformly for every unit input and every literal anchor.")),
                Item("finite_oriented_anchor_polar_repair", "Uniform finite-anchor polar repair", telescope),
                Paragraph(Text(
                    "This is V80 Theorem 14.1 with the standing complete-output definitions "
                    + "2.1 through 3.2 and section 14. IsStrictlyPositive means that the positive "
                    + "Gram operator is invertible; in finite dimension it is positive definite. "
                    + "positiveSqrt is Mathlib CFC.sqrt and ringInverse is its two-sided inverse, "
                    + "so the displayed U is precisely B(B*B)^(-1/2), with the same adjoint "
                    + "and phase conventions. No relation between the dimensions of H and W "
                    + "is assumed in advance. Delta zero and d one remain included.")),
                Paragraph(Text(
                    "The proof reconstructs real and imaginary coordinates from the opposite "
                    + "anchors and uses Parseval to obtain norm(B*F(x)-x) <= eta. At basis "
                    + "inputs the Gram diagonal is one and the off-diagonal modulus is at most "
                    + "delta/sqrt(2). Mathlib Gershgorin and continuous functional calculus put "
                    + "the spectrum in [1-kappa,1+kappa], prove positivity, and bound the "
                    + "positive square root. CFC.inverse_rpow identifies its inverse with the "
                    + "negative half power, and CFC.conjugate_rpow_neg_one_half proves the "
                    + "polar isometry normalization. "
                    + "The norm-square expansion gives norm(F(x)-B(x)) squared <= kappa+2 eta; "
                    + "the triangle inequality and the distance bound two give the literal minimum. "
                    + "Standard spectral, inverse-square-root, Parseval and scalar-root machinery "
                    + "is reused from pinned Mathlib. The new bridge relates actual nonlinear "
                    + "finite comparisons to the uniform repair; it does not assume any of the "
                    + "coordinate, Gram or polar conclusions.")),
                Paragraph(Text(
                    "This proves existence of a nearby mathematical representation on the same "
                    + "complete output. It supplies no physical implementation or internal control "
                    + "claim. It makes no sampled-input, arbitrary-amplitude approximate comparison, "
                    + "outcome-projection or sharpness claim.")))));
    }

    private static DocumentBlock Item(string name, string title, Formula formula, bool definition = false) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(definition
                ? "This definition is used by the complete repair theorem."
                : "All the displayed original premises are retained; the conclusion holds for every unit input."))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Exists(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. vars], body);
    private static Formula Eqn(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Lt(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThan, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Implies(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula Sub(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Subtract, r);
    private static Formula Add(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Add, r);
    private static Formula Mul(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Multiply, r);
    private static Formula Div(Formula l, Formula r) => new Formula.Fraction(l, r);
}
