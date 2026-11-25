using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class RobinFiniteMeshDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/RobinFiniteMesh.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite mesh approximation of the Robin mass",
        H("Actual endpoint samples and a uniform error bound"),
        Blocks(
            Paragraph(Text("Write M(A,B) for the weighted negative mass of the tail of the "
                + "actual Chebyshev kernel (ψ(t)−t)/t². The mesh x is strictly increasing "
                + "on the natural indices from 0 through N.")),
            Describe.Lean(DescribeId.Create("robin-finite-mesh-chord-mass"),
                DeclarationHandle.Create(Module + "chordMass"), H("Weighted chord mass"),
                StatementSource.FromAuthor(Chord()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For u(t)=t log(t), write Q(a,b,t)=(u(t)−u(a))/(u(b)−u(a)) "
                    + "and H(a,b,t)=(1−Q(a,b,t))R(a)+Q(a,b,t)R(b). The weight is "
                    + "w(t)=(log(t)/(1+log(t)))/(t sqrt(t)). On the meshes below, each signed "
                    + "ramp sample has the finite Mangoldt formula of RobinWeightedRamp.ramp_eq_sum "
                    + "with a cutoff at least the floor of its endpoint."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("robin-finite-mesh-endpoint-error"),
                DeclarationHandle.Create(Module + "abs_mass_sub_mesh_le"), H("Endpoint error bound"),
                StatementSource.FromAuthor(Mesh(false)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On each cell [a,b], monotonicity of ψ puts ψ(t)−t "
                    + "between ψ(a)−b and ψ(b)−a. Sum the centered chord estimates with "
                    + "a common mesh coefficient. Adjacent interval integrals recover M(A,B), "
                    + "and the widths sum to ψ(B)−ψ(A)+B−A."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("robin-finite-mesh-uniform-error"),
                DeclarationHandle.Create(Module + "abs_mass_sub_mesh_le_nine_mul_sq"),
                H("Uniform error at the three-quarter-power mesh scale"),
                StatementSource.FromAuthor(Mesh(true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unconditional Chebyshev bound ψ(B)≤(11/2)B "
                    + "makes the endpoint budget at most 12A. Squaring the step scale "
                    + "cancels A sqrt(A) in the common coefficient. For the empty mesh, "
                    + "both masses vanish."))), DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula At(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Parens(Formula a) => Seq(Open, a, Close);

    private static Formula Given(Formula result, params Formula[] hypotheses)
    {
        for (var i = hypotheses.Length - 1; i >= 0; i--)
            result = new Formula.Logic(hypotheses[i], FormulaLogicOperator.Implies, result);
        return result;
    }

    private static Formula Chord()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var t = F.Id("t");
        var integrand = Multiply(At("w", t), At("max", At("H", a, b, t), D(0)));
        var integral = Seq(Int, Underscore, Grp(a), Caret, Grp(b), Sp, integrand, Sp, F.Id("d"), t);
        return Disp(All("a", Real, All("b", Real, Eq(At("C", a, b), integral))));
    }

    private static Formula Mesh(bool uniform)
    {
        var a = F.Id("A");
        var b = F.Id("B");
        var h = F.Id("h");
        var eta = F.Id("eta");
        var n = F.Id("N");
        var i = F.Id("i");
        var j = F.Id("j");
        var next = At("x", Add(i, D(1)));
        var sample = At("C", At("x", i), next);
        var sum = Seq(Sum, Underscore, Grp(And(Le(D(0), i), Lt(i, n))), Sp, sample);
        var error = new Formula.Absolute(Subtract(At("M", a, b), Parens(sum)));
        var width = Subtract(Add(Subtract(At("psi", b), At("psi", a)), b), a);
        var factor = new Formula.Fraction(Multiply(D(3), Pow(h, D(2))),
            Multiply(Multiply(D(4), Pow(a, D(2))), At("sqrt", a)));
        Formula result = uniform
            ? Given(Le(error, Multiply(D(9), Pow(eta, D(2)))),
                Le(h, Multiply(eta, Pow(a, new Formula.Fraction(D(3), D(4))))))
            : Le(error, Multiply(factor, Parens(width)));
        var strict = All("i", Nat, All("j", Nat,
            Given(Lt(At("x", i), At("x", j)), Le(i, n), Le(j, n), Lt(i, j))));
        var step = All("i", Nat, Given(Le(Subtract(next, At("x", i)), h), Lt(i, n)));
        result = Given(result, Le(At("exp", D(1)), a), Le(b, Multiply(D(2), a)),
            Eq(At("x", D(0)), a), Eq(At("x", n), b), strict, step);
        result = All("N", Nat, All("x", new Formula.TypeArrow(Nat, Real), result));
        if (uniform)
            result = All("eta", Real, result);
        return Disp(All("A", Real, All("B", Real, All("h", Real, result))));
    }
}
