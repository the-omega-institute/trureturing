using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class FiniteSpectralPerturbationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/FiniteSpectralPerturbation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Small finite perturbations can bound weighted near-collisions at positive resolution.",
        H("Weighted Near-Collisions under Finite Spectral Perturbations"),
        Blocks(
            Paragraph(Text(
                "Let J be a finite type with decidable equality. The real functions g and w give "
                + "frequencies and weights with total W. For degree p, the multinomial coefficient "
                + "including weights is c(m), and D is the sum of c(m)² over degree-p vectors m. "
                + "The quantity E(g',p,η) sums c(m)c(n) over ordered pairs whose g' frequency sums "
                + "are at distance at most η. The positive perturbation radius is ε.")),
            Describe.Lean(
                DescribeId.Create("exists-nearby-collision-bound"),
                DeclarationHandle.Create(Owner + ".exists_nearby_collision_bound"),
                H("One perturbation with a controlled off-diagonal mass"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Choose each offset from M+2 equally spaced points in [−ε, ε]. For two "
                        + "distinct degree-p vectors, one coordinate of their difference is a "
                        + "nonzero integer. Fix all offsets except that coordinate. The difference "
                        + "of the perturbed frequency sums is affine with slope magnitude at least "
                        + "2ε/(M+1) in the remaining grid index.")),
                    Paragraph(Text(
                        "The least and greatest admissible indices differ by at most 2η divided by "
                        + "the slope magnitude. The fiber has at most 1+η(M+1)/ε points including "
                        + "both endpoints. Averaging each indicator over the finite product gives "
                        + "the displayed factor. Diagonal pairs contribute D at every assignment. "
                        + "Since the total coefficient weight is Wᵖ, the other pairs have total "
                        + "weight W²ᵖ−D. A single assignment is at most the upper bound on the mean.")),
                    Paragraph(Text(
                        "The weighted mass is the same one used in "),
                        Ref("D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.tail_moment_comparison"),
                        Text(". The perturbations are chosen for one finite spectrum, one degree "
                            + "and one resolution. Applying a bound to the fixed actual zeta ordinates "
                            + "requires an arithmetic estimate for those ordinates."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Bound()
    {
        var j = F.Id("j");
        var index = F.Id("J");
        var m = F.Id("M");
        var p = F.Id("p");
        var eta = F.Id("eta");
        var radius = Varepsilon;
        var w = F.Id("W");
        var diagonal = F.Id("D");
        var gPrime = F.Id("h");
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var nats = Seq(Mathbb, Grp(F.Id("N")));
        var weightCondition = Bind(FormulaQuantifier.ForAll, "j", index, AtMost(D(0), Call("w", j)));
        var proximity = Bind(FormulaQuantifier.ForAll, "j", index,
            AtMost(new Formula.Absolute(Seq(Call("h", j), Minus, Call("g", j))), radius));
        var factor = new Formula.Fraction(
            Add(D(1), new Formula.Fraction(Multiply(eta, Seq(Open, Add(m, D(1)), Close)), radius)),
            Add(m, D(2)));
        var offDiagonal = Seq(Open, new Formula.Power(w, Multiply(D(2), p)), Minus, diagonal, Close);
        var bound = AtMost(Call("E", gPrime, p, eta), Add(diagonal, Multiply(factor, offDiagonal)));
        var law = Bind(FormulaQuantifier.Exists, "h", Seq(index, Sp, To, Sp, reals),
            new Formula.Logic(proximity, FormulaLogicOperator.And, bound));
        var assumptions = Seq(Open, weightCondition, Close, Quad, Sp,
            p, InMacro, Sp, nats, Comma, Sp, m, InMacro, Sp, nats, Comma, Sp, D(0), Lt, radius,
            Comma, Sp, D(0), Leq, Sp, eta);
        return Disp(new Formula.Logic(assumptions, FormulaLogicOperator.Implies, law));
    }
}
