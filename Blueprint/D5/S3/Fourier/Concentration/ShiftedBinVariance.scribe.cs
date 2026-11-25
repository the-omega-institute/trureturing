using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class ShiftedBinVarianceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/ShiftedBinVariance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A shared shift and a quadratic lattice test give a variance lower bound for near-collision mass.",
        H("Common shifted bins and a parabolic test"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-shifted-squared-moment"),
                DeclarationHandle.Create(Owner + ".exists_shifted_squared_moment"),
                H("A common shift with controlled squared moment"),
                StatementSource.FromAuthor(Rounding()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite index set S, let z and c have arbitrary real values. Write "
                        + "B(u) = Σ c(i)⌊z(i)+u⌋², Q = Σ c(i)z(i)² and "
                        + "R = Σ c(i){z(i)}(1−{z(i)}), with all sums over S and braces denoting fractional part.")),
                    Paragraph(Text(
                        "For a single real z the shifted floor equals floor(z) on a subinterval "
                        + "of length 1−{z} and floor(z)+1 on the complementary subinterval. "
                        + "Integrating its square gives z²+{z}(1−{z}). The weighted integral is "
                        + "Q+R even for signed weights. Strict exceedance for every common shift "
                        + "in the half-open unit interval would contradict this integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("collision-parabolic-lower"),
                DeclarationHandle.Create(Owner + ".collision_parabolic_lower"),
                H("Variance lower bound from the clipped parabola"),
                StatementSource.FromAuthor(Parabolic()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be finite, x and c real-valued, a and V real, and η positive. "
                        + "Write W = Σ c(i), D = Σ c(i)(x(i)−a)², M = V/η²+1/4, "
                        + "and E = nearCollisionMass S x c η, including ordered pairs at distance η. "
                        + "All sums defining W and D are over S. The radius r is a positive natural number.")),
                    Paragraph(Text(
                        "The common shift applied to z(i) = (x(i)−a)/η gives integer bins "
                        + "b(i) with weighted second moment at most MW, since each rounding penalty "
                        + "is at most 1/4. Same-bin pairs have distance less than η. For "
                        + "q(k) = max(0,1−k²/r²), the weighted sum of q over those bins is "
                        + "at least W(1−M/r²). The square and fourth moment sums over the integer "
                        + "interval [−r,r] give Σ q(k)² = 16r/15−1/(15r³). "
                        + "Cauchy–Schwarz and the squared bin-mass lower bound from "),
                        Ref("D5/S3/Fourier/Concentration/FiniteSincCollisionMoment.sum_bin_mass_sq_le_nearCollisionMass"),
                        Text(" establish the assertion.")),
                    Paragraph(Text(
                        "For degree-p frequency sums of nonnegative weights with positive total "
                        + "weight W₀ and centered variance V₀, the moment computation in "),
                        Ref("D5/S3/Fourier/Concentration/FiniteCollisionVariance.tailCollisionMass_lower_variance"),
                        Text(" gives total weight W₀ᵖ and centered variance pV₀. "
                        + "Substitute these values for W and V. The inequality gives a necessary "
                        + "collision budget at finite resolution. An arithmetic upper bound for "
                        + "actual zeta ordinates is an independent open step."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Rounding()
    {
        var u = F.Id("u");
        return Disp(Seq(Exists, Sp, u, InMacro, Sp, OpenBracket, D(0), Comma,
            D(1), Close, Quad, Call("B", u), Leq, Add(F.Id("Q"), F.Id("R"))));
    }

    private static Formula Parabolic()
    {
        var r = F.Id("r");
        var w = F.Id("W");
        var m = F.Id("M");
        var eta = F.Id("eta");
        var rsq = new Formula.Power(r, D(2));
        var assumptions = Seq(Forall, Sp, F.Id("i"), InMacro, Sp, F.Id("S"), Comma, Sp,
            D(0), Leq, Call("c", F.Id("i")), Quad, D(0), Lt, eta, Comma, Sp,
            F.Id("D"), Leq, Multiply(F.Id("V"), w), Comma, Sp,
            D(0), Lt, r, Comma, Sp, m, Leq, rsq);
        var lhs = Multiply(new Formula.Power(w, D(2)),
            new Formula.Power(Seq(Open, Subtract(D(1), new Formula.Fraction(m, rsq)), Close), D(2)));
        var factor = Subtract(new Formula.Fraction(Multiply(D(1, 6), r), D(1, 5)),
            new Formula.Fraction(D(1), Multiply(D(1, 5), new Formula.Power(r, D(3)))));
        var rhs = Multiply(Seq(Open, factor, Close), F.Id("E"));
        return Disp(new Formula.Logic(assumptions, FormulaLogicOperator.Implies,
            new Formula.Relation(lhs, FormulaRelationOperator.LessThanOrEqual, rhs)));
    }
}
