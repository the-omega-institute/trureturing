using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class LaplaceEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero-safe convergent resolvent and Laplace integrals for finite entropy differences.",
        H("Entropy differences as resolvent integrals"), Blocks(
            Paragraph(Text("Let I be finite and let p_i and x_i be nonnegative real numbers. Put a=Σ_i p_i x_i. No normalization of the weights is required for this identity. With normalized weights, its right side is the Jensen difference for u log u. The integral is a single absolutely integrable difference; its separate resolvent terms need not be integrable.")),
            Describe.Lean(DescribeId.Create("subentropy-entropy-jensen-resolvent"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/LaplaceEntropy.entropy_jensen_resolvent"),
                H("The finite entropy resolvent identity"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0 and x_i>0, integrate x_i(1/(t+a)−1/(t+x_i)) using UniformIntegrals.reciprocal_difference, with the order of the shifts reversed when necessary. If x_i=0, the entire summand is zero. Finite linearity gives the identity because Σ_i p_i x_i=a. If a=0, nonnegativity forces every p_i x_i=0 and both sides vanish. This proves a scalar resolvent identity; it does not assert a Gaussian representation of matrix subentropy."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("subentropy-entropy-jensen-laplace"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/LaplaceEntropy.entropy_jensen_laplace"),
                H("The finite entropy Laplace identity"),
                StatementSource.FromAuthor(Disp(Statement(true))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here the weights also satisfy Σ_i p_i=1. Put F(s)=Σ_i p_i exp(−s x_i)−exp(−s a). Finite convex-exponential Jensen gives F(s)≥0. The preceding resolvent integrand equals ∫_(s>0) t exp(−ts)F(s) ds. Its known integrability proves integrability of the nonnegative two-variable kernel. Fubini exchanges s and t, and the Gamma integral at order two gives ∫_(t>0)t exp(−ts)dt=1/s². This proves the Laplace identity without excluding zero x_i or imposing an unproved boundary-limit condition."))),
                DescribeRole.Theorem))));

    private static Formula Statement(bool laplace = false)
    {
        Formula t = F.Id("t"), a = F.Id("a"), p = Call("p", F.Id("i")), x = Call("x", F.Id("i"));
        Formula px = Mul(p, x);
        Formula kernel = Sub(new Formula.Fraction(a, Add(t, a)),
            Call("sum", Mul(p, new Formula.Fraction(x, Add(t, x)))));
        if (laplace)
            kernel = new Formula.Fraction(Sub(Call("sum", Mul(p, Call("exp", Mul(Sub(D(0), t), x)))),
                Call("exp", Mul(Sub(D(0), t), a))), new Formula.Power(t, D(2)));
        Formula value = Sub(Call("sum", Mul(px, Call("log", x))), Mul(a, Call("log", a)));
        Formula integral = Seq(Int, Underscore,
            Grp(new Formula.Relation(t, FormulaRelationOperator.GreaterThan, D(0))),
            Sp, kernel, Sp, Mathrm, Grp(F.Id("d")), Sp, t);
        return new Formula.Logic(Call("IntegrableOn", kernel, Call("Ioi", D(0))),
            FormulaLogicOperator.And, new Formula.Relation(integral, FormulaRelationOperator.Equal, value));
    }
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
