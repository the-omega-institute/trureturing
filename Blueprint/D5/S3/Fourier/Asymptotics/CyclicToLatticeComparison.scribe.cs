using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicToLatticeComparisonDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicToLatticeComparison";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two cosine moments give a uniform comparison with the integer-lattice minimum.",
        H("Quantitative comparison of cyclic and lattice minima"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integral-cosine-moments-at-centered-representatives"),
                DeclarationHandle.Create(Owner + ".cosineMoment_eq_centered"),
                H("Centering the residue representatives"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    new Formula.Relation(
                        Call("M", F.Id("r"), F.Id("v")),
                        FormulaRelationOperator.Equal,
                        Call("CenteredMoment", F.Id("r"), F.Id("v")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive modulus q, natural frequency r and real residue weights v, "
                    + "M(r,v) sums v(i) cos(2πri/q) using least nonnegative representatives i. "
                    + "The centered moment uses the representatives in (−q/2,q/2]. At each residue the two "
                    + "angles differ by an integral multiple of 2π."))),
                DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("cyclic-to-lattice-squared-mass-comparison"),
            DeclarationHandle.Create(Owner + ".cyclic_to_lattice_comparison"),
            H("Energy and distance bounds on the finite cycle"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let n be a positive integer, q a modulus and λ real. Put m=λ/(8π²) and "
                    + "a=1−λ/q², and require (n²−1)/5≤m≤n(n+2)/5. The interval in particular gives λ≥0. "
                    + "Write r=n−1 when m=(n²−1)/5 and r=n otherwise, and assume q>2r. "
                    + "Let w be the integer-lattice minimizer furnished by the activation theorem for "
                    + "this interval, with radius parameter t and normalizer Z. Write L(m) for its squared mass.")),
                Paragraph(Text(
                    "The finite probability weights have full first and second cosine moments at least a. "
                    + "The minimum E_q(a) is attained. For each nonnegative weight v of mass one, "
                    + "E(v) denotes its squared mass, M_1(v) and M_2(v) its two cosine moments, "
                    + "and D_q(v,w) is the sum of squared differences against w at the centered residue representatives. "
                    + "The two signed contributions S_1 and S_2 are (2t/Z)(M_1(v)−a) and "
                    + "((q/(2π))²/Z)(M_2(v)−a). Both are nonnegative for a feasible competitor.")),
                Paragraph(Text(
                    "For a centered residue j, write θ=2πj/q. On the full centered range, "
                    + "θ² cos θ≤sin² θ. The sign suffices when cos θ≤0. Otherwise the half-angle estimate "
                    + "sin(|θ|/2)≥(|θ|/2)cos(θ/2), together with cos⁴(θ/2)≥cos θ, gives the inequality. "
                    + "Consequently (t cos θ−(q sin θ/(2π))²)/Z lies below the lattice weight. "
                    + "Summing against feasible v controls the cross term of the squared-distance identity. "
                    + "The zero site contributes t to Z, giving t/Z≤1.")),
                Paragraph(Text(
                    "For the upper bound the lattice support embeds injectively on the cycle since q>2r. "
                    + "The cosine deficits of the embedded law are bounded by its second moment times "
                    + "2π²/q² and 8π²/q² for the two modes. The inequality 1−cos x≤x²/2 supplies both estimates. "
                    + "The finite feasible set is closed in the unit box, so continuity gives a minimizer."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var q = F.Id("q");
        var a = F.Id("a");
        var m = F.Id("m");
        var t = F.Id("t");
        var z = F.Id("Z");
        var v = F.Id("v");
        var w = F.Id("w");
        var lambda = F.LambdaLower;
        var deficit = new Formula.Fraction(lambda, new Formula.Power(q, F.D(2)));
        var error = Multiply(new Formula.Fraction(Multiply(F.D(2), t), z), deficit);
        var latticeValue = Call("L", m);
        var cyclicMinimum = Call("E", q, a);
        var gap = Subtract(latticeValue, cyclicMinimum);
        var distanceWithSlacks = Add(Add(Call("D", q, v, w), Call("S", F.D(1), v)),
            Call("S", F.D(2), v));
        return F.Disp(new Formula.Aligned([
            F.Seq(F.Amp, F.D(0), F.Sp, F.Le, F.Sp, gap, F.Sp, F.Le, F.Sp,
                error, F.Sp, F.Le, F.Sp, Multiply(F.D(2), deficit), F.Comma),
            F.Seq(F.Amp, distanceWithSlacks, F.Sp, F.Le, F.Sp,
                Add(Subtract(Call("E", v), latticeValue), error), F.Dot)
        ]));
    }
}
