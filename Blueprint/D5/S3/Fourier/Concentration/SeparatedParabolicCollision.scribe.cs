using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class SeparatedParabolicCollisionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/SeparatedParabolicCollision";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite separated parabolic weights attain the asymptotic collision variance coefficient.",
        H("Separated parabolic collision constructions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("separated-parabolic-collision"),
                DeclarationHandle.Create(Owner + ".separated_parabolic_collision"),
                H("Exact finite mass, second moment and collision mass"),
                StatementSource.FromAuthor(Finite()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a positive natural number n let S be the integer interval [−n,n]. "
                        + "The sites are x(k)=k and their weights are c(k)=n²−k². "
                        + "Write W=n(4n²−1)/3, A=Σ c(k), B=Σ c(k)k², with sums over S, "
                        + "and E=nearCollisionMass S x c η for arbitrary real resolution η.")),
                    Paragraph(Text(
                        "The exact mass follows from "),
                        Ref("D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation.normalizer_formula"),
                        Text(". The second moment follows from "),
                        Ref("D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation.lower_moment_difference"),
                        Text(". The separation criterion "),
                        Ref("D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.int_near_eq"),
                        Text(" ensures distinct integer sites differ by "
                            + "at least one, so the closed band at 0≤η<1 contains only the diagonal. "
                            + "Use c(k)²=n²c(k)−k²c(k) to evaluate the collision sum from the same moments.")),
                    Paragraph(Text(
                        "At n=1 the center is the only positive weight, with zero second moment, and the formula holds for all nonnegative resolutions. "
                        + "At n≥2 and η≥1, the ordered pair (0,1) has strictly positive weight. The diagonal is still counted, so collision mass strictly exceeds the formula. Negative resolutions have zero collision mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parabolic-collision-ratio-limit"),
                DeclarationHandle.Create(Owner + ".parabolic_collision_ratio_limit"),
                H("Attainment in the small relative resolution limit"),
                StatementSource.FromAuthor(Limits()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At each natural index n let V(n)=(n²−1)/5, "
                        + "W(n)=n(4n²−1)/3, and E(n) the preceding construction’s collision mass "
                        + "at η(n). Assume η(n)→L>0 and eventually 0<η(n)<1. Write T(n)=η(n)/√V(n) "
                        + "and C(n)=E(n)√V(n)/(W(n)²η(n)).")),
                    Paragraph(Text(
                        "Put t=1/n. The first ratio becomes √5 t η(n)/√(1−t²) "
                        + "and the second is (3/(5√5)) ((4+t²)/(4−t²))√(1−t²)/η(n). "
                        + "The finite identities apply eventually and the limiting denominators are nonzero. "
                        + "Continuity and t→0 prove both limits. Taking η(n)=n/(n+1) gives L=1 and attains the coefficient 3/(5√5).")),
                    Paragraph(Text(
                        "The construction provides admissible finite witnesses for the limiting coefficient "
                        + "of the universal shifted-bin variance bound. It concerns arbitrary finite weighted "
                        + "data. Attainment subject to a fixed frequency-sum structure or to actual zeta "
                        + "ordinates requires additional arithmetic information."))),
                DescribeRole.Theorem))));

    private static Formula Finite()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var eta = F.Id("eta");
        var w = F.Id("W");
        var n2 = new Formula.Power(n, D(2));
        var assumptions = Seq(D(0), Lt, Sp, n);
        var conclusion = Seq(
            Forall, Sp, k, InMacro, Sp, F.Id("S"), Comma, Sp, D(0), Leq, Sp, Call("c", k),
            Quad, D(0), Lt, Sp, w, Comma, Sp,
            Equal(F.Id("A"), w), Comma, Sp,
            Equal(F.Id("B"), new Formula.Fraction(Multiply(w, Seq(Open, Subtract(n2, D(1)), Close)), D(5))),
            Comma, Sp, Open, new Formula.Logic(Equal(F.Id("E"), new Formula.Fraction(
                Multiply(w, Seq(Open, Add(Multiply(D(4), n2), D(1)), Close)), D(5))),
                FormulaLogicOperator.Iff, Seq(D(0), Leq, Sp, eta, Comma, Sp, Open, Equal(n, D(1)), Sp, Lor, Sp, eta, Lt, D(1), Close)), Close);
        return Disp(new Formula.Logic(assumptions, FormulaLogicOperator.Implies, conclusion));
    }

    private static Formula Limits()
    {
        var n = F.Id("n");
        var l = F.Id("L");
        var e = Call("eta", n);
        var assumptions = Seq(D(0), Lt, Sp, l, Comma, Sp,
            Call("Eventually", Seq(D(0), Lt, e, Lt, D(1))), Comma, Sp,
            Call("TendstoAtTop", e, l));
        var limits = Seq(Call("TendstoAtTop", Call("T", n), D(0)), Comma, Sp,
            Call("TendstoAtTop", Call("C", n),
                new Formula.Fraction(D(3), Multiply(Multiply(D(5), Call("sqrt", D(5))), l))));
        return Disp(new Formula.Logic(assumptions, FormulaLogicOperator.Implies, limits));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
