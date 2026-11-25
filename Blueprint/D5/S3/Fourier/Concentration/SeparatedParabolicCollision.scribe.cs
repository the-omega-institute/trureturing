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
                        + "and E=nearCollisionMass S x c η for real resolution η in [0,1).")),
                    Paragraph(Text(
                        "Exact lattice normalization and the lower endpoint moment identity in "),
                        Ref("D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation.exists_lattice_square_moment_minimizer_on_interval"),
                        Text(" give the mass and second moment. Distinct integer sites differ by "
                            + "at least one, so the closed band at resolution η contains only the diagonal. "
                            + "Use c(k)²=n²c(k)−k²c(k) to evaluate the collision sum from the same moments.")),
                    Paragraph(Text(
                        "At n=1 the center is the only positive weight, with zero second moment. "
                        + "For n≥2 the variance about zero is positive. The closed radius η=1 "
                        + "can admit adjacent positive-weight pairs, so the strict bound on η is material."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parabolic-collision-ratio-limit"),
                DeclarationHandle.Create(Owner + ".parabolic_collision_ratio_limit"),
                H("Attainment in the small relative resolution limit"),
                StatementSource.FromAuthor(Limits()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At each natural index n let V(n)=(n²−1)/5, η(n)=n/(n+1), "
                        + "W(n)=n(4n²−1)/3, and E(n) the preceding construction's collision mass "
                        + "at η(n). The data are admissible for every n≥2. Write T(n)=η(n)/√V(n) "
                        + "and C(n)=E(n)√V(n)/(W(n)²η(n)).")),
                    Paragraph(Text(
                        "Put t=1/n. The first ratio becomes √5 t/((1+t)√(1−t²)) "
                        + "and the second is (3/(5√5)) ((4+t²)/(4−t²))√(1−t²)(1+t). "
                        + "The finite identities apply for n≥2 and every denominator used in the limit "
                        + "is nonzero at t=0. Continuity and t→0 prove both limits.")),
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
        var assumptions = Seq(D(0), Lt, Sp, n, Comma, Sp, D(0), Leq, Sp, eta, Lt, D(1));
        var conclusion = Seq(
            Forall, Sp, k, InMacro, Sp, F.Id("S"), Comma, Sp, D(0), Leq, Sp, Call("c", k),
            Quad, D(0), Lt, Sp, w, Comma, Sp,
            Equal(F.Id("A"), w), Comma, Sp,
            Equal(F.Id("B"), new Formula.Fraction(Multiply(w, Seq(Open, Subtract(n2, D(1)), Close)), D(5))),
            Comma, Sp, Equal(F.Id("E"), new Formula.Fraction(
                Multiply(w, Seq(Open, Add(Multiply(D(4), n2), D(1)), Close)), D(5))));
        return Disp(new Formula.Logic(assumptions, FormulaLogicOperator.Implies, conclusion));
    }

    private static Formula Limits() => Disp(Seq(
        Call("TendstoAtTop", Call("T", F.Id("n")), D(0)), Comma, Sp,
        Call("TendstoAtTop", Call("C", F.Id("n")),
            new Formula.Fraction(D(3), Multiply(D(5), Call("sqrt", D(5)))))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
