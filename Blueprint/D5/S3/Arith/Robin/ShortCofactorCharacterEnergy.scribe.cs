using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ShortCofactorCharacterEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Short cofactor character sums have fourth moment upper and first moment lower bounds.",
        H("Short Cofactor Character Energy"),
        Blocks(
            Paragraph(Text("For a real cutoff H, I(H) consists of the positive natural "
                + "numbers strictly below H. The multiplicative energy E(I) counts "
                + "ordered quadruples (a,c,b,d) in I to the fourth power with ab=cd.")),
            Describe.Lean(
                DescribeId.Create("short-interval-multiplicative-energy"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ShortCofactorCharacterEnergy.short_interval_energy"),
                H("Logarithmic energy bound"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The cutoff is any real number at least one. "
                        + "There is no primality or coprimality restriction.")),
                    Paragraph(Text("Write a=gu and c=gv with g=gcd(a,c). The equality "
                        + "ab=cd and coprimality of u,v imply b=jv and d=ju. "
                        + "For m=max(u,v), the two orientations and the smaller "
                        + "coordinate give at most 2m choices; both g and j are "
                        + "at most N/m for the integral interval from 1 to N. "
                        + "Summing the resulting bounds gives 2N squared times "
                        + "the N-th harmonic number.")),
                    Paragraph(Text("This is the classical gcd parametrization for "
                        + "the multiplicative energy of an interval. The harmonic "
                        + "estimate is the standard bound by 1+log(N)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("short-cofactor-character-moments"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ShortCofactorCharacterEnergy.character_bounds"),
                H("Character moments for any modulus"),
                StatementSource.FromAuthor(CharacterStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("V is a positive modulus, S is the subset of I(H) "
                        + "coprime to V, k is its size, and Q is phi(V). "
                        + "B is the sum of a character on S. M_p is the sum of "
                        + "the p-th powers of the absolute values of B over all "
                        + "nonprincipal characters, divided by Q.")),
                    Paragraph(Text("Character orthogonality identifies the full fourth "
                        + "moment with integer multiplicative energy when H squared "
                        + "is at most V. Removing the principal character decreases "
                        + "this moment. The second moment after removal is k-k squared "
                        + "over Q. Two applications of Cauchy-Schwarz give "
                        + "M_2 cubed <= M_1 squared times M_4, yielding the "
                        + "first moment estimate when 2k <= Q.")),
                    Paragraph(Text("For the classical relation between multiplicative "
                        + "collisions and character moments, see Ayyad, Cochrane and "
                        + "Zheng, Journal of Number Theory 59, 398-413, "
                        + "doi:10.1006/jnth.1996.0105."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-short-cofactor-character-energy"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ShortCofactorCharacterEnergy.result"),
                H("Fibonacci cutoffs"),
                StatementSource.FromAuthor(FibonacciStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let V=F_r, g=ceil(V/10), A=1+Vg, y=log(A), "
                        + "ell=log(y), and H=exp(a*y/ell squared). For every "
                        + "positive real a, all sufficiently large prime indices r "
                        + "satisfy the three displayed bounds with these same parameters.")),
                    Paragraph(Text("Euler's product formula gives n <= 2*phi(n) squared "
                        + "for every positive integer n: p <= (p-1) squared for primes "
                        + "p other than two, and two contributes the factor 2. "
                        + "An explicit threshold ensures 8*H squared < V. "
                        + "The cardinality of the short unit set is at most H, "
                        + "so 2k <= phi(V) and the general character estimates apply.")),
                    Paragraph(Text("The logarithmic cutoff is smaller than V because "
                        + "A <= V squared and ell squared eventually exceeds 8a. "
                        + "The growth bound r <= F_r for r >= 5 transfers the "
                        + "explicit threshold to Fibonacci indices."))),
                DescribeRole.Theorem))));

    private static Formula FibonacciStatement()
    {
        Formula a = F.Id("a");
        Formula r = F.Id("r");
        Formula r0 = Seq(F.Id("r"), Underscore, Grp(D(0)));
        Formula h = F.Id("H");
        Formula k = F.Id("k");
        Formula m1 = Seq(F.Id("M"), Underscore, Grp(D(1)));
        Formula m4 = Seq(F.Id("M"), Underscore, Grp(D(4)));
        Formula logarithm = Seq(D(1), Plus, new Formula.Apply(Log, [h]));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, a, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                a, Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp,
                Exists, Sp, r0, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma),
            Seq(Forall, Sp, r, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                Open, r, Sp, Ge, Sp, r0, Sp, Land, Sp,
                new Formula.Apply(F.Id("Prime"), [r]), Close, Sp, Rightarrow),
            Seq(new Formula.Power(h, D(2)), Sp, Lt, Sp, F.Id("V"), Sp, Land, Sp,
                m4, Sp, Le, Sp, D(2), Sp, new Formula.Power(h, D(2)),
                Open, logarithm, Close, Sp, Land),
            Seq(new Formula.Fraction(new Formula.Power(k, new Formula.Fraction(D(3), D(2))),
                Seq(D(4), Sp, h, Sp, Sqrt, Grp(logarithm))), Sp, Le, Sp, m1)
        ]));
    }

    private static Formula CharacterStatement()
    {
        Formula v = F.Id("V");
        Formula h = F.Id("H");
        Formula k = F.Id("k");
        Formula q = F.Id("Q");
        Formula m1 = Seq(F.Id("M"), Underscore, Grp(D(1)));
        Formula m4 = Seq(F.Id("M"), Underscore, Grp(D(4)));
        Formula logarithm = Seq(D(1), Plus, new Formula.Apply(Log, [h]));
        Formula denominator = Seq(D(4), Sp, h, Sp, Sqrt, Grp(logarithm));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, v, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                Forall, Sp, h, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma),
            Seq(D(0), Sp, Lt, Sp, v, Comma, Sp, D(1), Sp, Le, Sp, h,
                Comma, Sp, new Formula.Power(h, D(2)), Sp, Le, Sp, v, Sp, Rightarrow),
            Seq(m4, Sp, Le, Sp, D(2), Sp, new Formula.Power(h, D(2)), Sp,
                Open, logarithm, Close, Sp, Land),
            Seq(Open, D(2), Sp, k, Sp, Le, Sp, q, Sp, Rightarrow, Sp,
                new Formula.Fraction(new Formula.Power(k, new Formula.Fraction(D(3), D(2))),
                    denominator), Sp, Le, Sp, m1, Close)
        ]));
    }

    private static Formula Statement()
    {
        Formula h = F.Id("H");
        Formula interval = new Formula.Apply(F.Id("I"), [h]);
        Formula energy = new Formula.Apply(F.Id("E"), [interval]);
        return Disp(Seq(Forall, Sp, h, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")),
            Comma, Sp, D(1), Sp, Le, Sp, h, Sp, Rightarrow, Sp,
            energy, Sp, Le, Sp, D(2), Sp, new Formula.Power(h, D(2)), Sp,
            Open, D(1), Plus, new Formula.Apply(Log, [h]), Close));
    }
}
