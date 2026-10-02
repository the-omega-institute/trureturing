using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ShortCofactorCharacterEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Short positive intervals have a logarithmic multiplicative energy bound.",
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
                        + "estimate is the standard bound by 1+log(N); "
                        + "no originality claim is made."))),
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
                DescribeRole.Theorem))));

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
            Seq(D(0), Sp, Lt, Sp, v, Comma, Sp, D(1), Sp, Le, Sp, h,
                Comma, Sp, new Formula.Power(h, D(2)), Sp, Le, Sp, v, Sp, Rightarrow),
            Seq(m4, Sp, Le, Sp, D(2), Sp, new Formula.Power(h, D(2)), Sp,
                Open, logarithm, Close, Comma),
            Seq(D(2), Sp, k, Sp, Le, Sp, q, Sp, Rightarrow, Sp,
                new Formula.Fraction(new Formula.Power(k, new Formula.Fraction(D(3), D(2))),
                    denominator), Sp, Le, Sp, m1)
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
