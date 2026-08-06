using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class FinitePoissonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Fourier/FinitePoisson",
            "Finite Poisson summation on an arbitrary additive subgroup of a positive cyclic group."),
        H("Finite Poisson Summation"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("finite-poisson-summation-on-a-cyclic-subgroup"),
                H("Finite Poisson summation on a cyclic subgroup"),
                LeanTheorem("D5/S3/Fourier/FinitePoisson.finite_poisson_summation"),
                StatementProjectionFixtureLoader.FromLean(LeanTheorem("D5/S3/Fourier/FinitePoisson.finite_poisson_summation")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The annihilator is defined explicitly by triviality of the standard character on H. Its identification with the complete character group of the quotient supplies both character orthogonality and the cardinal identity |H||H-perp| = m. Expanding the pinned ZMod discrete Fourier transform and exchanging the two finite sums then yields the stated normalization without assuming either identity.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-even-subgroup-has-an-explicit-poisson-witness"),
                H("The even subgroup has an explicit Poisson witness"),
                LeanTheorem("D5/S3/Fourier/FinitePoisson.finite_poisson_mod_four_even_delta"),
                Disp(Seq(F.Id("H"), Eq, OpenBrace, D(0), Comma, D(2), CloseBrace, Comma, Quad, Sp, F.Id("f"), Open, F.Id("x"), Close, Eq, Mathbf, Grp(D(1)), Underscore, Grp(F.Id("x"), Eq, D(0)), Nl, Quad, Rightarrow, Quad, Nl, Sum, Underscore, Grp(F.Id("h"), InMacro, Sp, F.Id("H")), F.Id("f"), Open, F.Id("h"), Close, Eq, D(1), Eq, Frac, Grp(Bar, F.Id("H"), Bar), Grp(D(4)), Sum, Underscore, Grp(F.Id("k"), InMacro, Sp, F.Id("H"), Caret, Perp), Widehat, Sp, F.Id("f"), Open, F.Id("k"), Close, Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Kernel-reduced membership checks prove that 2 belongs to H while 1 does not. The branch witnesses then prove 2 belongs to the annihilator and 1 does not; character orthogonality evaluates to 2 at x = 2 and to 0 at x = 1. For the delta function at zero, both sides of Poisson summation reduce to the explicit value 1.")))
            ))));
}
