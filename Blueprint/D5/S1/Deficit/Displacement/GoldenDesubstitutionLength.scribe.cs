using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Displacement;

internal sealed class GoldenDesubstitutionLengthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden substitution of prime exponents becomes Zeckendorf displacement in the expansion-face length.",
        H("Golden Desubstitution on Expansion-Face Length"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-length-displacement-sum"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDesubstitutionLength.lambdaPlus_nS_eq_displacement_sum"),
                H("The substituted expansion-face length is a displacement sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    LambdaLower, Underscore, Grp(Plus), Open,
                    F.Id("nS"), Sp, F.Id("n"), Close, Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("p")), Sp,
                    F.Id("betaReal"), Open,
                    F.Id("displacementDecode"), Open, F.Id("vp"), Close, Close,
                    Sp, Cdot, Sp, Log, Sp, F.Id("p")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The hidden product nS applies goldenSubstStart to every exponent in the prime "
                        + "factorization. Its own factorization therefore has exactly those transformed "
                        + "exponents. Expanding lambdaPlus and using the repository's golden substitution "
                        + "boundary theorem replaces each transformed exponent by displacementDecode, the "
                        + "one-step upward shift of its canonical Zeckendorf digits."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-length-increment"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDesubstitutionLength.lambdaPlus_nS_sub_lambdaPlus"),
                H("Substitution changes length by exponentwise displacement increments"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("n"), Neq, D(0), Sp, Implies, Sp,
                    LambdaLower, Underscore, Grp(Plus), Open,
                    F.Id("nS"), Sp, F.Id("n"), Close, Sp, Minus, Sp,
                    LambdaLower, Underscore, Grp(Plus), Open, F.Id("n"), Close, Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("p")), Sp, Left, Open,
                    F.Id("betaReal"), Open,
                    F.Id("displacementDecode"), Open, F.Id("vp"), Close, Close,
                    Sp, Minus, Sp, F.Id("betaReal"), Open, F.Id("vp"), Close,
                    Right, Close, Sp, Cdot, Sp, Log, Sp, F.Id("p")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonzero n, subtracting the original expansion-face length from the substituted "
                        + "one combines the two finite prime sums term by term. Each summand is the change "
                        + "from betaReal at the original exponent to betaReal at its Zeckendorf displacement "
                        + "decode, weighted by the logarithm of the corresponding prime."))),
                DescribeRole.Theorem))));
}
