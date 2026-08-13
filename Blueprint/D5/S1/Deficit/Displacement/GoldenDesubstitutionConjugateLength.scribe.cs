using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Displacement;

internal sealed class GoldenDesubstitutionConjugateLengthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden substitution of prime exponents becomes Zeckendorf displacement in the conjugate-face length.",
        H("Golden Desubstitution on Conjugate-Face Length"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-conjugate-length-displacement-sum"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDesubstitutionConjugateLength.lambdaMinus_nS_eq_displacement_sum"),
                H("The substituted conjugate-face length is a displacement sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    LambdaLower, Underscore, Grp(Minus), Open,
                    F.Id("nS"), Sp, F.Id("n"), Close, Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("p")), Sp,
                    F.Id("betaContraction"), Open,
                    F.Id("displacementDecode"), Open, F.Id("vp"), Close, Close,
                    Sp, Cdot, Sp, Log, Sp, F.Id("p")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The hidden product nS and its factorization come from the expansion-face bridge. "
                        + "Expanding lambdaMinus over that factorization applies betaContraction to every "
                        + "goldenSubstStart exponent. The repository's golden substitution boundary theorem "
                        + "then replaces each transformed exponent by displacementDecode, the one-step upward "
                        + "shift of its canonical Zeckendorf digits."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-conjugate-length-increment"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenDesubstitutionConjugateLength.lambdaMinus_nS_sub_lambdaMinus"),
                H("Substitution changes conjugate length by exponentwise displacement increments"),
                StatementSource.FromAuthor(Disp(Seq(
                    LambdaLower, Underscore, Grp(Minus), Open,
                    F.Id("nS"), Sp, F.Id("n"), Close, Sp, Minus, Sp,
                    LambdaLower, Underscore, Grp(Minus), Open, F.Id("n"), Close, Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("p")), Sp, Left, Open,
                    F.Id("betaContraction"), Open,
                    F.Id("displacementDecode"), Open, F.Id("vp"), Close, Close,
                    Sp, Minus, Sp, F.Id("betaContraction"), Open, F.Id("vp"), Close,
                    Right, Close, Sp, Cdot, Sp, Log, Sp, F.Id("p")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Subtracting the original conjugate-face length from the substituted one combines the "
                        + "two finite prime sums term by term. Each summand is the change from betaContraction "
                        + "at the original exponent to betaContraction at its Zeckendorf displacement decode, "
                        + "weighted by the logarithm of the corresponding prime."))),
                DescribeRole.Theorem))));
}
