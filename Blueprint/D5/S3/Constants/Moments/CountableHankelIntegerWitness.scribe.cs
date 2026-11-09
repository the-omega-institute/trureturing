using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class CountableHankelIntegerWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete spectral integer witnesses",
        H("Complete spectral integer witnesses"),
        Blocks(Describe.Lean(
                DescribeId.Create("exists-integer-negative"),
                DeclarationHandle.Create("D5/S3/Constants/Moments/CountableHankelIntegerWitness.exists_integer_negative"),
                H("Finite integer direction for the complete weighted spectrum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every index type iota, complex maps z and w, permutation c, unit-disk node bound, injectivity of z, conjugation compatibility of nodes and weights, summability of all absolute weights, and finite node superlevel cuts for every positive radius, and for every index i0 with a nonreal node and nonzero weight, there exist a natural N and integer vector u on Fin(N+1) such that the real part of the complete sum of w(i) times [the sum over a in Fin(N+1) of u(a) z(i) to power a] squared is strictly negative.")),
                    Paragraph(Text("The real polynomial from complete head isolation is expressed by its coefficients through its natural degree. Each complete moment sum is absolutely convergent. Finite expansion and HasSum identify its form with the finite real quadratic form whose matrix entry at a,b is the real part of the full moment of order a+b. Rational density and exact denominator scaling are applied to this same matrix. The complete spectral family and all weights are fixed throughout. No polynomial degree bound, effective coefficient search, or unconditional positivity is claimed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quadratic-identity"),
                DeclarationHandle.Create("D5/S3/Constants/Moments/CountableHankelIntegerWitness.quadratic_identity"),
                H("The finite coefficient form equals the complete ordinary-square sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every index type iota, complex maps z,w with norm(z(i)) at most one and summable norm(w(i)), natural N and real coefficient vector u on Fin(N+1), the real part of the complete sum_i w(i) (sum_a u(a) z(i) to power a) squared equals sum_ab u(a) u(b) Re(sum_i w(i) z(i) to power (a+b)). This consumed identity needs neither injectivity nor conjugation nor a finite head. Absolute moment summability and the finite HasSum expansion identify the two forms."))),
                DescribeRole.Theorem))));
}
