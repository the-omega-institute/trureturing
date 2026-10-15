using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeSugawaraLocalNilpotenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence.";

    private static DocumentBlock.Describe Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("sugawara-local-nilpotence-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Sugawara one-mode lowers native oscillator degree and is locally nilpotent on every finite-support state.",
        H("Unrestricted Actual Sugawara Local Nilpotence"),
        Blocks(
            Paragraph(Text("D is the original integral symmetric even-diagonal lattice data, including rank zero and degenerate Gram matrices. "
                + "H is any complex matrix, without an inverse, positivity or signature assumption. Carrier(D) is the original finite charge sum of multivariate polynomials. "
                + "The nonnegative oscillator degree of a monomial d is sum_x (x.2+1)*d(x); charge energy is not included in this bound.")),
            Paragraph(Text("The original weighted Euler derivation and its actual Sugawara commutator are used directly. "
                + "The supplier oscillatorEuler_monomial supplies the actual basis eigenvalue, and eulerMode_single gives its action in the original charge carrier. "
                + "Coefficient separation compares the nonnegative output oscillator degree with the signed difference N-j, never truncated natural subtraction. "
                + "No lower bound on total L0 energy or finite arbitrary-signature energy fiber is asserted.")),
            Entry("oscillatorBound", "Finite native oscillator bound",
                "N(v) is the finite supremum of oscillatorEnergy(d) over the nonzero original charge/monomial coefficients of v. It is zero for the zero state and every degree-zero charged ground state.", DescribeRole.Definition),
            Entry("one_pow_basis_euler", "Signed degree of every actual power",
                "For every natural j and every actual basis label a=(beta,d), E(L1^j a)=(oscillatorEnergy(d)-j)L1^j a, with the difference formed in Complex. The charge contribution is absent from E.", DescribeRole.Theorem),
            Entry("one_pow_basis_eq_zero", "Coefficient separation annihilates excessive powers",
                "If j>oscillatorEnergy(d), every actual coefficient of L1^j a vanishes: its nonnegative output degree cannot equal the negative integer oscillatorEnergy(d)-j. This applies to all charges and arbitrary H.", DescribeRole.Theorem),
            Entry("one_pow_eq_zero", "Every finite-support state is locally nilpotent",
                "For every actual state v and every natural j>N(v), the actual operator (sugawaraMode(D,H,1))^j sends v to zero. The native finite monomial expansion extends the basis argument to mixed degrees and mixed charges.", DescribeRole.Theorem))));
}
