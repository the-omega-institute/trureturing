using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class OddPrimeJetRadicalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetRadical.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The leading-zero ideal of the actual odd-prime jet commutant.",
        H("The radical and principal units"), Blocks(
            Paragraph(Text("Let p be any odd prime, K any field in an arbitrary universe with its given algebra structure over F=ZMod p, and q:K→K any F-linear map satisfying q(1)=0. All operators act on the original polynomial space of degree less than p. The commutant algebra consists of the actual F-linear operators commuting with every original representation operator. Restriction to constants gives a ring homomorphism to K; its kernel J is the leading-zero ideal. No finiteness hypothesis is needed for these structural statements.")),
            Describe.Lean(DescribeId.Create("odd-prime-jet-radical-commute"),
                DeclarationHandle.Create(Prefix + "radical_commute"), H("Commutativity of the ideal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any two members of J commute under actual operator composition. In the unique divided-degree coordinates the leading scalar is zero. The scalar convolution and the scalar contribution to the top map are symmetric, and both ordered top-scalar terms vanish. The highest coefficient remains an unrestricted F-linear endomorphism of K."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-prime-jet-radical-element-pow"),
                DeclarationHandle.Create(Prefix + "radical_element_pow"), H("Elementwise nilpotence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For X in J, X^p=0. This directly uses the derivative-filtration theorem for operators commuting with differentiation and annihilating constants from the commutant normal-form source."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-prime-jet-radical-joint-pow"),
                DeclarationHandle.Create(Prefix + "radical_pow_eq_bot"), H("Joint ideal-power nilpotence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The entire ideal power J^p is zero. For each r, every element of J^r annihilates the kernel of D^r. To advance this assertion, write a generator of J^(r+1) as XY with X in J and Y in J^r. If D^(r+1)v=0, then D(Yv)=Y(Dv)=0, so Yv is constant and X annihilates it. Ideal closure extends the assertion to sums. Finally D^p=0 on the original polynomial carrier."))), DescribeRole.Theorem))));
}
