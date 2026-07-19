using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class ZeroOrbitCongruenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Phase/ZeroOrbitCongruence",
                "Separate the finite congruence premise from the global norm exclusion in the 36-divisibility step."),
            H("Zero-Orbit Congruence"),
            Blocks(
                Paragraph(
                    Text("This module records the exact finite-ring part of a local-to-global divisibility argument. The local candidate disjunction modulo 36 remains an explicit premise; no residue enumeration is inferred from the two theorems below.")),
                new DocumentBlock.Describe(
                    DescribeId.Create("eisenstein-norm-mod-three"),
                    DescribeKind.Theorem,
                    H("Eisenstein norm residues modulo three"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/ZeroOrbitCongruence.eisenstein_norm_mod_three")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The norm polynomial x^2 - xy + y^2 takes only residues zero and one in Z/3Z. The proof exhausts all nine residue pairs.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("thirty-six-local-to-global"),
                    DescribeKind.Theorem,
                    H("The local candidates collapse to divisibility by 36"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/ZeroOrbitCongruence.thirty_six_dvd_of_local_candidates_and_eisenstein_norm")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "If the local computation leaves residues zero and eight modulo 36, and the represented residue is an Eisenstein norm modulo three, the residue eight branch is impossible. The result does not prove the local 432-case computation that supplies the candidate disjunction.")))))));
}
