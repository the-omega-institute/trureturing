using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostStateFieldDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostStateField.";
    private static DocumentBlock Node(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("bc-state-field-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual signed occupation-word ghost fields on the full countable Fock carrier.",
        H("The actual ghost state-field construction"), Blocks(
            Paragraph(Text("The carrier, vacuum, occupation creators, CAR and parity are exactly those of CountableOccupationFock and BcGhostFock. An ascending occupation list gives nested divided derivatives of the physical b and c fields. A reverse-ordered normal-product half carries the sign determined by the tail length. This construction defines a linear map on every finitely supported occupation state and does not replace the carrier by a finite cutoff.")),
            Paragraph(Text("The signed normal product is the vectorwise finite constructor SignedFieldNormalProductLocality.signedNormalMinusOne. Its covariance is the minus-one case of SignedFieldResidueLocality.residue_translation, using negativeResidue and the zero Hasse derivative. These generic results retain the attribution to Scott Carnahan's vertexAlg source; the occupation-word construction uses their signed reverse half.")),
            Node("stateField_creation", "All-state creation and the exact physical generators",
                "The minus-one coefficient creates every actual state, every nonnegative coefficient annihilates the vacuum, and the vacuum field is the identity field. The generating states are the singleton occupations zero and one. Their normalized vertex modes are respectively the physical b mode shifted by minus one and c mode shifted by plus two."),
            Node("stateField_translation", "Covariance for the original ghost translation",
                "The translation is BcGhostVirasoro.L at minus one. Its vacuum value vanishes, and its commutator with every state-field mode is the formal derivative coefficient. The proof uses the original b and c Ward identities, the integer binomial shift and the generic signed residue covariance; no translation operator is supplied as an assumption."),
            Node("stateField_parity", "Parity on the full state space",
                "Conjugation by occupation parity intertwines every state-field coefficient with the field of the parity-transformed state. This holds for arbitrary inhomogeneous finite sums and specializes to the homogeneous sign through linearity."),
            Paragraph(Text("The companion BcGhostStateFieldLocality and BcGhostStateFieldIterate modules establish homogeneous all-state signed locality and the signed all-integer iterate law with finite coefficient sums. This document does not identify the conformal state with the existing ghost Virasoro field, the ghost cubic with a state zero mode, or prove the BRST derivation, physical bracket, no-ghost, string or AdS/CFT programme.")))));
}
