using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GovernanceFixedPoint;

internal sealed class GovernanceFixedPointCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical carriers for governance gate equations with blind and self-reading "
            + "status derivation, together with the two-status flip.",
        H("Governance Fixed-Point Core"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gate"),
                DeclarationHandle.Create(Prefix + "Gate"),
                H("Gate agreement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A gate requires pointwise equality of the handwritten and derived "
                        + "status maps."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("blind-deriver"),
                DeclarationHandle.Create(Prefix + "BlindDeriver"),
                H("Blind derivation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A blind deriver reads a context and an entry without receiving the "
                        + "handwritten status map."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("self-reading-deriver"),
                DeclarationHandle.Create(Prefix + "SelfReadingDeriver"),
                H("Self-reading derivation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A self-reading deriver additionally receives the complete handwritten "
                        + "status map."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lift-blind"),
                DeclarationHandle.Create(Prefix + "liftBlind"),
                H("Blind lift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The canonical lift makes a blind deriver self-reading by ignoring its "
                        + "handwritten-map argument."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("status-blind"),
                DeclarationHandle.Create(Prefix + "StatusBlind"),
                H("Status blindness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Status blindness is exact factorization through the canonical blind "
                        + "lift."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("boolean-flip"),
                DeclarationHandle.Create(Prefix + "boolFlip"),
                H("Boolean flip"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Boolean flip exchanges false and true."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prefix-extension"),
                DeclarationHandle.Create(Prefix + "PrefixExtension"),
                H("Prefix extension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A new byte list extends an old one when it is the old list followed by "
                        + "a suffix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("tail-bytes"),
                DeclarationHandle.Create(Prefix + "TailBytes"),
                H("Tail bytes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Tail bytes are the document bytes at and after a starting offset."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("content-key"),
                DeclarationHandle.Create(Prefix + "ContentKey"),
                H("Content key"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A content key is represented by the complete byte list."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("content-key-constructor"),
                DeclarationHandle.Create(Prefix + "contentKey"),
                H("Content-key constructor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The canonical content key retains all input bytes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("verdict"),
                DeclarationHandle.Create(Prefix + "Verdict"),
                H("Verdict"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A settlement verdict is pending, admitted, or rejected."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("settlement"),
                DeclarationHandle.Create(Prefix + "Settlement"),
                H("Settlement view"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The settlement view maps logical identifiers to current verdicts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ledger-entry"),
                DeclarationHandle.Create(Prefix + "LedgerEntry"),
                H("Ledger entry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A ledger entry couples one logical identifier to its source bytes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("active-index"),
                DeclarationHandle.Create(Prefix + "ActiveIndex"),
                H("Active index view"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The active-index view maps each logical identifier to its active "
                        + "content key."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("active-source"),
                DeclarationHandle.Create(Prefix + "ActiveSource"),
                H("Active source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A content key is active for an identifier exactly when the index maps "
                        + "that identifier to the key."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rekey-result"),
                DeclarationHandle.Create(Prefix + "RekeyResult"),
                H("Rekey result"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A rekey result records its predecessor, replacement entry, active "
                        + "index, and settlement view."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("legal-tail-rekey"),
                DeclarationHandle.Create(Prefix + "LegalTailRekey"),
                H("Legal tail rekey"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A legal tail rekey preserves identity and settlement while extending "
                        + "the eligible source tail and updating only its active key."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conservative-rekey"),
                DeclarationHandle.Create(Prefix + "ConservativeRekey"),
                H("Conservative rekey"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A conservative rekey preserves settlement and every unrelated active "
                        + "index while replacing exactly one logical source."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-allowed"),
                DeclarationHandle.Create(Prefix + "JointAllowed"),
                H("Jointly allowed repairs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The jointly allowed repairs are the intersection of two rule sets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reachable-repair"),
                DeclarationHandle.Create(Prefix + "ReachableRepair"),
                H("Reachable repair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A repair class is reachable when it contains a jointly allowed repair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("deadlocked"),
                DeclarationHandle.Create(Prefix + "Deadlocked"),
                H("Deadlock"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A repair class is deadlocked when no repair in it is jointly allowed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("allowed-with-channel"),
                DeclarationHandle.Create(Prefix + "AllowedWithChannel"),
                H("Channel-extended allowance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Adding a channel unions its repairs with the jointly allowed set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conservative-channel"),
                DeclarationHandle.Create(Prefix + "ConservativeChannel"),
                H("Conservative channel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A conservative channel retains every formerly allowed repair and adds "
                        + "exactly the designated repair class."))),
                DescribeRole.Definition))));
}
