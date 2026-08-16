namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    internal static FrozenActiveEntry ApplyReattest(
        FrozenActiveEntry entry,
        FrozenReattestPayload payload,
        string eventHash,
        FrozenNodeMaterial? validatedMaterial = null)
    {
        if (payload.IsLegacyFormat)
        {
            var legacyMaterial = payload.HasAxiomClosure
                ? entry.Material with { AxiomClosure = payload.AxiomClosure }
                : entry.Material;
            return entry with
            {
                Material = legacyMaterial,
                Payload = entry.Payload with
                {
                    AxiomClosure = payload.HasAxiomClosure
                        ? payload.AxiomClosure
                        : entry.Payload.AxiomClosure,
                    Input = payload.Input,
                    InputFingerprint = payload.InputFingerprint,
                    SemanticReceipt = payload.SemanticReceipt,
                },
                LastAttestationEventHash = eventHash,
                AxiomClosureKnown = entry.AxiomClosureKnown || payload.HasAxiomClosure,
            };
        }

        var frozenNodeId = payload.FrozenNodeId
            ?? throw new FormatException("Extended Reattest is missing frozen_node_id.");
        var statementId = payload.StatementId
            ?? throw new FormatException("Extended Reattest is missing statement_id.");
        var witnessId = payload.WitnessId
            ?? throw new FormatException("Extended Reattest is missing witness_id.");
        var material = validatedMaterial ?? new FrozenNodeMaterial(
            entry.Material.RepoPath,
            payload.DeclarationStatementIds,
            statementId,
            witnessId,
            frozenNodeId,
            payload.PrerequisiteFrozenNodeIds,
            payload.HasAxiomClosure ? payload.AxiomClosure : entry.Material.AxiomClosure,
            new FrozenModuleAttestation(
                entry.Material.RepoPath,
                payload.Input.DescriptorBlobOid)
            {
                BaseCommitOid = payload.Input.BaseCommitOid,
                BaseTreeOid = payload.Input.BaseTreeOid,
            });
        return entry with
        {
            Material = material,
            Payload = entry.Payload with
            {
                DeclarationStatementIds = payload.DeclarationStatementIds,
                AxiomClosure = payload.HasAxiomClosure
                    ? payload.AxiomClosure
                    : entry.Payload.AxiomClosure,
                FrozenNodeId = frozenNodeId,
                Input = payload.Input,
                InputFingerprint = payload.InputFingerprint,
                PrerequisiteFrozenNodeIds = payload.PrerequisiteFrozenNodeIds,
                SemanticReceipt = payload.SemanticReceipt,
                StatementId = statementId,
                WitnessId = witnessId,
            },
            LastAttestationEventHash = eventHash,
            AxiomClosureKnown = entry.AxiomClosureKnown || payload.HasAxiomClosure,
        };
    }
}
