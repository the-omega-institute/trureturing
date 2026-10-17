using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedOriginalOrbitGyrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original primitive-path orbits and forward gyration",
        H("Original primitive-path orbits and forward gyration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("countedoriginalorbitgyration-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration.numberedWordEquiv"),
                H("Recover all legal original numbered words"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Splitting each original product edge recovers both vertex words and the actual two half-edge labels. Legality supplies the outside seam and dependent endpoint transports. Rejoining proves the inverse equation, including empty fibers and zero vertex counts. Restriction and signed-time periodic extension give an equivalence with actual periodic paths; finite primitivity agrees with the original minimal shift period."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("countedoriginalorbitgyration-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration.orbitBasisEquiv"),
                H("The quotient has a unique least numbered representative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The orbit relation is reachability by nonnegative iterates of the actual forward shift on primitive paths. Periodic coordinate reduction identifies it with cyclic rotation of their finite restrictions. The original edge key compares source, target, then parallel-edge number; its induced lexicographic word key selects a unique least rotation of each primitive word. This yields a bijection from the actual path-orbit quotient to the least-word basis. Finiteness is obtained from the finite legal-word carrier, without graph inhabitedness assumptions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("countedoriginalorbitgyration-4"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration.primitivePath_card_eq_period_mul_orbit_card"),
                H("Primitive-path cardinality is period times orbit cardinality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every square count matrix A and every positive period d, the number of actual paths of minimal period d equals d times the number of their actual forward-shift orbits. Each path determines its least numbered representative and its forward phase in Fin d. Shifting the representative by that phase recovers the path. Conversely, minimal period makes phases below d unique, so this correspondence is a bijection with the product of the canonical basis and Fin d. The quotient-to-basis equivalence then gives the cardinality identity.")),
                    Paragraph(Text("This is the classical count for free finite cyclic orbits on the original path carrier. No nonempty graph or nonempty primitive stratum is required: empty strata contribute zero on both sides."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countedoriginalorbitgyration-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration.relativeForwardGyration_eq_order_types"),
                H("From actual forward offsets to the order-type lift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The elementary homeomorphism induces the original primitive-path and orbit equivalences. For an image path x, canonicalForwardOffset is defined as the negative of the least-rotation index k in Fin d. The proved forward-offset equation carries the canonical target representative to x by that many forward shifts. The proved residue formula identifies its image in ZMod d with the integer minus k.")),
                    Paragraph(Text("RelativeForwardGyration sums these offsets over the actual source quotient, through its proved basis equivalence. Reindexing by legal numbered words gives the integer word-weight sum modulo d. The order-type decomposition then yields orderTypeGyrationLift: the finite integer sum of rank-word weights times products of entrywise binomial coefficients. The theorem asserts equality in ZMod d for every n,m and every nonzero d; no desired orbit-sum identity is assumed.")),
                    Paragraph(Text("This uses the classical finite-orbit transversal and necklace/least-rotation method. It supplies one dependency for the original SGCC objective. Full SGCC, image exhaustion, the localized triangle and the full beam/word comparison are not established here."))),
                DescribeRole.Theorem))));
}
