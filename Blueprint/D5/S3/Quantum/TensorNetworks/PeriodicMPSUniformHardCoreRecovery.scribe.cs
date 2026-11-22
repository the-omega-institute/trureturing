using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSUniformHardCoreRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformHardCoreRecovery";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-site reconstruction near the cyclic independent-set state",
        H("Two-site reconstruction near the cyclic independent-set state"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorerecovery-exists-generic-actual-reconstruction"),
                DeclarationHandle.Create(Module + ".exists_generic_actual_reconstruction"),
                H("Generic reconstruction in an actual-state neighborhood"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps"),
                    LibraryNoteRef.Create("D5/L/StatisticalMechanics/lesanovsky2012constrainedspinchain")),
                Blocks(
                    Paragraph(Text("For each ring length n ≥ 7, the normalized projector of the equal-weight cyclic independent-set state lies in a relatively Euclidean-open neighborhood in the actual periodic binary bond-two projector image. This neighborhood contains a relatively open dense set of targets. For each such target, equality of the trace-one first adjacent two-site marginals with any actual projector of that length forces equality of the full projectors. Equality of projectors identifies the same ray, or the same unit-mass amplitude up to phase.")),
                    Paragraph(Text("The witness marginal has a singleton fiber even in the compact closure of the actual projector image. Compactness and a determinant-pencil decoder force all actual competitors with sufficiently nearby observations into the four-complex-dimensional ordinary trace chart. Seven regular real readouts leave one real coordinate. Along that coordinate, the real 00,01 coherence has a strict analytic fold, with curvature certified by the shifted hard-core energy.")),
                    Paragraph(Text("Two analytic paths share the seven regular readouts and the fold coherence. The normalized 11,11 population separates them at fourth order with a nonzero coefficient of sign (−1)^(n−1). A length recurrence lifts the checked transfer-coefficient identities to every n ≥ 7. Analyticity makes the coincidence set of the two branches nowhere dense, and localization transfers singleton fibers to the actual projector image.")),
                    Paragraph(Text("Lesanovsky supplies the periodic constrained ground-state model and its equal weights at fugacity one. Critch and Morton formulate the broader marginal reconstruction question in Conjecture 10. Density here is relative to the specified neighborhood for each length."))),
                DescribeRole.Theorem))));
}
