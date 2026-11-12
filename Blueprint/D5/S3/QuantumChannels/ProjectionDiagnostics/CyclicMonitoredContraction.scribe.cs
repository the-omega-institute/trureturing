using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.ProjectionDiagnostics;

internal sealed class CyclicMonitoredContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual cyclic monitored restriction has no nonzero all-future hidden vector.",
        H("Cyclic monitored observability"),
        Blocks(Describe.Lean(
            DescribeId.Create("cyclic-monitored-future-kernel"),
            DeclarationHandle.Create("D5/S3/QuantumChannels/ProjectionDiagnostics/CyclicMonitoredContraction.cyclic_future_kernel_eq_bot"),
            H("The actual cyclic restriction has zero future kernel"),
            StatementSource.FromAuthor(Disp(Seq(
                F.Id("C"), Eq, F.Id("span"), Grp(F.Id("U"), Caret, F.Id("n"), F.Id("v")),
                Comma, Quad,
                F.Id("K"), Eq, F.Id("intersection"), Underscore, F.Id("n"),
                F.Id("ker"), Grp(Seq(F.Id("B"), Underscore, F.Id("C")),
                    Seq(F.Id("T"), Underscore, F.Id("C")), Caret, F.Id("n")),
                Eq, Grp(D(0))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every finite dimensional complex Hilbert space, every unitary U, and every "
                + "vector v, C is the span of the actual forward orbit U^n v. The operator T_C "
                + "is the restriction of (I-P_v)U and B_C is the restriction of P_v U. "
                + "Both preserve C. The theorem includes v=0 and requires no recurrence premise. "
                + "Orthogonal observability duality identifies the ambient hidden space; maximal "
                + "unobservability gives its invariance under the monitored step. On its intersection "
                + "with C the monitored step equals U. Finite dimensional injectivity supplies "
                + "surjectivity of this restricted U, hence inverse invariance. Every hidden cyclic "
                + "vector is then orthogonal to every U^n v and must vanish. "
                + "This is the structural no-dark obligation for the registered cyclic contraction "
                + "route. A strict power norm bound and the infinite weighted return identity "
                + "are not asserted here. The recurrence and expected-return result is classical: "
                + "Grunbaum, Velazquez, Werner and Werner, arXiv:1202.3903v3, Theorem 2."))),
            DescribeRole.Theorem))));
}
