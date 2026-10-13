using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Topology;

internal sealed class FinitePrefixCompactnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite realizability of every horizon forces one compatible infinite path.",
        H("Finite Prefix Compactness"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-prefixes-give-global-path"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Topology/FinitePrefixCompactness."
                    + "exists_global_path_of_finite_prefixes"),
            H("Finite prefixes give a global path"),
            StatementSource.FromAuthor(Formula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each time index has a finite discrete alphabet, and R records the allowed "
                        + "transition to the next index.")),
                Paragraph(Text(
                    "The N-prefix conditions form a decreasing sequence of nonempty closed "
                        + "subsets of the compact product. Cantor intersection compactness supplies "
                        + "a point in every stage, hence a path satisfying every transition.")),
                Paragraph(Text(
                    "This is the finite-prefix to infinite-path bridge used when extending "
                        + "symbolic or finite-state constructions to an actual infinite object."))),
            DescribeRole.Theorem))));

    private static Formula Formula()
    {
        Formula relation = F.Id("R");
        Formula finite = Call("FinitePrefixRealizable", relation);
        Formula global = Call("GlobalPath", relation);
        return Disp(Seq(finite, Sp, Rightarrow, Sp, global, Dot));
    }
}
