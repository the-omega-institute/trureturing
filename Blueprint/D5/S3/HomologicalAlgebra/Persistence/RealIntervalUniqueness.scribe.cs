using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Persistence;

internal sealed class RealIntervalUniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/bauer2015persistence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual supported interval sums used in natural classification and endpoint recovery.",
        H("Actual Real Interval Sums"),
        Blocks(
            Definition("interval-family", "IntervalFamily", "Positive finite or essential intervals",
                "An occurrence has a real birth and a death in WithTop(Real), strictly greater than "
                    + "birth. Infinity is allowed. Repeated intervals retain separate occurrences."),
            Definition("interval-space", "intervalSpace", "The actual supported coordinate subspace",
                "At time r this is the subspace of K-valued occurrence coordinates that vanish "
                    + "unless birth <= r < death. The field is arbitrary."),
            Definition("interval-arrow", "intervalArrow", "The actual structure map",
                "For s <= t, retain source coordinates whose deaths are strictly above t and kill "
                    + "the others. The output lies in the supported subspace at t."),
            Definition("interval-sum", "intervalSum", "A real persistence functor",
                "The supported spaces and actual arrows form a functor from the real preorder to "
                    + "ModuleCat. Identity and composition hold at exact birth/death points, "
                    + "zero spaces and infinite tails. The substantive classification and "
                    + "arbitrary competing-decomposition uniqueness proof is in RealDecomposition."))));

    private static DocumentBlock.Describe Definition(string id, string declaration, string heading, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(body))), DescribeRole.Definition);
}
