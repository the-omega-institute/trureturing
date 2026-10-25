using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedSplitSuccessorOrderedDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/SignedSplitSuccessorOrdered.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adaptive signed columns with literal finite histories and prescribed reservoirs.",
        H("Ordered signed columns"),
        Blocks(
            Describe.Lean(DescribeId.Create("ordered-history"), DeclarationHandle.Create(Owner + "OrderedHistory"),
                H("Finite dynamic history"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A history of depth q stores the target indices, target clopens, finite clopen test families and every actual row's auxiliary indices on Fin(q). A column may contain countably many independent row choices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ordered-column"), DeclarationHandle.Create(Owner + "OrderedColumn"),
                H("One measured column"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The column stores the target index and clopen, the fixed finite tests and one auxiliary index for every row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("append-history"), DeclarationHandle.Create(Owner + "append"),
                H("Literal append"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All four old arrays are retained by Fin.snoc. The new entry is appended at the last index."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("restrict-history"), DeclarationHandle.Create(Owner + "restrict"),
                H("Exact truncation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Truncation restricts every array along Fin.castSucc."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ordered-column-spec"), DeclarationHandle.Create(Owner + "Spec"),
                H("Measured extension obligations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The predicate records exact truncation, increasing indices, the active row set, the literal finite exclusion and target slice, target whole-fibre constancy and signed mass, the finite test family, pool membership and every-lift finite signed marginal bounds. It is an output predicate, not a prefix assumption."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ordered-signed-column"), DeclarationHandle.Create(Owner + "exists_ordered_signed_column"),
                H("Adaptive signed column"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite set of rows with code below q and all earlier columns determine the exclusion. Compact separation derives every fixed clopen fibre test from the original continuous separating coordinates, including empty carriers or coordinate families. The target index retains the earlier tests; its literal slice supplies fibre constancy at that same index. Only then are all earlier tests and the three clopens B(q), H(q), R(q) combined, and each row chooses its next auxiliary index independently.")),
                    Paragraph(Text("The row bases form a dependent family. Inputs are actual signed references and infinite reservoirs, coordinate-E, positive target-variation convergence and the previous measured history. No moving-test estimate or suitable successor split is assumed. The one-column theorem does not choose old/new birth reservoirs or initialize the residual label."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordinary-pool"), DeclarationHandle.Create(Owner + "ordinaryPool"),
                H("Old reservoirs and the new row's signed pool"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Old J and permanent N have proof-indexed domains excluding the distinguished new row. Their intersection uses the original column parity. The new row instead uses its signed convergence pool; no old J or N is supplied at birth."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ordinary-reference"), DeclarationHandle.Create(Owner + "ordinaryReference"),
                H("Old references and the constructed birth reference"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An inherited signed reference is supplied only on old rows. The distinguished new row uses its independently extracted signed cluster. This definition never requests an old reference on the new row."))), DescribeRole.Definition))));
}
