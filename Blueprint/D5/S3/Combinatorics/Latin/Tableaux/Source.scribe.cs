using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Latin.Tableaux;

internal sealed class SourceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Latin/Tableaux/Source.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/daugherty2026counting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal source Latin tableaux: Source", H("Source for Latin tableaux"),
        Blocks(
            Paragraph(Text("Daugherty et al., arXiv:2610.29291v1, Conjecture 6.3 asks for the full count of Latin tableaux of shape (k,k-1,...,5,4,3,3) for every integer k at least five. Cells and integer symbols retain their fixed identities, and the prescribed symbol multiplicities are those of the conjugate partition.")),
            Describe.Lean(DescribeId.Create("latin-source-cells"),
                DeclarationHandle.Create(Prefix + "Cells"), H("Fixed source cells"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The dependent cell type keeps every row and column position, including the two distinct bottom rows of length three."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-source-filling"),
                DeclarationHandle.Create(Prefix + "Filling"), H("Unrestricted integer fillings"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A filling assigns an arbitrary integer to every fixed source cell. No bounded-symbol assumption enters the source definition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-source-shape"),
                DeclarationHandle.Create(Prefix + "shape"), H("The exact conjectural shape"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For k at least five this is (k,k-1,...,5,4,3,3), in the source order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-source-conjugate"),
                DeclarationHandle.Create(Prefix + "conjugate"), H("The full conjugate type"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The multiplicity of an integer s is the number of rows of length at least s when s is positive, and zero otherwise."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-source-sourcelatin"),
                DeclarationHandle.Create(Prefix + "SourceLatin"), H("Literal source Latin tableaux"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every row and column is injective, and the multiplicity equation is imposed for every integer symbol. This is the unreduced count of Definition 2.5 and Section 4."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-source-lt"),
                DeclarationHandle.Create(Prefix + "LT"), H("The literal source count"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Nat.card of the entire subtype of unrestricted integer fillings satisfying SourceLatin. Finiteness is subsequently proved."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-source-rowsymbols"),
                DeclarationHandle.Create(Prefix + "rowSymbols"), H("Actual row symbols"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The finite image of the filling on a single fixed row."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-source-source-row-symbols"),
                DeclarationHandle.Create(Prefix + "source_row_symbols"), H("Conjugate type forces row saturation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Strong induction on symbols and exact multiplicity quotas prove that every row has exactly the integers 1 through its length. This is proved from the full type condition, rather than assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-source-rowlatin"),
                DeclarationHandle.Create(Prefix + "RowLatin"), H("Equivalent row formulation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Rows are injective and have the full initial interval of integer symbols, and columns remain injective."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-source-source-iff-rows"),
                DeclarationHandle.Create(Prefix + "source_iff_rows"), H("Both directions of source correspondence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The converse counts occurrences by an explicit bijection with rows containing the symbol, recovering the conjugate multiplicities for all integers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-source-finitelatin"),
                DeclarationHandle.Create(Prefix + "FiniteLatin"), H("Finite carrier with actual integer interpretation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A row of length m uses Fin m; its integer interpretation is value plus one. Fixed positions are preserved."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-source-sourceequiv"),
                DeclarationHandle.Create(Prefix + "sourceEquiv"), H("Reversible unrestricted-to-finite correspondence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Explicit inverse functions give an equivalence between all source integer tableaux and FiniteLatin. Equal-length rows and all fixed integer symbols remain distinct."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-source-source-finite"),
                DeclarationHandle.Create(Prefix + "source_finite"), H("Source finiteness"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Transport finiteness along sourceEquiv. The finite carrier is justified by a reversible correspondence, not substituted for the source objects."))), DescribeRole.Theorem)), []));
}
