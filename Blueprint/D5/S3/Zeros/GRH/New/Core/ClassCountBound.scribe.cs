using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Core;

internal sealed class ClassCountBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Class Count Bound", H("Class Count Bound"),
        Blocks(
            Paragraph(Text("Crude explicit bound for the class number of the standard unimodular hermitian genus.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Core/ClassCountBound.card_classes_le"),
                H("card_classes_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If N is a nonzero natural number in the different of E and f is the number of infinite places, then the standard definite hermitian space of rank n has at most (1 + 2(6N(fn)²)³)^{4fn²} classes Γ\\G_f/K, K = Kf the stabiliser of the standard lattice.")))))));
}
