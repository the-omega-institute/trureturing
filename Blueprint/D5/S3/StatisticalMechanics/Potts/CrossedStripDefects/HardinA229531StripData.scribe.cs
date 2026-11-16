using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects;
internal sealed class HardinA229531StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.";
    private const string Note = "D5/L/SpinModels/hardin2013a229531";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact width-five HDA transfer.", H("Width-five HDA transfer"), Blocks(
            Describe.Lean(DescribeId.Create("row"), DeclarationHandle.Create(Prefix + "Row"),
                H("Actual rows"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Row is the function type Fin 5 to Fin 3. Its 243 values are the actual labelled rows."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("horizontal"), DeclarationHandle.Create(Prefix + "horizontal"),
                H("Horizontal bonds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The horizontal bond set is HardinA229583StripData.horizontal, containing the four adjacent pairs in Fin 5."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("between"), DeclarationHandle.Create(Prefix + "between"),
                H("Crossed bonds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The inter-row bond set is the union of HardinA229583StripData.antidiagonal with its coordinate-swapped image, containing both diagonals for each adjacent column pair."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid"), DeclarationHandle.Create(Prefix + "Valid"),
                H("Valid residual states"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Valid p d means that d is at most one and the internal horizontal defect count of p is at most one minus d."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("decidablevalid"), DeclarationHandle.Create(Prefix + "decidableValid"),
                H("Finite state decision"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The instance decides the conjunction defining Valid on an actual row and natural residual budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"), DeclarationHandle.Create(Prefix + "cl"),
                H("The class map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The map Row times Nat to Fin 20 identifies global colour permutations and reflection. Proper rows use HardinA233126SquareStrip.boundaryClass at Seen=(true,true); defective rows use their full equality pattern. The transition_counts theorems pin the class transfer for every valid state."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"), DeclarationHandle.Create(Prefix + "T"),
                H("The transfer matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("T is an integer matrix indexed by Fin 20 on both axes. Its proper-row diagonal subblocks call HardinA233171DiagonalStrip.transfer at indices one through six and divide by 32. The division removes the two lifts per colour in each of five cells after Seen is saturated. Every entry is pinned to the actual three-colour successor sum by HardinA229531StripClasses.transition_counts."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial"), DeclarationHandle.Create(Prefix + "initial"),
                H("Initial distribution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The vector Fin 20 to Int counts first rows by their exact residual budget and class. HardinA229531Strip.finite_certificate verifies these weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"), DeclarationHandle.Create(Prefix + "terminal"),
                H("Terminal acceptance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The vector Fin 20 to Int is one exactly at zero-residual classes and zero otherwise; HardinA229531Strip.finite_certificate checks this for all valid rows."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"), DeclarationHandle.Create(Prefix + "W"),
                H("Forward weights"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("W has type Fin 14 to Fin 20 to Int. Its fourteen rows are the initial vector followed by thirteen right multiplications by T. HardinA229531Strip.finite_certificate pins those identities and the order-twelve polynomial relation."))), DescribeRole.Definition))));
}
