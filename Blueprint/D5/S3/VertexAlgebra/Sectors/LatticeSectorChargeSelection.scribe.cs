using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;
internal sealed class LatticeSectorChargeSelectionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeSectorChargeSelection", H("LatticeSectorChargeSelection"), Blocks(
            Paragraph(Text("Construction uses arbitrary ordinary symmetric even integral lattice data, including degenerate forms, zero charges and rank zero. Classification and universality require an explicit two-sided complex inverse Gram matrix, with no positivity or integer unimodularity.")),
            Describe.Lean(
                DescribeId.Create("latticesectorchargeselection-action-current"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorChargeSelection.action_current"),
                H("action_current"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("action_current on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorchargeselection-zero-current-ward"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorChargeSelection.zero_current_ward"),
                H("zero_current_ward"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("zero_current_ward on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorchargeselection-nonzero-coefficient-charge"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorChargeSelection.nonzero_coefficient_charge"),
                H("nonzero_coefficient_charge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("nonzero_coefficient_charge on the actual charge-labelled oscillator sectors; the precise parameters and conclusion are the compiled Lean statement."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticesectorchargeselection-wrong-charge-vanishing"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorChargeSelection.wrong_charge_vanishing"),
                H("wrong_charge_vanishing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Zero-current Ward yields a Gram-kernel charge constraint. An explicit complex inverse Gram turns it into exact charge equality, so every wrong-charge lawful IO is zero. No individual charge pairing or projected state is divided by."))), DescribeRole.Theorem),
            Paragraph(Text("Classical sources are Bakalov-Kac, arXiv math/0402315v1, section 4.1, and Matsuo-Nagatomo free-boson reconstruction. Imported residue/Pascal and Sugawara suppliers retain Scott Carnahan and Kalle Kytola source attribution and licenses. No literature novelty is claimed.")),
            Paragraph(Text("The category is the neutral Heisenberg sector category. Full charged lattice-VOA modules, dual-lattice coset fusion, coherent associativity and braiding, pentagon and hexagon, Monster or twisted anomaly, CFT, string theory and AdS/CFT remain additional unproved edges. Rank zero has one charge and a one-dimensional IO space; it is not the zero theory.")))));
}
