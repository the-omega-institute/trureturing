using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.GoodReduction;

internal sealed class ThetaOrthogonalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Theta Orthogonality", H("Theta Orthogonality"),
        Blocks(
            Paragraph(Text("Valuations of theta values at torsion points, sup norm, boundedness, peak-shifting defects. Orthogonality of translates of theta functions; stable integral lattices are proportional.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/GoodReduction/ThetaOrthogonality.exists_proportional_orbit_lattice"),
                H("exists_proportional_orbit_lattice"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let B be positive, N·L^∨ ⊂ L with N and all c(a)c(−a) units of the valuation ring O. For finite non-zero theta families f_i, g_k and some γ ≠ 0, an O-module stable under the c(a)U_a (a ∈ L^∨) contains all g_k iff all γf_i.")))))));
}
