using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.PeriodRings;

internal sealed class AmaxStructureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Amax Structure", H("Amax Structure"),
        Blocks(
            Paragraph(Text("Adic extension of linear maps; existence of (p,z)-adic topological bases with coordinates. Subgroup of multiples of n in an abelian group; link with adic filtration. Separated module of bounded rank with regular parameters over complete base is finite free. Coordinates of an adic topological basis: approximation, submodule membership, separation. Colmez's A_max, B_max^+, B_max with Frobenius, Galois action and θ. A_max modulo p is a polynomial ring; how A_inf lies in A_max.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/AmaxStructure.mem_span_pow_of_p_pow_dvd"),
                H("mem_span_pow_of_p_pow_dvd"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If the image in A of an element a of A_inf is divisible by p^m, then a lies in the ideal (p, ξ)^m of A_inf.")))))));
}
