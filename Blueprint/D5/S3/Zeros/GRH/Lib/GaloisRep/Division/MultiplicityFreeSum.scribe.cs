using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.Division;

internal sealed class MultiplicityFreeSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multiplicity Free Sum", H("Multiplicity Free Sum"),
        Blocks(
            Paragraph(Text("Degree-n killing polynomials and free cocharacter weights force rank n and characteristic polynomials. Twisting a Galois representation by an algebraic Hecke character shifts weights and Hecke polynomials. Sum of distinct irreducible constituents keeps goodness, occurring weights and killing polynomial.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/Division/MultiplicityFreeSum.exists_rep_span_diagonal"),
                H("exists_rep_span_diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Suppose that for each τ some continuous ρ_τ is, along the filter F of places w, unramified or crystalline, with J(τ) occurring among its jumps at τ and P_w killing geometric Frobenius. Then one continuous r, whose image spans all diagonal matrices, does this for all τ.")))))));
}
