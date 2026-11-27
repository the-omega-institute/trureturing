using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Unitary;

internal sealed class CongruenceLevelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Congruence Level", H("Congruence Level"),
        Blocks(
            Paragraph(Text("Reduction maps, principal levels, levels cut out by reductions at split places; index. Parahoric and pro-p Iwahori groups, dominant cone, exponents, multiplicativity of U-operators. Principal congruence subgroups: neighbourhood basis, index bound, quotients of profinite integers.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Unitary/CongruenceLevel.relIndex_principalLevel_le"),
                H("relIndex_principalLevel_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a nonzero integer a of the CM field E, the index of the principal level K(a) in K₀ (Subgroup.relIndex, 0 if infinite) is at most N(a)^(n²), with N(a) the absolute norm of (a) and n the rank.")))))));
}
