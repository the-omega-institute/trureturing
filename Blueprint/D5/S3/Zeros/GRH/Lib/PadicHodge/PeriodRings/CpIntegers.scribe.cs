using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.PeriodRings;

internal sealed class CpIntegersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cp Integers", H("Cp Integers"),
        Blocks(
            Paragraph(Text("C_p, its integers, isometric Galois action; functoriality of tilt, untilt and Fontaine's θ.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/CpIntegers.untilt_dvd_iff"),
                H("untilt_dvd_iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let R be a p-adically complete, integrally closed domain in which p is not a unit. For x, y in the tilt of R, x^♯ divides y^♯ in R if and only if x divides y.")))))));
}
