using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class CrudeModularDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crude Modular Data", H("Crude Modular Data"),
        Blocks(
            Paragraph(Text("Kernels, data and the definite chain B of the proof, named. The level generator's ideal is the product of the chosen primes. Marked primes above a served prime, integral forms, even places, counts of low columns. Functions modulo a modulus give crude data, by finite Fourier expansion.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/CrudeModularData.isAdmissibleComb_vacuumDatum"),
                H("isAdmissibleComb_vacuumDatum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If all conjugates of the values of Ψ have modulus at most M, the datum Ψ ⊗ θ° is a finite combination of translates of θ° whose coefficients have, under every automorphism of ℂ, total modulus at most |O_E/𝔪|^(nn′)·M.")))))));
}
