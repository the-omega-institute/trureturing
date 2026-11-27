using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class GlobalSieveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global Sieve", H("Global Sieve"),
        Blocks(
            Paragraph(Text("Adelic sieve: one-sided Poisson summation per pivot, frequency sum bound, final sieve inequality.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/GlobalSieve.sieve"),
                H("sieve"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The sieve, under Filling.IsAdmissible: for the forms J_v of the Bessel systems, a system J' at T (bounds e, finHeadWeight, Filling.frequencyGain), finite sets U ⊂ A of T-units, g⁻¹ a T-integer: Re ∑_{t∈U, p,q∈A^ϱ} J'∏J_v ≤ vol(Ô)^(ϱ+1)∏l(v,i)⁻²·(e∏_v((1+b⁻¹⁰)/deg_v) + b^(−6kf−10)/deg).")))))));
}
