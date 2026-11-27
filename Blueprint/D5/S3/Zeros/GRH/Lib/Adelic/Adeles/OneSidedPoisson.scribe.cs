using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class OneSidedPoissonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One Sided Poisson", H("One Sided Poisson"),
        Blocks(
            Paragraph(Text("self-duality of a number field in its adeles, strong approximation, and the Poisson inequality. The file treats totally complex fields, for which the field is its own annihilator and the pairing is non-degenerate. Strong approximation omitting a nonempty set of finite places is deduced from duality, and Poisson summation is an inequality for nonnegative lower semicontinuous functions. Source: J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, thesis 1950, in Cassels-Fröhlich ch. XV, Theorem 4.1.4; for strong approximation, Cassels, ch. II §15.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/OneSidedPoisson.sum_le_of_fourier"),
                H("sum_le_of_fourier"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("One-sided Poisson summation on the adeles of E: let F ≥ 0 be integrable and lower semicontinuous at the points of a finite set T ⊂ E. If S bounds all finite sums of |∫ ψ(−ξx)F(x) dx| over ξ in E, then ∑_{t∈T} F(t) ≤ S.")))))));
}
