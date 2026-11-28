using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class BesselCutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bessel Cut", H("Bessel Cut"),
        Blocks(
            Paragraph(Text("Normalise a real-place Bessel function and cut it off. A Bessel function at a real place, an average of a discrete series coefficient that is large at one point, inherits the coefficient's decay, and normalising it and multiplying by a scalar cut-off gives a continuous approximant, close in L² and compactly supported modulo the unipotent group, with an explicit tail bound. Averages of integrable discrete series coefficients over a unipotent group and their decay are known, and the normalisation and scalar cut-off with a tail bound are standard. Related work: Muić, Fourier coefficients of automorphic forms and integrable discrete series, 2015; Miličić, Asymptotic behavior of matrix coefficients of the discrete series, 1977; Wallach, Real Reductive Groups II, 1992.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/BesselCut.exists_cut_isCutPair"),
                H("exists_cut_isCutPair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Given a peaked Bessel function (HasPeakAt) at x with besselSize x ≤ b^{5(ϱ+1)}, and numerical bounds on b, n, l, there are F, reproduced by convolution with deg·ψ_l, and V such that (F, V) satisfies IsCutPair.")))))));
}
