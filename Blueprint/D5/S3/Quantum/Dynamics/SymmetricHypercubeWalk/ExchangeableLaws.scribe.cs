using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk;

internal sealed class ExchangeableLawsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ExchangeableLaws.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Hamming/ide2026scaling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At fixed order, a finite sampling estimate identifies a Walsh coefficient with a shifted moment up to vanishing error.",
        H("Exchangeable cube laws and shifted radial moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("abs-walshcoefficient-sub-shiftedmoment-le"),
                DeclarationHandle.Create(Prefix + "abs_walshCoefficient_sub_shiftedMoment_le"),
                H("The sampling error bound"),
                StatementSource.FromAuthor(Disp(Seq(Lvert, Sp, F.Id("W"), Underscore, Grp(F.Id("c")), Open, Mu, Close, Minus, F.Id("M"), Underscore, Grp(F.Id("k")), Open, Nu, Close, Rvert, Sp, Leq, Sp, Frac, Grp(F.Id("k"), Open, F.Id("k"), Minus, D(1), Close), Grp(F.Id("d"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let μ be permutation-invariant on the d-cube, let ν be its normalized Hamming-weight pushforward, and let c embed k coordinates. The coefficient W_c is the expected product of the k coordinate signs. Sampling without replacement computes this same expectation by exchangeability. Sampling with replacement computes M_k(ν). A collision union bound gives k(k−1)/d. For fixed k the corresponding bound for a difference of two laws is twice this quantity. At d = 0 the embedding forces k = 0, both observables are one, and the bound uses Lean’s convention that division by zero is zero."))),
                DescribeRole.Theorem))));
}
