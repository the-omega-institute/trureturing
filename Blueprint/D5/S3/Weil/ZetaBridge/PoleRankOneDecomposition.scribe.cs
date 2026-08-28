using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class PoleRankOneDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula test = F.Id("f");
        Formula variable = F.Id("x");
        Formula readout = Seq(
            Int, Underscore, Grp(Mathbb, Grp(F.Id("R"))), Sp,
            Exp, Open, Frac, Grp(variable), Grp(D(2)), Close, Sp,
            test, Open, variable, Close, Sp, F.Id("d"), variable);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The completed-zeta pole pair of a convolution square is one positive boundary "
                + "observation energy.",
            H("Pole Rank-One Decomposition"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("pole-pair-is-one-boundary-observation-energy"),
                    DeclarationHandle.Create(
                        "D5/S3/Weil/ZetaBridge/PoleRankOneDecomposition."
                            + "pole_rank_one_decomposition"),
                    H("The pole pair is one boundary observation energy"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, test, InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
                        Operatorname, Grp(F.Id("poleTerm")), Open,
                        Operatorname, Grp(F.Id("convolutionSquare")), Open, test, Close, Close,
                        Sp, Eq, Sp, D(2), Sp, Vert, readout, Vert, Caret, Grp(D(2))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Here W is the frozen carrier of even smooth compactly supported complex "
                            + "functions on the real line. The convolution square and pole term "
                            + "are the existing canonical objects. Evenness identifies the two "
                            + "half-frequency boundary readings, while the frozen complex-frequency "
                            + "convolution factorization turns each pole evaluation into the squared "
                            + "modulus of the displayed integral."))),
                    DescribeRole.Theorem))));
    }
}
