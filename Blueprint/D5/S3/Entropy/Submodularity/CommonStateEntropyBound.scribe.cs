using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Submodularity;

internal sealed class CommonStateEntropyBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite state determined by either coordinate has entropy bounded by their mutual information.",
        H("Entropy of a Commonly Determined State"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-state-entropy-is-bounded-by-mutual-information"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/CommonStateEntropyBound."
                    + "common_state_entropy_le_mutual_information"),
                H("A commonly determined state is controlled by mutual information"),
                StatementSource.FromAuthor(CommonStateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be a normalized nonnegative mass function on finite X times Y. "
                            + "Let a : X -> C and b : Y -> C be deterministic maps into a "
                            + "finite common-state carrier. Assume a(x) = b(y) whenever the "
                            + "joint cell p(x,y) has nonzero mass. Then the entropy of the "
                            + "pushforward of the X-marginal through a is at most the mutual "
                            + "information of p.")),
                    Paragraph(Text(
                        "The support-qualified agreement is exactly the almost-sure statement "
                            + "that one common random state is determined from either "
                            + "coordinate. Zero-mass cells impose no agreement requirement and "
                            + "do not change the induced common-state law.")),
                    Paragraph(Text(
                        "The proof extends the joint law by the deterministic Y-to-C channel "
                            + "and applies the existing Markov data-processing inequality. "
                            + "Support agreement turns the X,C projection into the graph of a; "
                            + "the existing mutual-information entropy balance then identifies "
                            + "the information in that graph with the entropy of the common "
                            + "state. Loogle, LeanSearch, pinned-Mathlib, repository, and "
                            + "digestion-record searches found no exact theorem to bind."))),
                DescribeRole.Theorem))));

    private static Formula CommonStateFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula pxy = Seq(F.Id("p"), Open, x, Comma, Sp, y, Close);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, F.Id("X"), Comma, Sp, F.Id("Y"), Comma, Sp, F.Id("C"), Comma, RowBreak,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("X"), Close,
            CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("Y"), Close,
            CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("C"), Close,
            CloseBracket, Comma, RowBreak,
            F.Id("p"), Colon, Sp, F.Id("X"), Times, Sp, F.Id("Y"), To, Sp,
            Mathbb, Grp(F.Id("R")), Comma, RowBreak,
            F.Id("a"), Colon, Sp, F.Id("X"), To, Sp, F.Id("C"), Comma, Sp,
            F.Id("b"), Colon, Sp, F.Id("Y"), To, Sp, F.Id("C"), Comma, RowBreak,
            Open, Open, Forall, Sp, x, Comma, Sp, y, Comma, Sp,
            D(0), Leq, Sp, pxy, Close, Sp, Land, Sp,
            Sum, Underscore, Grp(x, Comma, y), pxy, Eq, D(1), Close, Comma, RowBreak,
            Open, Forall, Sp, x, Comma, Sp, y, Comma, Sp,
            pxy, Neq, D(0), Sp, Rightarrow, Sp,
            F.Id("a"), Open, x, Close, Eq, F.Id("b"), Open, y, Close, Close,
            Sp, Rightarrow, RowBreak,
            F.Id("H"), Open, F.Id("a"), Underscore, Grp(Star),
            F.Id("p"), Underscore, Grp(F.Id("X")), Close, Sp, Leq, Sp,
            F.Id("I"), Underscore, Grp(F.Id("p")), Open,
            F.Id("X"), Semi, F.Id("Y"), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
