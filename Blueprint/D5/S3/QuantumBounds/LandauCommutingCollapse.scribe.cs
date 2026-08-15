using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class LandauCommutingCollapseDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Landau =
        LibraryNoteRef.Create("D5/L/Quantum/landau1987violation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local commutativity collapses the algebraic CHSH square to four times the identity.",
        H("CHSH Square under Local Commutativity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-commutativity-collapses-the-chsh-square"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/LandauCommutingCollapse." +
                    "chsh_square_eq_four_of_local_pair_commutes"),
                H("Local commutativity collapses the CHSH square"),
                StatementSource.FromAuthor(CommutingCollapseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A0 and A1 and B0 and B1 be finite complex Hermitian " +
                        "involutions. If either the Alice pair or the Bob pair commutes, " +
                        "then the square of their CHSH matrix is four times the identity. " +
                        "The proof specializes LandauIdentity.landau_identity: the local " +
                        "commutation equality makes one commutator, and hence their " +
                        "Kronecker product, zero.")),
                    Paragraph(
                        Text(
                            "Lawrence J. Landau's 1987 work on the violation of Bell's " +
                            "inequality in quantum theory is contextual historical credit; "),
                        Ref(Landau.Value),
                        Text(
                            " records its verified bibliographic metadata and access limit. " +
                            "The article text was not readable, so this repository-derived " +
                            "provenance does not claim that the paper states this exact " +
                            "commuting-pair corollary.")),
                    Paragraph(Text(
                        "This is only the algebraic square equality under a commuting local " +
                        "pair. It does not assert an expectation bound of two, an " +
                        "operator-norm CHSH bound of two, or any optimization over states."))),
                DescribeRole.Theorem))));

    private static Formula CommutingCollapseFormula() => Disp(Seq(
        Forall, Sp, F.Id("m"), Comma, Sp, F.Id("n"), Comma, Esc,
        OpenBracket,
        Operatorname, Grp(F.Id("Fintype")), Open, F.Id("m"), Close,
        CloseBracket, Sp,
        OpenBracket,
        Operatorname, Grp(F.Id("DecidableEq")), Open, F.Id("m"), Close,
        CloseBracket, Sp,
        OpenBracket,
        Operatorname, Grp(F.Id("Fintype")), Open, F.Id("n"), Close,
        CloseBracket, Sp,
        OpenBracket,
        Operatorname, Grp(F.Id("DecidableEq")), Open, F.Id("n"), Close,
        CloseBracket, Comma, Esc,
        Forall, Sp,
        F.Id("A"), Underscore, Grp(D(0)), Comma, Sp,
        F.Id("A"), Underscore, Grp(D(1)), InMacro, Sp,
        F.Id("M"), Underscore, Grp(F.Id("m")),
        Open, Mathbb, Grp(F.Id("C")), Close, Comma, Esc,
        Forall, Sp,
        F.Id("B"), Underscore, Grp(D(0)), Comma, Sp,
        F.Id("B"), Underscore, Grp(D(1)), InMacro, Sp,
        F.Id("M"), Underscore, Grp(F.Id("n")),
        Open, Mathbb, Grp(F.Id("C")), Close, Comma, Esc,
        ObservableHypotheses(), Sp, Land, Sp,
        LocalCommutativity(), Sp, Rightarrow, Sp, Esc,
        Operatorname, Grp(F.Id("let")), Sp,
        F.Id("S"), Colon, Eq, CHSHMatrix(), Semi, Esc,
        F.Id("S"), Caret, Grp(D(2)), Eq,
        D(4), Cdot, Sp,
        F.Id("I"), Underscore, Grp(F.Id("m"), Times, Sp, F.Id("n"))));

    private static Formula ObservableHypotheses() => Seq(
        ObservableHypothesis("A", 0, "m"), Sp, Land, Sp,
        ObservableHypothesis("A", 1, "m"), Sp, Land, Sp,
        ObservableHypothesis("B", 0, "n"), Sp, Land, Sp,
        ObservableHypothesis("B", 1, "n"));

    private static Formula ObservableHypothesis(string family, byte index, string dimension) =>
        Seq(
            Open,
            Operatorname, Grp(F.Id("Hermitian")), Open,
            F.Id(family), Underscore, Grp(D(index)), Close,
            Sp, Land, Sp,
            F.Id(family), Underscore, Grp(D(index)), Caret, Grp(D(2)),
            Eq, F.Id("I"), Underscore, Grp(F.Id(dimension)),
            Close);

    private static Formula LocalCommutativity() => Seq(
        Open,
        Open,
        F.Id("A"), Underscore, Grp(D(0)), Sp,
        F.Id("A"), Underscore, Grp(D(1)), Eq,
        F.Id("A"), Underscore, Grp(D(1)), Sp,
        F.Id("A"), Underscore, Grp(D(0)),
        Close, Sp, Lor, Sp,
        Open,
        F.Id("B"), Underscore, Grp(D(0)), Sp,
        F.Id("B"), Underscore, Grp(D(1)), Eq,
        F.Id("B"), Underscore, Grp(D(1)), Sp,
        F.Id("B"), Underscore, Grp(D(0)),
        Close,
        Close);

    private static Formula CHSHMatrix() => Seq(
        Operatorname, Grp(F.Id("kronecker")), Open,
        F.Id("A"), Underscore, Grp(D(0)), Comma, Sp,
        F.Id("B"), Underscore, Grp(D(0)), Close,
        Plus,
        Operatorname, Grp(F.Id("kronecker")), Open,
        F.Id("A"), Underscore, Grp(D(0)), Comma, Sp,
        F.Id("B"), Underscore, Grp(D(1)), Close,
        Plus,
        Operatorname, Grp(F.Id("kronecker")), Open,
        F.Id("A"), Underscore, Grp(D(1)), Comma, Sp,
        F.Id("B"), Underscore, Grp(D(0)), Close,
        Minus,
        Operatorname, Grp(F.Id("kronecker")), Open,
        F.Id("A"), Underscore, Grp(D(1)), Comma, Sp,
        F.Id("B"), Underscore, Grp(D(1)), Close);
}
