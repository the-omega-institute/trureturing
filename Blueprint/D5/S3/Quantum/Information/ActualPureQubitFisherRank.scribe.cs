using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ActualPureQubitFisherRankDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ActualPureQubitFisherRank.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral SLD information bounds measurement Fisher information and controls the rank-one branch.",
        H("Fisher information and the qubit rank alternative"),
        Blocks(
            Paragraph(Text("The measurement Fisher statement allows arbitrary finite matrix and outcome index sets n and J, including empty sets; Jm in the rank alternative is Fin m. PSD means positive semidefinite, 1n is the identity matrix, and all derivatives are real derivatives. C1(I) means continuously differentiable on I. spectralQFI is the spectral SLD information defined in ActualPureQubitGeometry; the displayed cost uses positivity at zero supplied by the hypotheses. The real rank is the dimension of the range of the real linear map effectReadout. Open refers to the ordinary topology of the real line.")),
            Describe.Lean(DescribeId.Create("spectral-energy"),
                DeclarationHandle.Create(Module + "spectral_energy"), H("Spectral information equals SLD energy"),
                StatementSource.FromAuthor(EnergyFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite index type n with decidable equality, including the empty type, rho is positive semidefinite and L is Hermitian. The SLD equation alone implies the energy identity for any complex matrix B. The positive-semidefinite proof hp is the argument used by spectralQFI to choose its spectral decomposition. No invertibility assumption is needed.")))),
            Describe.Lean(DescribeId.Create("actual-fisher"),
                DeclarationHandle.Create(Module + "actual_fisher"), H("Measurement Fisher lower bound"),
                StatementSource.FromAuthor(FisherFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two neighborhood hypotheses are two-sided at zero. The lower bound applies to the spectral information of the differentiable positive curve with the stated exact real-part readout.")))),
            Describe.Lean(DescribeId.Create("actual-rank-alternative"),
                DeclarationHandle.Create(Module + "actual_rank_alternative"), H("Rank alternative and binary cost gap"),
                StatementSource.FromAuthor(AlternativeFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every chosen negative-score index and positive-score index, the conclusion is the displayed disjunction. The hypotheses require positive effects but do not require their sum to be the identity or I to be preconnected.")))))));

    private static Formula EnergyFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, Forall, Sp, F.Id("n"), Esc, Operatorname, Grp(F.Id("finite")),
        Comma, Esc, Forall, Rho, Comma, F.Id("B"), Comma, F.Id("L"), InMacro, Mathbb, Sp, F.Id("C"), Caret,
        Grp(F.Id("n"), Times, Sp, F.Id("n")), Comma, Esc, Forall, Sp, F.Id("h"), Underscore, F.Id("p"), InMacro,
        Operatorname, Grp(F.Id("PSD")), Open, Rho, Close, Comma, RowBreak, Amp, F.Id("L"), Caret, Star, Eq,
        F.Id("L"), Esc, Land, Esc, F.Id("L"), Rho, Plus, Rho, Sp, F.Id("L"), Eq, D(2), F.Id("B"), Longrightarrow,
        Operatorname, Grp(F.Id("Re")), Operatorname, Grp(F.Id("tr")), Open, F.Id("L"), Rho, Sp, F.Id("L"), Close,
        Eq, Operatorname, Grp(F.Id("spectralQFI")), Open, Rho, Comma, F.Id("B"), Comma, F.Id("h"), Underscore,
        F.Id("p"), Close, Dot, End, Grp(F.Id("aligned"))));

    private static Formula FisherFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, Forall, Sp, F.Id("n"), Comma, F.Id("J"), Esc, Mathrm, Grp(F.Id("finite")), Comma, Esc, F.Id("N"),
        Colon, F.Id("J"), To, Mathbb, Sp, F.Id("C"), Caret, Grp(F.Id("n"), Times, Sp, F.Id("n")), Comma, Esc, Rho, Colon, Mathbb, Sp, F.Id("R"), To, Mathbb, Sp,
        F.Id("C"), Caret, Grp(F.Id("n"), Times, Sp, F.Id("n")), Comma, Esc, F.Id("p"), Comma, F.Id("v"), Colon, F.Id("J"), To, Mathbb, Sp, F.Id("R"),
        Comma, RowBreak, Amp, Open, Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Comma, Operatorname, Grp(F.Id("PSD")), Open, F.Id("N"), Underscore,
        F.Id("j"), Close, Close, Land, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J")), F.Id("N"), Underscore, F.Id("j"), Eq, D(1),
        Underscore, F.Id("n"), Land, Open, Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Comma, D(0), Lt, F.Id("p"), Underscore, F.Id("j"), Close, Land,
        Operatorname, Grp(F.Id("DifferentiableAt")), Open, Rho, Comma, D(0), Close, RowBreak, Amp, Land, Esc, Open, Exists, DeltaLower, Gt, D(0),
        Comma, Forall, Sp, F.Id("u"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Esc, Bar, F.Id("u"), Bar, Lt, DeltaLower, Longrightarrow, Operatorname,
        Grp(F.Id("PSD")), Open, Rho, Open, F.Id("u"), Close, Close, Close, RowBreak, Amp, Land, Esc, Open, Exists, DeltaLower, Underscore, D(2),
        Gt, D(0), Comma, Forall, Sp, F.Id("u"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Esc, Bar, F.Id("u"), Bar, Lt, DeltaLower, Underscore, D(2),
        Longrightarrow, Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Comma, Operatorname, Grp(F.Id("Re")), Operatorname, Grp(F.Id("tr")), Open,
        F.Id("N"), Underscore, F.Id("j"), Rho, Open, F.Id("u"), Close, Close, Eq, F.Id("p"), Underscore, F.Id("j"), Plus, F.Id("u"), F.Id("v"),
        Underscore, F.Id("j"), Close, RowBreak, Amp, Longrightarrow, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J")), Frac, Grp(F.Id("v"),
        Underscore, F.Id("j"), Caret, D(2)), Grp(F.Id("p"), Underscore, F.Id("j")), Le, Operatorname, Grp(F.Id("spectralQFI")), Open, Rho, Open,
        D(0), Close, Comma, Rho, Apos, Open, D(0), Close, Close, End, Grp(F.Id("aligned"))));

    private static Formula AlternativeFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, Forall, Sp, F.Id("m"), InMacro, Mathbb, Sp, F.Id("N"), Comma, Esc, F.Id("N"), Colon, F.Id("J"),
        Underscore, F.Id("m"), To, Mathbb, Sp, F.Id("C"), Caret, Grp(D(2), Times, D(2)), Comma, Esc, Rho, Colon, Mathbb, Sp, F.Id("R"), To, Mathbb, Sp,
        F.Id("C"), Caret, Grp(D(2), Times, D(2)), Comma, Esc, F.Id("p"), Comma, F.Id("v"), Colon, F.Id("J"), Underscore, F.Id("m"), To, Mathbb, Sp,
        F.Id("R"), Comma, Esc, F.Id("I"), Subseteq, Mathbb, Sp, F.Id("R"), Comma, Esc, Ell, Comma, F.Id("h"), InMacro, Sp, F.Id("J"), Underscore,
        F.Id("m"), Comma, RowBreak, Amp, Operatorname, Grp(F.Id("Open")), Open, F.Id("I"), Close, Land, D(0), InMacro, Sp, F.Id("I"), Land, Sp,
        F.Id("v"), Neq, D(0), Land, Open, Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m"), Comma, D(0), Lt, F.Id("p"), Underscore,
        F.Id("j"), Close, Land, Open, Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m"), Comma, Operatorname, Grp(F.Id("PSD")), Open,
        F.Id("N"), Underscore, F.Id("j"), Close, Close, Land, Rho, InMacro, Sp, F.Id("C"), Caret, D(1), Open, F.Id("I"), Close, RowBreak, Amp, Land,
        Esc, Open, Forall, Sp, F.Id("u"), InMacro, Sp, F.Id("I"), Comma, Operatorname, Grp(F.Id("PSD")), Open, Rho, Open, F.Id("u"), Close, Close, Land,
        Operatorname, Grp(F.Id("tr")), Open, Rho, Open, F.Id("u"), Close, Close, Eq, D(1), Land, Rho, Open, F.Id("u"), Close, Caret, D(2), Eq,
        Rho, Open, F.Id("u"), Close, Close, RowBreak, Amp, Land, Esc, Open, Forall, Sp, F.Id("u"), InMacro, Sp, F.Id("I"), Comma, Forall, Sp, F.Id("j"),
        InMacro, Sp, F.Id("J"), Underscore, F.Id("m"), Comma, Operatorname, Grp(F.Id("Re")), Operatorname, Grp(F.Id("tr")), Open, F.Id("N"),
        Underscore, F.Id("j"), Rho, Open, F.Id("u"), Close, Close, Eq, F.Id("p"), Underscore, F.Id("j"), Plus, F.Id("u"), F.Id("v"), Underscore,
        F.Id("j"), Close, Land, Frac, Grp(F.Id("v"), Underscore, Ell), Grp(F.Id("p"), Underscore, Ell), Lt, D(0), Land, D(0), Lt, Frac,
        Grp(F.Id("v"), Underscore, F.Id("h")), Grp(F.Id("p"), Underscore, F.Id("h")), RowBreak, Amp, Longrightarrow, Operatorname,
        Grp(F.Id("rank")), Underscore, Grp(Mathbb, Sp, F.Id("R")), Open, Operatorname, Grp(F.Id("effectReadout")), Open, F.Id("N"), Close, Close, Eq,
        D(2), Esc, Lor, Esc, Minus, Frac, Grp(F.Id("v"), Underscore, Ell), Grp(F.Id("p"), Underscore, Ell), Frac, Grp(F.Id("v"), Underscore,
        F.Id("h")), Grp(F.Id("p"), Underscore, F.Id("h")), Le, Operatorname, Grp(F.Id("spectralQFI")), Open, Rho, Open, D(0), Close, Comma, Rho,
        Apos, Open, D(0), Close, Close, End, Grp(F.Id("aligned"))));
}
