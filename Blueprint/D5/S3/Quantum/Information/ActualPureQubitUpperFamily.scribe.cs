using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ActualPureQubitUpperFamilyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ActualPureQubitUpperFamily.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized positive effect matrices and pure-state arcs give a matching upper family.",
        H("Actual pure-qubit upper family"),
        Blocks(
            Paragraph(Text("J is an arbitrary finite outcome index set and Jm is Fin m. All scalars and radius parameters are real. PSD means positive semidefinite, the qubit identity is the two-by-two identity matrix, and P(R) denotes the set of subsets of the real line. The following moment notation is used with the outcome set of each statement; eR is shorthand after the function t has been chosen.")),
            Paragraph(Math(Notation1Formula())),
            Paragraph(Text("root, effect, radiusMap, extendedCost and IsProgram are exactly the functions and full program predicate in ActualPureQubitGeometry. In particular IsProgram includes the canonical density-state realization, positive exact complex Born probabilities, and equality to the spectral cost at zero. The vector written as the square root of B times d is the function taking j to that scalar multiple of d at j. Both limits below are through all positive real radii tending to zero.")),
            Describe.Lean(DescribeId.Create("actual-effect-family"),
                DeclarationHandle.Create(Module + "actual_effect_family"), H("Normalized positive effect family"),
                StatementSource.FromAuthor(EffectsFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same functions w and t satisfy the initial values, the moment limit, normalization of the small roots and effects, the radius equation, and every strict margin in the displayed conjunction.")))),
            Describe.Lean(DescribeId.Create("actual-upper-family"),
                DeclarationHandle.Create(Module + "actual_upper_family"), H("Matching family of actual programs"),
                StatementSource.FromAuthor(ProgramsFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The functions N, rho, I and Q give actual programs simultaneously for every sufficiently small positive radius, with direction equal to the square root of B times d and the displayed cost limit.")))))));

    private static Formula EffectsFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, Forall, Sp, F.Id("J"), Esc, Mathrm, Grp(F.Id("finite")), Comma, Esc, F.Id("p"), Comma, F.Id("d"),
        Colon, F.Id("J"), To, Mathbb, Sp, F.Id("R"), Comma, Esc, F.Id("B"), InMacro, Mathbb, Sp, F.Id("R"), Comma, RowBreak, Amp, Open, Forall, Sp,
        F.Id("j"), InMacro, Sp, F.Id("J"), Comma, D(0), Lt, F.Id("p"), Underscore, F.Id("j"), Close, Land, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp,
        F.Id("J")), F.Id("p"), Underscore, F.Id("j"), Eq, D(1), Land, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J")), F.Id("d"), Underscore,
        F.Id("j"), Eq, D(0), Land, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J")), Frac, Grp(F.Id("d"), Underscore, F.Id("j"), Caret, D(2)),
        Grp(F.Id("p"), Underscore, F.Id("j")), Eq, D(1), Land, D(0), Lt, F.Id("B"), RowBreak, Amp, Longrightarrow, Exists, Sp, F.Id("w"), Comma,
        F.Id("t"), Colon, Mathbb, Sp, F.Id("R"), To, Mathbb, Sp, F.Id("R"), Comma, Esc, F.Id("w"), Open, D(0), Close, Eq, D(1), Land, Sp, F.Id("t"), Open,
        D(0), Close, Eq, D(0), RowBreak, Amp, Land, Lim, Underscore, Grp(F.Id("R"), To, D(0), Caret, Plus), Frac, Grp(Operatorname,
        Grp(F.Id("extendedCost")), Open, F.Id("B"), Comma, Alpha, Comma, F.Id("w"), Close, Open, F.Id("t"), Open, F.Id("R"), Close, Caret, D(2),
        Close, Minus, F.Id("B")), Grp(F.Id("R"), Caret, D(2)), Eq, Frac, Grp(F.Id("B"), Caret, D(2)), Grp(D(4)), Open, Mu, Underscore, D(4),
        Minus, D(1), Minus, Mu, Underscore, D(3), Caret, D(2), Close, RowBreak, Amp, Land, Exists, DeltaLower, Gt, D(0), Comma, Forall, Sp,
        F.Id("R"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Esc, D(0), Lt, F.Id("R"), Lt, DeltaLower, Longrightarrow, RowBreak, Amp, Open, D(0), Lt,
        F.Id("R"), Land, D(0), Lt, F.Id("t"), Open, F.Id("R"), Close, Land, Sp, F.Id("t"), Open, F.Id("R"), Close, Lt, D(1), Land, D(0), Lt,
        F.Id("w"), Open, F.Id("e"), Underscore, F.Id("R"), Close, RowBreak, Amp, Land, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J")),
        Operatorname, Grp(F.Id("root")), Open, F.Id("p"), Underscore, F.Id("j"), Comma, F.Id("d"), Underscore, F.Id("j"), Comma, Alpha, Comma,
        F.Id("e"), Underscore, F.Id("R"), Comma, F.Id("w"), Open, F.Id("e"), Underscore, F.Id("R"), Close, Close, Eq, D(1), RowBreak, Amp, Land,
        Esc, Open, Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Comma, Operatorname, Grp(F.Id("PSD")), Open, Operatorname, Grp(F.Id("effect")), Open,
        F.Id("p"), Underscore, F.Id("j"), Comma, F.Id("d"), Underscore, F.Id("j"), Comma, Alpha, Comma, F.Id("e"), Underscore, F.Id("R"), Comma,
        F.Id("w"), Open, F.Id("e"), Underscore, F.Id("R"), Close, Close, Close, Close, RowBreak, Amp, Land, Sum, Underscore, Grp(F.Id("j"),
        InMacro, Sp, F.Id("J")), Operatorname, Grp(F.Id("effect")), Open, F.Id("p"), Underscore, F.Id("j"), Comma, F.Id("d"), Underscore, F.Id("j"),
        Comma, Alpha, Comma, F.Id("e"), Underscore, F.Id("R"), Comma, F.Id("w"), Open, F.Id("e"), Underscore, F.Id("R"), Close, Close, Eq, D(1),
        Underscore, D(2), Land, Operatorname, Grp(F.Id("radiusMap")), Open, F.Id("B"), Comma, Alpha, Comma, F.Id("w"), Close, Open, F.Id("t"),
        Open, F.Id("R"), Close, Close, Eq, F.Id("R"), RowBreak, Amp, Land, Esc, Open, Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Comma, Esc, D(0),
        Lt, F.Id("p"), Underscore, F.Id("j"), Minus, Alpha, Sp, F.Id("e"), Underscore, F.Id("R"), F.Id("w"), Open, F.Id("e"), Underscore, F.Id("R"),
        Close, F.Id("d"), Underscore, F.Id("j"), Land, D(0), Lt, Open, F.Id("p"), Underscore, F.Id("j"), Minus, Alpha, Sp, F.Id("e"), Underscore,
        F.Id("R"), F.Id("w"), Open, F.Id("e"), Underscore, F.Id("R"), Close, F.Id("d"), Underscore, F.Id("j"), Close, Caret, D(2), Minus, D(4),
        F.Id("e"), Underscore, F.Id("R"), Open, D(1), Minus, F.Id("e"), Underscore, F.Id("R"), Close, F.Id("w"), Open, F.Id("e"), Underscore,
        F.Id("R"), Close, Caret, D(2), F.Id("d"), Underscore, F.Id("j"), Caret, D(2), Close, RowBreak, Amp, Land, Esc, Open, Forall, Sp, F.Id("j"),
        InMacro, Sp, F.Id("J"), Comma, Esc, F.Id("R"), Open, D(1), Plus, F.Id("t"), Open, F.Id("R"), Close, Close, Bar, Sqrt, Sp, F.Id("B"), F.Id("d"),
        Underscore, F.Id("j"), Bar, Lt, F.Id("p"), Underscore, F.Id("j"), Close, Close, End, Grp(F.Id("aligned"))));

    private static Formula ProgramsFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, Forall, Sp, F.Id("m"), InMacro, Mathbb, Sp, F.Id("N"), Comma, Esc, F.Id("p"), Comma, F.Id("d"), Colon,
        F.Id("J"), Underscore, F.Id("m"), To, Mathbb, Sp, F.Id("R"), Comma, Esc, F.Id("B"), InMacro, Mathbb, Sp, F.Id("R"), Comma, RowBreak, Amp, Open,
        Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m"), Comma, D(0), Lt, F.Id("p"), Underscore, F.Id("j"), Close, Land, Sum,
        Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m")), F.Id("p"), Underscore, F.Id("j"), Eq, D(1), Land, Sum, Underscore,
        Grp(F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m")), F.Id("d"), Underscore, F.Id("j"), Eq, D(0), Land, Sum, Underscore,
        Grp(F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m")), Frac, Grp(F.Id("d"), Underscore, F.Id("j"), Caret, D(2)), Grp(F.Id("p"),
        Underscore, F.Id("j")), Eq, D(1), Land, D(0), Lt, F.Id("B"), RowBreak, Amp, Longrightarrow, Exists, Sp, F.Id("N"), Colon, Mathbb, Sp, F.Id("R"),
        To, Open, F.Id("J"), Underscore, F.Id("m"), To, Mathbb, Sp, F.Id("C"), Caret, Grp(D(2), Times, D(2)), Close, Comma, Esc, Rho, Colon, Mathbb, Sp,
        F.Id("R"), To, Open, Mathbb, Sp, F.Id("R"), To, Mathbb, Sp, F.Id("C"), Caret, Grp(D(2), Times, D(2)), Close, Comma, Esc, F.Id("I"), Colon,
        Mathbb, Sp, F.Id("R"), To, Mathcal, Sp, F.Id("P"), Open, Mathbb, Sp, F.Id("R"), Close, Comma, Esc, F.Id("Q"), Colon, Mathbb, Sp, F.Id("R"), To, Mathbb, Sp,
        F.Id("R"), Comma, RowBreak, Amp, Lim, Underscore, Grp(F.Id("R"), To, D(0), Caret, Plus), Frac, Grp(F.Id("Q"), Open, F.Id("R"), Close,
        Minus, F.Id("B")), Grp(F.Id("R"), Caret, D(2)), Eq, Frac, Grp(F.Id("B"), Caret, D(2)), Grp(D(4)), Open, Mu, Underscore, D(4), Minus,
        D(1), Minus, Mu, Underscore, D(3), Caret, D(2), Close, RowBreak, Amp, Land, Esc, Open, Exists, DeltaLower, Gt, D(0), Comma, Forall, Sp,
        F.Id("R"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Esc, D(0), Lt, F.Id("R"), Lt, DeltaLower, Longrightarrow, Operatorname,
        Grp(F.Id("IsProgram")), Open, F.Id("p"), Comma, Sqrt, Sp, F.Id("B"), F.Id("d"), Comma, F.Id("R"), Comma, F.Id("N"), Open, F.Id("R"), Close,
        Comma, Rho, Open, F.Id("R"), Close, Comma, F.Id("I"), Open, F.Id("R"), Close, Comma, F.Id("Q"), Open, F.Id("R"), Close, Close, Close,
        End, Grp(F.Id("aligned"))));

    private static Formula Notation1Formula() =>
        Disp(Seq(Mu, Underscore, D(3), Eq, Sum, Underscore, F.Id("j"), Frac, Grp(F.Id("d"), Underscore, F.Id("j"), Caret, D(3)), Grp(F.Id("p"),
        Underscore, F.Id("j"), Caret, D(2)), Comma, Quad, Mu, Underscore, D(4), Eq, Sum, Underscore, F.Id("j"), Frac, Grp(F.Id("d"), Underscore,
        F.Id("j"), Caret, D(4)), Grp(F.Id("p"), Underscore, F.Id("j"), Caret, D(3)), Comma, Quad, Alpha, Eq, Minus, D(2), Mu, Underscore, D(3),
        Comma, Quad, Sp, F.Id("e"), Underscore, F.Id("R"), Eq, F.Id("t"), Open, F.Id("R"), Close, Caret, D(2)));
}
