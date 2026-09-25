using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ActualPureQubitCostInfimumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ActualPureQubitCostInfimum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full finite affine-readout pure-qubit cost infimum has quadratic coefficient one quarter of the weighted score-square projection residual.",
        H("Actual pure-qubit cost infimum"),
        Blocks(
            Paragraph(Text("Let Jm be Fin m. For positive probabilities p summing to one and a centered nonzero real direction v, define the scores, their second moment B, and their third moment M3 by")),
            Paragraph(Math(Notation1Formula())),
            Paragraph(Text("The weighted squared residual after projecting the score square onto the span of the constant function and the score is")),
            Paragraph(Math(Notation3Formula())),
            Paragraph(Text("Here costs and C2 are the attainable cost set and its guarded real infimum from ActualPureQubitGeometry, with the full IsProgram predicate there. BddBelow(S) means that S has a real lower bound. IsGLB(S,c) means that c is a lower bound and every real lower bound is at most c:")),
            Paragraph(Math(Notation5Formula())),
            Paragraph(Text("All radii in the statement are real. The right limit is through every positive real radius tending to zero, and the three eventual properties hold together on one positive interval.")),
            Describe.Lean(DescribeId.Create("actual-qubit-infimum-expansion"),
                DeclarationHandle.Create(Module + "result"), H("Exact quadratic infimum coefficient"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary finite positive probability data, a nonzero centered direction, and at least three distinct scores, the residual is positive and the normalized infimum excess tends to one quarter of that residual as real positive radii tend to zero. Repeated and zero individual scores are allowed. Cubic approximate minimizers suffice; no optimum is assumed attained. This result makes no two-score attainment or unrestricted CPTP processor equivalence claim.")),
                    Paragraph(Text(
                        "The lower bound uses the joint limit of feasible rank-two coefficients: positivity, normalization, and the spectral cost equation exclude a positive limiting transverse parameter when three scores are distinct. The remaining diagonal coefficients converge to the normalized weighted score squares. An exact matching inequality then gives the quadratic lower coefficient. The rank-one branch has a fixed positive cost gap, and a smooth family of actual programs supplies the matching upper bound.")))))));

    private static Formula ResultFormula() =>
        Disp(Seq(Begin, Grp(F.Id("aligned")), Amp, Forall, Sp, F.Id("m"), InMacro, Mathbb, Sp, F.Id("N"), Comma, Esc, F.Id("p"), Comma, F.Id("v"), Colon,
        F.Id("J"), Underscore, F.Id("m"), To, Mathbb, Sp, F.Id("R"), Comma, RowBreak, Amp, Open, Forall, Sp, F.Id("j"), InMacro, Sp, F.Id("J"), Underscore,
        F.Id("m"), Comma, D(0), Lt, F.Id("p"), Underscore, F.Id("j"), Close, Land, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J"),
        Underscore, F.Id("m")), F.Id("p"), Underscore, F.Id("j"), Eq, D(1), Land, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J"), Underscore,
        F.Id("m")), F.Id("v"), Underscore, F.Id("j"), Eq, D(0), Land, Sp, F.Id("v"), Neq, D(0), RowBreak, Amp, Land, Esc, Open, Exists, Sp, F.Id("i"),
        Comma, F.Id("j"), Comma, F.Id("k"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m"), Comma, Esc, F.Id("s"), Underscore, F.Id("i"), Neq, Sp,
        F.Id("s"), Underscore, F.Id("j"), Land, Sp, F.Id("s"), Underscore, F.Id("i"), Neq, Sp, F.Id("s"), Underscore, F.Id("k"), Land, Sp, F.Id("s"),
        Underscore, F.Id("j"), Neq, Sp, F.Id("s"), Underscore, F.Id("k"), Close, RowBreak, Amp, Longrightarrow, Quad, D(0), Lt, F.Id("V"), RowBreak,
        Amp, Land, Esc, Open, Exists, DeltaLower, Gt, D(0), Comma, Forall, Sp, F.Id("R"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Esc, D(0), Lt,
        F.Id("R"), Lt, DeltaLower, Longrightarrow, RowBreak, Amp, Qquad, Operatorname, Grp(F.Id("costs")), Open, F.Id("p"), Comma, F.Id("v"),
        Comma, F.Id("R"), Close, Neq, Emptyset, Land, Operatorname, Grp(F.Id("BddBelow")), Open, Operatorname, Grp(F.Id("costs")), Open,
        F.Id("p"), Comma, F.Id("v"), Comma, F.Id("R"), Close, Close, Land, Operatorname, Grp(F.Id("IsGLB")), Open, Operatorname,
        Grp(F.Id("costs")), Open, F.Id("p"), Comma, F.Id("v"), Comma, F.Id("R"), Close, Comma, F.Id("C"), Underscore, D(2), Open, F.Id("p"),
        Comma, F.Id("v"), Comma, F.Id("R"), Close, Close, Close, RowBreak, Amp, Land, Lim, Underscore, Grp(F.Id("R"), To, D(0), Caret, Plus),
        Frac, Grp(F.Id("C"), Underscore, D(2), Open, F.Id("p"), Comma, F.Id("v"), Comma, F.Id("R"), Close, Minus, F.Id("B")), Grp(F.Id("R"),
        Caret, D(2)), Eq, Frac, Sp, F.Id("V"), D(4), End, Grp(F.Id("aligned"))));

    private static Formula Notation1Formula() =>
        Disp(Seq(F.Id("s"), Underscore, F.Id("j"), Eq, Frac, Grp(F.Id("v"), Underscore, F.Id("j")), Grp(F.Id("p"), Underscore, F.Id("j")), Comma,
        Quad, Sp, F.Id("B"), Eq, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m")), F.Id("p"), Underscore, F.Id("j"),
        F.Id("s"), Underscore, F.Id("j"), Caret, D(2), Eq, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m")), Frac,
        Grp(F.Id("v"), Underscore, F.Id("j"), Caret, D(2)), Grp(F.Id("p"), Underscore, F.Id("j")), Comma, Quad, Sp, F.Id("M"), Underscore, D(3), Eq,
        Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m")), F.Id("p"), Underscore, F.Id("j"), F.Id("s"), Underscore,
        F.Id("j"), Caret, D(3), Dot));

    private static Formula Notation3Formula() =>
        Disp(Seq(F.Id("V"), Eq, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J"), Underscore, F.Id("m")), F.Id("p"), Underscore, F.Id("j"),
        Left, Open, F.Id("s"), Underscore, F.Id("j"), Caret, D(2), Minus, F.Id("B"), Minus, Frac, Grp(F.Id("M"), Underscore, D(3)),
        Grp(F.Id("B")), F.Id("s"), Underscore, F.Id("j"), Right, Close, Caret, D(2), Eq, Sum, Underscore, Grp(F.Id("j"), InMacro, Sp, F.Id("J"),
        Underscore, F.Id("m")), F.Id("p"), Underscore, F.Id("j"), F.Id("s"), Underscore, F.Id("j"), Caret, D(4), Minus, F.Id("B"), Caret, D(2),
        Minus, Frac, Grp(F.Id("M"), Underscore, D(3), Caret, D(2)), Grp(F.Id("B")), Dot));

    private static Formula Notation5Formula() =>
        Disp(Seq(Operatorname, Grp(F.Id("BddBelow")), Open, F.Id("S"), Close, Esc, Leftrightarrow, Esc, Exists, Sp, F.Id("b"), InMacro, Mathbb, Sp,
        F.Id("R"), Comma, Forall, Sp, F.Id("q"), InMacro, Sp, F.Id("S"), Comma, F.Id("b"), Le, Sp, F.Id("q"), Comma, Qquad, Operatorname, Grp(F.Id("IsGLB")),
        Open, F.Id("S"), Comma, F.Id("c"), Close, Esc, Leftrightarrow, Esc, Open, Forall, Sp, F.Id("q"), InMacro, Sp, F.Id("S"), Comma, F.Id("c"), Le, Sp,
        F.Id("q"), Close, Land, Open, Forall, Sp, F.Id("b"), InMacro, Mathbb, Sp, F.Id("R"), Comma, Open, Forall, Sp, F.Id("q"), InMacro, Sp, F.Id("S"), Comma,
        F.Id("b"), Le, Sp, F.Id("q"), Close, Rightarrow, Sp, F.Id("b"), Le, Sp, F.Id("c"), Close, Dot));
}
