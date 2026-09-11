using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hilbert;

internal sealed class NymanHalflineZeroSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Hilbert/NymanHalflineZeroSeparation.";
    private static Formula Rho => F.Rho;
    private static Formula Beta => F.Beta;
    private static Formula J => Seq(F.Id("J"), Underscore, Grp(Rho));
    private static Formula Chi => Seq(Mathrm, Grp(F.Id("chi")));
    private static Formula M => F.Id("M");
    private static Formula C => Seq(F.Id("C"), Underscore, Grp(Mathrm, Grp(F.Id("real"))));
    private static Formula Sq(Formula x) => Seq(Grp(x), Caret, Grp(D(2)));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert);
    private static Formula Energy => Seq(Frac, Grp(D(1)), Grp(D(2), Beta, Minus, D(1)),
        Plus, Frac, Grp(D(1)), Grp(Sq(Norm(Seq(Rho, Minus, D(1))))));
    private static Formula Bound => Seq(Frac, Grp(D(1)), Grp(Sq(Norm(Rho)), Open, Energy, Close));
    private static Formula Middle => Seq(Frac,
        Grp(Open, D(2), Beta, Minus, D(1), Close, Sq(Norm(Seq(Rho, Minus, D(1))))),
        Grp(Norm(Rho), Caret, Grp(D(4))));
    private static Formula Radius => Norm(Seq(D(1), Minus, Frac, Grp(D(1)), Grp(Rho)));
    private static Formula RadiusBound => Seq(Sq(Radius), Open, D(1), Minus, Sq(Radius), Close);
    private static Formula Dn => Seq(F.Id("d"), Underscore, Grp(F.Id("N")));
    private static Formula Distance(Formula space) => Seq(Operatorname, Grp(F.Id("infDist")),
        Open, Chi, Comma, space, Close);
    private static Formula Shell => Seq(F.Id("S"), Underscore, Grp(F.Id("N")));
    private static Formula Bind => Seq(Forall, Sp, Rho, InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma,
        Operatorname, Grp(F.Id("IsNontrivialZero")), Open, Rho, Close, Comma,
        Beta, Eq, Re, Sp, Rho, Gt, Sp, Frac, Grp(D(1)), Grp(D(2)), Comma, Sp);
    private static Formula Annihilates(Formula space) => Seq(Forall, Sp, F.Id("f"), InMacro, Sp, space, Comma, J, Open, F.Id("f"), Close, Eq, D(0));

    private static DocumentBlock.Describe Claim(string id, string name, string title,
        Formula formula, string explanation, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An off-critical zeta zero separates the target from both half-line source closures.",
        H("Half-Line Zero Separation"), Blocks(
            Paragraph(Text("H is the existing complex L2 space on (0,infinity), chi is the "
                + "indicator of (0,1), and F_a is the real-parameter fractional-reciprocal source. "
                + "The canonical predicate Zeta23.IsNontrivialZero(rho) means zeta(rho)=0 and "
                + "0<Re(rho)<1. Below beta=Re(rho)>1/2. These are conditional statements; "
                + "they do not assert the existence of such a zero.")),
            Paragraph(Text("S_N is the original natural shell, including S_0={0}, and d_N is "
                + "the existing infimum distance from chi to S_N. M is the original cumulative "
                + "natural closed space, the closure of the union of these shells. C_real is "
                + "defined separately as the closure of the complex span of every F_a with real "
                + "a at least one. No equality of M and C_real is assumed.")),
            Claim("halfline-separator-target", "halflineFunctional_target", "Target evaluation",
                Seq(Forall, Sp, Rho, InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma,
                    Re, Sp, Rho, Gt, Sp, Frac, Grp(D(1)), Grp(D(2)), Comma, Rho, Neq, D(1), Comma,
                    J, Open, Chi, Close, Eq, Frac, Grp(D(1)), Grp(Rho)),
                "The target's tail integral vanishes. Its integral over (0,1) is the elementary "
                    + "complex power integral 1/rho. This evaluation does not require a zeta zero."),
            Claim("halfline-separator-real-source", "halflineFunctional_realSource", "All real sources vanish",
                Seq(Bind, Forall, Sp, F.Id("a"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma,
                    F.Id("a"), Ge, Sp, D(1), Comma, J, Open, F.Id("F"), Underscore, Grp(F.Id("a")), Close, Eq, D(0)),
                "E9 at theta=1/a gives the near-zero integral. The source equals 1/(a*x) "
                    + "beyond one, so its integral after division by x is 1/a. At the stipulated "
                    + "zero, the two contributions cancel exactly, including a=1."),
            Claim("halfline-separator-shell", "halflineFunctional_shell", "Every finite shell vanishes",
                Seq(Bind, Forall, Sp, F.Id("N"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Annihilates(Shell)),
                "Linearity and equality with the natural source vectors annihilate the span "
                    + "for every N, including zero. No Gram inverse or rank premise occurs."),
            Claim("halfline-separator-natural-closure", "halflineFunctional_M", "Natural closed space vanishes",
                Seq(Bind, Annihilates(M)),
                "The kernel of J is closed and contains every shell. It therefore contains "
                    + "their union and its closure, which is the existing space M."),
            Claim("halfline-full-real-closure", "fullRealClosure", "Full real source closure",
                Seq(C, Eq, Overline, Grp(Operatorname, Grp(F.Id("span")), Underscore,
                    Grp(Mathbb, Grp(F.Id("C"))), OpenBrace, F.Id("F"), Underscore, Grp(F.Id("a")),
                    Colon, F.Id("a"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, F.Id("a"), Ge, Sp, D(1), CloseBrace)),
                "C_real is a closed complex submodule of H formed from all real parameters. "
                    + "It is not defined by the natural cumulative family.", DescribeRole.Definition),
            Claim("halfline-separator-real-closure", "halflineFunctional_fullRealClosure", "Full real closure vanishes",
                Seq(Bind, Annihilates(C)),
                "All real sources lie in the closed kernel, hence so do their complex span "
                    + "and its topological closure."),
            Claim("halfline-finite-distance-bound", "nyman_halfline_distance_bound", "Finite distance bound",
                Seq(Bind, Forall, Sp, F.Id("N"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Bound, Le, Sp, Sq(Dn)),
                "For every f in S_N, J(chi-f)=1/rho. The operator norm inequality and the "
                    + "exact norm formula bound each distance, hence the infimum distance. "
                    + "The positive energy ensures division is valid."),
            Claim("halfline-natural-distance-bound", "nyman_halfline_closed_distance_bound", "Natural closure distance bound",
                Seq(Bind, Bound, Le, Sp, Sq(Distance(M))),
                "The same separation argument applies to M, using its annihilation by J."),
            Claim("halfline-real-distance-bound", "nyman_halfline_real_closed_distance_bound", "Full real closure distance bound",
                Seq(Bind, Bound, Le, Sp, Sq(Distance(C))),
                "The same separation argument applies to the full real source closure. "
                    + "Neither closed-space bound assumes the two spaces coincide."),
            Claim("halfline-radius-chain", "nyman_halfline_radius_chain", "Exact original radius chain",
                Seq(Bind, Bound, Eq, Middle, Eq, RadiusBound, Gt, Sp, D(0)),
                "The original radius is r=norm(1-1/rho). The norm-square identity "
                    + "norm(rho-1)^2=norm(rho)^2-(2*beta-1) gives both equalities. "
                    + "The canonical zero hypotheses imply rho differs from zero and one, "
                    + "while beta>1/2 supplies the remaining positive factor."),
            Claim("halfline-literal-e11", "nyman_halfline_e11", "Complete conditional E11",
                Seq(Bind, Begin, Grp(F.Id("gathered")),
                    Open, Forall, Sp, F.Id("N"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
                    Bound, Le, Sp, Sq(Dn), Close, RowBreak,
                    Land, Sp, Bound, Le, Sp, Sq(Distance(M)), RowBreak,
                    Land, Sp, Bound, Le, Sp, Sq(Distance(C)), RowBreak,
                    Land, Sp, Bound, Eq, Middle, Eq, RadiusBound, Gt, Sp, D(0),
                    End, Grp(F.Id("gathered"))),
                "This combines the original finite-distance bound for every natural N, "
                    + "both separately defined closed-space bounds, and the full positive "
                    + "radius chain at Zeta23.IsNontrivialZero. The constructed complex-linear "
                    + "functional and its representative formula provide the separating witness."))));
}
