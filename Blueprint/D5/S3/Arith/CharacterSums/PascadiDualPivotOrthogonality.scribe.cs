using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiDualPivotOrthogonalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CharacterSums/PascadiDualPivotOrthogonality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual unit cubic separates four-coordinate pivot spectra and gives an exact complete dual-frequency energy identity.",
        H("Exact Dual Orthogonality for the Fixed-Sum Cubic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pascadi-dual-spectral-reading-injective"),
                DeclarationHandle.Create(Prefix + "spectral_reading_injective"),
                H("The cubic removes the scaling ambiguity"),
                StatementSource.FromAuthor(Disp(F.Seq(
                    Call("CommRing", F.Id("R")), Comma, Sp, Call("IsUnit", F.Id("g")), Sp,
                    Implies, Sp, Call("InjOn", F.Id("spectralReading"), F.Id("AdmissiblePoint"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix any commutative ring R and parameters r,s,rho,sigma,g,h in R, with g a unit. "
                        + "For reduced pivot u=(alpha,beta), define a=r alpha+sigma beta and b=s alpha-rho beta. "
                        + "An admissible point z=(x,y) has a,b,x,y,h-x-y,x+y,h-x,h-y all units and satisfies "
                        + "g a b x y (h-x-y)=h. The spectral reading is (alpha x,alpha y,beta x,beta y). "
                        + "The theorem says that equality of these four readings for two admissible pivot-point "
                        + "pairs identifies both their reduced pivots and their points. It applies to composite rings, "
                        + "including ZMod(p^2), and uses no passage to a residue field.")),
                    Paragraph(Text(
                        "Extract a unit t=x/x' from equality of the first-coordinate readings. It gives "
                        + "u'=t u. The reconstructed physical a is a unit, so the other two readings give y=t y'. "
                        + "The two original cubic equations then imply P_h(z)=t^2 P_h(z'). Expanding this equality "
                        + "gives t^2 x' y' (x'+y') (t-1)=0. The first factor is a unit, hence t=1. "
                        + "This is the essential separation argument; separation is not assumed as an input. "
                        + "For the original integer resonance coordinates, r rho+s sigma=p and "
                        + "p alpha=rho a+sigma b, p beta=s a-r b recover exactly the physical pivot formulas above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pascadi-complete-dual-energy"),
                DeclarationHandle.Create(Prefix + "complete_dual_energy"),
                H("The full four-frequency average is exactly diagonal"),
                StatementSource.FromAuthor(EnergyStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be any nonzero natural modulus, fix g a unit, and retain any finite reduced-pivot "
                        + "set S. Write AdmissibleFibres(S,Z) for the requirement that every point of every Z(u), "
                        + "for u in S, satisfies the admissible cubic and all the unit conditions above. "
                        + "Each Z(u) is finite, and further point deletions are permitted. "
                        + "For arbitrary complex pivot coefficients c and masks chi, define "
                        + "K(u;w,n)=chi(u) sum_{z in Z(u)} e_q((alpha w+beta n) dot z). "
                        + "The sum over all w,n in (ZMod q)^2 of |sum_{u in S} c(u) K(u;w,n)|^2, "
                        + "divided by q^4, equals sum_{u in S} |c(u) chi(u)|^2 card(Z(u)). "
                        + "There is no bound or nonvanishing assumption on c or chi. In particular q may be p^2.")),
                    Paragraph(Text(
                        "The proof reuses Mathlib's orthogonality of finite additive characters. The four-coordinate "
                        + "reading embeds the actual pivot-point atoms into distinct characters, by the preceding "
                        + "unit-ring theorem. Expand the weighted square, sum the complete character Gram matrix, "
                        + "and retain exactly its diagonal. Reindexing the finite atoms by their pivot fibres gives "
                        + "the displayed cardinality factor. The normalization is the exact size q^4 of the full "
                        + "frequency group, rather than the size of a restricted frequency window.")),
                    Paragraph(Text(
                        "This is a project derivation for the Pascadi dual-direction kernel, with no literature "
                        + "novelty claim. The spectrum is unprojected and the averaging period is complete. "
                        + "Positivity permits restricting the unnormalized energy to a frequency subset, but the "
                        + "identity supplies no normalized concentration bound in a short literal frequency box. "
                        + "That local concentration problem and the unrestricted original count remain separate."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula EnergyStatement() => Disp(F.Seq(
        F.Id("q"), Neq, Sp, D(0), Sp, Land, Sp, Call("IsUnit", F.Id("g")), Sp, Land, Sp,
        Call("AdmissibleFibres", F.Id("S"), F.Id("Z")), Sp, Implies, Sp,
        Frac,
        Grp(Sum, Underscore, Grp(F.Id("f"), InMacro, Call("DualFrequency", F.Id("q"))), Sp,
            Vert, Sp, Sum, Underscore, Grp(F.Id("u"), InMacro, Sp, F.Id("S")), Sp,
            Call("c", F.Id("u")), Sp, Call("K", F.Id("u"), F.Id("f")), Sp, Vert, Caret, D(2)),
        Grp(F.Id("q"), Caret, D(4)), Eq,
        Sum, Underscore, Grp(F.Id("u"), InMacro, Sp, F.Id("S")), Sp,
        Vert, Sp, Call("c", F.Id("u")), Sp, Call("chi", F.Id("u")), Sp, Vert, Caret, D(2), Sp,
        Call("card", Call("Z", F.Id("u")))));
}
