using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class RationalIntervalMarkersDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula X(Formula k) => Seq(Id("x"), Open, k, Close);
    private static Formula Fr(int n, int d) => Seq(Frac, Grp(Num(n)), Grp(Num(d)));
    private static Formula AllK => Seq(Forall, Sp, Id("k"), InMacro, Sp, Mathbb, Grp(Id("Z")), Comma, Sp);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed-error rational interval pseudo-orbits have a finite middle block of at most three consecutive integer times, with strict boundary behavior.",
        H("Rational Interval Markers"), Blocks(
        Paragraph(Text("Let I=[0,1], f(u)=2u/(1+u), and x:Z->I. The predicate ClosedRationalPseudoOrbit(delta,x) means "
            + "|f(x(k))-x(k+1)|<=delta for every integer k. Both interval endpoints and equality in the error bound are included. "
            + "Write B={k : 1/3<x(k)<2/3}. The domain follows the closed, bi-infinite pseudo-orbit convention in Alfonso Artigue, Shadowing maps, arXiv:2504.00171v1, Section 2.1. "
            + "The marker estimates below concern this rational interval map; they are not attributed to that paper.")),
        Describe.Lean(DescribeId.Create("rational-interval-markers"),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/RationalIntervalMarkers.rational_interval_marker_classification"),
            H("Three consecutive markers and strict cap boundaries"),
            StatementSource.FromAuthor(St(
                Seq(Id("x"), Colon, Mathbb, Grp(Id("Z")), To, Sp, OpenBracket, D(0), Comma, D(1), CloseBracket, Comma,
                    Sp, Delta, InMacro, Sp, Mathbb, Grp(Id("R")), Comma, Sp, Delta, Le, Sp, Fr(1,256), Comma),
                Seq(Par(Seq(AllK, Bar, Frac, Grp(D(2), X(Id("k"))), Grp(D(1), Plus, X(Id("k"))),
                    Minus, X(Seq(Id("k"), Plus, D(1))), Bar, Le, Sp, Delta)), Rightarrow),
                Seq(Id("B"), Sp, Id("finite"), Land, Sp, Id("ncard"), Open, Id("B"), Close, Le, Sp, D(3), Land),
                Seq(Open, Par(Seq(AllK, X(Id("k")), Lt, Fr(1,3))), Lor, Sp,
                    Par(Seq(AllK, Fr(2,3), Lt, X(Id("k")))), Lor),
                Seq(Open, Exists, Sp, Id("l"), Comma, Id("r"), InMacro, Sp, Mathbb, Grp(Id("Z")), Comma,
                    Id("l"), Le, Sp, Id("r"), Land, Sp, Id("r"), Minus, Id("l"), Le, Sp, D(2), Land),
                Seq(Id("B"), Eq, OpenBracket, Id("l"), Comma, Id("r"), CloseBracket, Land),
                Seq(Par(Seq(AllK, Id("k"), Lt, Id("l"), Rightarrow, Sp, X(Id("k")), Le, Sp, Fr(1,3))), Land, Sp,
                    Par(Seq(AllK, Id("r"), Lt, Id("k"), Rightarrow, Sp, Fr(2,3), Le, Sp, X(Id("k")))), Close, Close, Land),
                Seq(Par(Seq(AllK, X(Id("k")), Eq, Fr(1,3), Rightarrow, Sp, Id("k"), Plus, D(1), InMacro, Sp, Id("B"))), Land),
                Par(Seq(AllK, X(Id("k")), Eq, Fr(2,3), Rightarrow, Sp, Id("k"), Minus, D(1), InMacro, Sp, Id("B"))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/artigue2025shadowing")),
            Blocks(Paragraph(Text("The interval [l,r] in the conclusion is an integer interval. The final two universal implications hold in every alternative. "
                + "Since a pseudo-orbit exists, the error parameter is automatically nonnegative. The only supplied scale assumption is delta<=1/256. "
                + "Exact rational inequalities give: u>=1/3 implies v>1/3; u>=2/3 implies v>2/3; and u<=1/3 implies v<2/3 for every admitted step u to v. "
                + "On the closed band, the factorization 15u(1-u)-2(1+u)=(2/3-u)(15u-3)>=0 gives f(u)-u>=2/15. "
                + "Thus v-u>=2/15-delta>1/8. Applying ScalarBandProgress.classify with eta=1/8 and N=3 gives r-l<3, hence at most three markers. "
                + "At u=1/3 the next value is inside the band. At a value 2/3, its predecessor can lie in neither cap and is therefore marked. "
                + "These implications make both cap alternatives strict at every time. "
                + "The theorem supplies finite marker sums and their local index bounds. It establishes no continuous selector, shadowing-map property, or converse counterexample."))),
            DescribeRole.Theorem)
        )));
}
