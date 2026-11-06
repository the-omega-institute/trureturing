using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class BirkhoffSharpContractionDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, V(name), Sp, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Open, a, Close, Sp, Rightarrow, Sp, Open, b, Close);
    private static Formula Both(Formula a, Formula b) =>
        Seq(Open, a, Close, Sp, Land, Sp, Open, b, Close);
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula AtMost(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula P(Formula x) => Call("Positive", x);
    private static Formula Dst(Formula x, Formula y) => Call("distance", x, y);
    private static Formula Act(Formula x) => Call("mulVec", V("A"), x);
    private static Formula Th => Call("theta", V("A"));
    private static Formula K => Call("kappa", V("A"));
    private static Formula S => Call("imageDistances", V("A"));
    private static Formula C => Call("coefficients", V("A"));
    private static Formula Vec(string type) => Arr(V(type), R);
    private static Formula Entry(Formula i, Formula j) => Call("entry", V("A"), i, j);
    private static Formula Context(Formula body) =>
        All("I", Call("Type"), All("J", Call("Type"),
            Seq(OpenBracket, Call("Fintype", V("I")), CloseBracket, Sp,
                OpenBracket, Call("Fintype", V("J")), CloseBracket, Sp,
                OpenBracket, Call("Nonempty", V("I")), CloseBracket, Sp,
                OpenBracket, Call("Nonempty", V("J")), CloseBracket, Sp,
                All("A", Call("Matrix", V("I"), V("J"), R), body))));
    private static Formula PositiveMatrix => All("i", V("I"), All("j", V("J"),
        Less(D(0), Entry(V("i"), V("j")))));
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Open, V(name), Sp, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Root(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula Indexed(Formula op, Formula bound, Formula value) =>
        Seq(op, Underscore, Grp(bound), Sp, value);
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula DistanceDefinition =>
        All("K", Call("Type"), Seq(OpenBracket, Call("Fintype", V("K")), CloseBracket, Sp,
            OpenBracket, Call("Nonempty", V("K")), CloseBracket, Sp,
            All("x", Vec("K"), All("y", Vec("K"), Equal(Dst(V("x"), V("y")),
                Call("log", Fraction(
                    Indexed(Max, Member(V("k"), V("K")), Fraction(Call("x", V("k")), Call("y", V("k")))),
                    Indexed(Min, Member(V("k"), V("K")), Fraction(Call("x", V("k")), Call("y", V("k")))))))))));
    private static Formula ThetaDefinition => Context(Equal(Th,
        Indexed(Max, Seq(V("i"), Comma, V("k"), InMacro, V("I"), Semi,
                V("j"), Comma, V("l"), InMacro, V("J")),
            Fraction(Product(Entry(V("i"), V("j")), Entry(V("k"), V("l"))),
                Product(Entry(V("i"), V("l")), Entry(V("k"), V("j")))))));
    private static Formula KappaDefinition => Context(Equal(K,
        Fraction(Seq(Root(Th), Minus, D(1)), Seq(Root(Th), Plus, D(1)))));
    private static Formula ImageDefinition => Context(All("r", R,
        Seq(Member(V("r"), S), Sp, Iff, Sp,
            ExistsIn("x", Vec("J"), ExistsIn("y", Vec("J"),
                Both(P(V("x")), Both(P(V("y")), Equal(Dst(Act(V("x")), Act(V("y"))), V("r")))))))));
    private static Formula CoefficientDefinition => Context(All("c", R,
        Seq(Member(V("c"), C), Sp, Iff, Sp, Both(AtMost(D(0), V("c")),
            All("x", Vec("J"), All("y", Vec("J"),
                Imp(P(V("x")), Imp(P(V("y")), AtMost(Dst(Act(V("x")), Act(V("y"))),
                    Product(V("c"), Dst(V("x"), V("y"))))))))))));
    private static Formula Contract => Context(Imp(PositiveMatrix,
        Both(All("x", Vec("J"), Imp(P(V("x")), P(Act(V("x"))))),
            Both(Call("IsLUB", S, Call("log", Th)),
                Both(Equal(Call("sSup", S), Call("log", Th)),
                    Both(Call("IsLeast", C, K),
                        Both(AtMost(D(0), K), Less(K, D(1)))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive finite rectangular matrix has exact Hilbert image diameter log Theta "
            + "and least nonnegative contraction coefficient (sqrt Theta-1)/(sqrt Theta+1).",
        H("Sharp rectangular Birkhoff contraction"),
        Blocks(
            Paragraph(Text("The row and column types are finite and nonempty and live in independent universes. "
                + "The notation entry(A,i,j) means the real matrix entry A(i,j), and mulVec is the finite matrix-vector sum. "
                + "Positive means strict positivity in every coordinate. All inputs below belong to this intrinsic positive domain.")),
            Paragraph(Math(Disp(All("K", Call("Type"), All("x", Arr(V("K"), R),
                Seq(P(V("x")), Sp, Iff, Sp, All("k", V("K"), Less(D(0), Call("x", V("k")))))))))),
            Paragraph(Text("For a finite nonempty coordinate type, distance is log of the maximum coordinate ratio divided by the minimum. "
                + "Theta is the maximum over all two rows and two columns of A(i,j) A(k,l)/(A(i,l) A(k,j)). "
                + "The diagonal minors show Theta is at least one. Kappa is (sqrt Theta-1)/(sqrt Theta+1).")),
            Paragraph(Math(Disp(DistanceDefinition))),
            Paragraph(Math(Disp(ThetaDefinition))),
            Paragraph(Math(Disp(KappaDefinition))),
            Paragraph(Text("imageDistances(A) consists of distance(Ax,Ay) for all strictly positive x and y. "
                + "coefficients(A) consists of all real c at least zero such that distance(Ax,Ay) is at most c times distance(x,y) "
                + "for every such pair. IsLUB asserts both the upper bound and its leastness; IsLeast asserts membership and minimality.")),
            Paragraph(Math(Disp(ImageDefinition))),
            Paragraph(Math(Disp(CoefficientDefinition))),
            Describe.Lean(DescribeId.Create("sharp-rectangular-contraction"),
                DeclarationHandle.Create("D5/S3/Analytic/Convexity/BirkhoffSharpContraction.sharp_contraction"),
                H("Exact image diameter and least contraction coefficient"),
                StatementSource.FromAuthor(Disp(Contract)),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/eveson1995birkhoff")),
                Blocks(
                    Paragraph(Text("The entrywise maximal cross ratio bounds the cross ratio of the images of two nonnegative residual vectors, "
                        + "by multiplying each minor inequality by the two coordinate weights and summing. "
                        + "For minimum and maximum input ratios m and M, the residuals x-m y and M y-x are nonnegative. "
                        + "If m equals M, the pair is proportional. Otherwise both residual images are positive and the scalar two-dimensional "
                        + "Birkhoff inequality gives the factor kappa. Taking the extremal output row pair gives the upper estimate.")),
                    Paragraph(Text("For the diameter lower bound, take a minor attaining Theta. "
                        + "The vectors e(j)+eta times the all-ones vector and e(l)+eta times the all-ones vector are strictly positive for eta positive. "
                        + "Their selected output row contrast tends to log Theta as eta tends to zero from above. "
                        + "Thus every number strictly below log Theta is exceeded by an actual positive image distance.")),
                    Paragraph(Text("For coefficient leastness, a smaller nonnegative c forces Theta greater than one and distinct maximizing columns j and l. "
                        + "Put L=sqrt Theta and q=A(i,l)L/A(i,j). Choose t positive with c t below log((1+L exp(t))/(L+exp(t))); "
                        + "the derivative at zero of this curve is kappa. The vector w(eta,t) has coordinate q exp(t) at j, one at l, and eta elsewhere. "
                        + "The pair w(eta,t), w(eta,0) has input distance exactly t for every positive eta. "
                        + "For this fixed t its selected output row contrast tends to that scalar curve as eta tends to zero. "
                        + "Choosing eta afterwards defeats c.")),
                    Paragraph(Text("Singleton types, rank-one matrices, Theta equal to one, and proportional input pairs are included. "
                        + "The diameter and coefficient are supremal and leastness statements; they need not be attained by a distinct positive pair. "
                        + "No square shape, common universe, rank, invertibility, stochasticity or normalization assumption is used. "
                        + "Empty coordinate types and zero input coordinates are outside the asserted domain.")),
                    Paragraph(Text("The result is classical. Eveson and Nussbaum give the scalar sharpness and rectangular diameter formulas. "
                        + "The consumed upper estimates adapt TauCetiProject/TauCeti revision afa08a3ed16fb167e35de371afb1eb03fbc5913a under Apache-2.0; "
                        + "the complete license is docs/reports/licenses/tauceti-birkhoff/LICENSE.txt. "
                        + "The adaptation uses finite max/min distance and the direct square-root coefficient. "
                        + "Replace these adapted estimates by direct applications when equivalent declarations are supplied by the host's pinned library."))),
                DescribeRole.Theorem))));
}
