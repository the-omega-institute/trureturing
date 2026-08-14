using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.MetricGeometry;

internal sealed class GreenClassDiameterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Green class has exact prefix-metric diameter set by its first unpinned coordinate.",
        H("Exact Diameter and Optimal Supports for Green Classes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("green-class-diameter"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/MetricGeometry/GreenClassDiameter.green_class_diameter"),
                H("The first hole determines the exact Green-class diameter"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("diam")), Open,
                    F.Id("G"), Open, F.Id("S"), Comma, Sp, F.Id("t"), Close, Close,
                    Sp, Eq, Sp,
                    Frac, Grp(D(1)), Grp(D(2)), Caret,
                    Grp(Operatorname, Grp(F.Id("firstHole")), Open, F.Id("S"), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let O be a nontrivial alphabet with the discrete topology, and equip infinite "
                        + "strings N -> O with Mathlib's PiNat prefix metric. For a finite support S and "
                        + "target t, the Green class G(S,t) consists of all strings agreeing with t on S. "
                        + "Its diameter is exactly (1/2)^firstHole(S), where firstHole(S) is the least "
                        + "coordinate outside S.")),
                    Paragraph(Text(
                        "For the upper bound, two members of the class cannot first differ below the first "
                        + "hole: every smaller coordinate lies in S and is pinned to t. The PiNat distance "
                        + "formula and the strict decrease of (1/2)^n then bound every pairwise distance by "
                        + "(1/2)^firstHole(S).")),
                    Paragraph(Text(
                        "For the lower bound, nontriviality supplies a symbol distinct from t at the first "
                        + "hole. Updating t only at that coordinate gives another member of G(S,t), and the "
                        + "two witnesses first differ exactly there. Their distance attains the upper bound, "
                        + "so the diameter equality is sharp; this is why nontriviality is load-bearing."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prefix-support-minimizes-diameter"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/MetricGeometry/GreenClassDiameter.prefix_support_minimizes_diameter"),
                H("Prefix supports uniquely minimize diameter at fixed budget"),
                StatementSource.FromAuthor(Disp(Seq(
                    Frac, Grp(D(1)), Grp(D(2)), Caret,
                    Grp(Operatorname, Grp(F.Id("card")), Open, F.Id("S"), Close),
                    Sp, Le, Sp,
                    Operatorname, Grp(F.Id("diam")), Open,
                    F.Id("G"), Open, F.Id("S"), Comma, Sp, F.Id("t"), Close, Close,
                    Sp, Land, Sp, Open,
                    Operatorname, Grp(F.Id("diam")), Open,
                    F.Id("G"), Open, F.Id("S"), Comma, Sp, F.Id("t"), Close, Close,
                    Sp, Eq, Sp,
                    Frac, Grp(D(1)), Grp(D(2)), Caret,
                    Grp(Operatorname, Grp(F.Id("card")), Open, F.Id("S"), Close),
                    Sp, Iff, Sp,
                    F.Id("S"), Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("range")), Open,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("S"), Close, Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every support S, firstHole(S) is at most card(S). Since powers of one half "
                        + "strictly decrease with their natural exponent, the exact diameter formula turns "
                        + "this combinatorial inequality into the lower bound (1/2)^card(S) <= diam G(S,t).")),
                    Paragraph(Text(
                        "Equality of the diameters forces equality of the exponents. The frozen first-hole "
                        + "characterization says firstHole(S) = card(S) exactly when S is the initial segment "
                        + "range(card(S)); conversely that prefix support has its first hole at card(S). "
                        + "Thus prefix supports are the unique diameter minimizers at a fixed support budget."))),
                DescribeRole.Theorem))));
}
