using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class BiInfiniteBandDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula X(Formula k) => Seq(Id("x"), Open, k, Close);
    private static Formula AllK => Seq(Forall, Sp, Id("k"), InMacro, Sp, Mathbb, Grp(Id("Z")), Comma, Sp);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local scalar barriers and positive progress force a finite consecutive transition band over all integer times.",
        H("Bi-infinite Scalar Transition Bands"), Blocks(
        Paragraph(Text("Let x map the integers to the reals, and let a, b and eta be real numbers. Define B={k : a<x(k)<b}. "
            + "The predicate ScalarBandProgress(x,a,b,eta) consists of four local conditions: the lower cap is backward invariant; "
            + "the upper cap is forward invariant; a lower-cap value cannot jump directly to the upper cap; and every middle value advances by at least eta. "
            + "Explicitly, for every integer k these conditions are:")),
        Paragraph(Math(St(
            Seq(AllK, X(Seq(Id("k"), Plus, D(1))), Le, Sp, Id("a"), Rightarrow, Sp, X(Id("k")), Le, Sp, Id("a")),
            Seq(AllK, Id("b"), Le, Sp, X(Id("k")), Rightarrow, Sp, Id("b"), Le, Sp, X(Seq(Id("k"), Plus, D(1)))),
            Seq(AllK, X(Id("k")), Le, Sp, Id("a"), Rightarrow, Sp, X(Seq(Id("k"), Plus, D(1))), Lt, Id("b")),
            Seq(AllK, Id("a"), Lt, X(Id("k")), Land, Sp, X(Id("k")), Lt, Id("b"), Rightarrow, Sp,
                X(Id("k")), Plus, Id("eta"), Le, Sp, X(Seq(Id("k"), Plus, D(1))))))),
        Describe.Lean(DescribeId.Create("scalar-band-classification"),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/BiInfiniteBand.classify"),
            H("Finite band and the two cap alternatives"),
            StatementSource.FromAuthor(St(
                Seq(Id("x"), Colon, Mathbb, Grp(Id("Z")), To, Sp, Mathbb, Grp(Id("R")), Comma,
                    Sp, Id("a"), Comma, Id("b"), Comma, Id("eta"), InMacro, Sp, Mathbb, Grp(Id("R")), Comma,
                    Sp, Id("N"), InMacro, Sp, Mathbb, Grp(Id("N")), Comma),
                Seq(Id("ScalarBandProgress"), Open, Id("x"), Comma, Id("a"), Comma, Id("b"), Comma, Id("eta"), Close,
                    Land, Sp, D(0), Lt, Id("eta"), Land, Sp, Id("b"), Minus, Id("a"), Lt, Id("N"), Id("eta"), Rightarrow),
                Seq(Id("B"), Sp, Id("finite"), Land),
                Seq(Open, Par(Seq(AllK, X(Id("k")), Le, Sp, Id("a"))), Lor, Sp,
                    Par(Seq(AllK, Id("b"), Le, Sp, X(Id("k")))), Lor),
                Seq(Open, Exists, Sp, Id("l"), Comma, Id("r"), InMacro, Sp, Mathbb, Grp(Id("Z")), Comma,
                    Id("l"), Le, Sp, Id("r"), Land, Sp, Id("r"), Minus, Id("l"), Lt, Id("N"), Land),
                Seq(Id("B"), Eq, OpenBracket, Id("l"), Comma, Id("r"), CloseBracket, Land),
                Seq(Par(Seq(AllK, Id("k"), Lt, Id("l"), Rightarrow, Sp, X(Id("k")), Le, Sp, Id("a"))), Land, Sp,
                    Par(Seq(AllK, Id("r"), Lt, Id("k"), Rightarrow, Sp, Id("b"), Le, Sp, X(Id("k")))), Close, Close))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Here [l,r] denotes the integer interval. Between two markers, the backward lower barrier and forward upper barrier force every intervening time to remain marked. "
                + "Induction then gives x(i+n)>=x(i)+n eta throughout a marked block. Two marked endpoints differ in value by less than b-a, so their time difference is less than N. "
                + "Fixing one marker bounds all markers in a finite integer interval; its minimum and maximum give the exact block and the two cap tails. "
                + "If there is no marker, the no-jump condition propagates the lower cap forward as well as backward, so the entire sequence lies in one cap. "
                + "The statement makes no boundedness assumption on x outside the band and no assumption that the errors or transitions have finite support."))),
            DescribeRole.Theorem)
        )));
}
