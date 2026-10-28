using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class ReturnDistanceSubshiftDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/ReturnDistanceSubshift.";
    private static Formula Id(string s) => F.Id(s);
    private static Formula Z => Seq(Mathbb, Grp(Id("Z")));
    private static Formula SetZ => Call("Set", Z);
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), Colon, Sp, t, Comma);
    private static Formula Hyp(Formula a) => Seq(a, Sp, Rightarrow, Sp);
    private static Formula Call(string s, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(Id(s))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static DocumentBlock.Describe Thm(string key, string decl, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(key), DeclarationHandle.Create(Owner + decl), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual compact two-sided binary return-distance subshift and its ordinary finite-word language.",
        H("Return-Distance Subshifts and Exact-Length QFT"), Blocks(
        Paragraph(Text("The alphabet is the two-element subtype of the natural numbers {0,1}, with the inherited discrete metric. "
            + "Configurations have all integer coordinates. ReturnLegal(D,x) requires the difference q-p to belong to D for every consecutive pair of one coordinates. "
            + "Finite supports obey the same return-distance restriction; singleton supports and the all-zero configuration are always legal. "
            + "The set is closed because the assertion that fixed p,q are consecutive ones is a finite clopen cylinder condition. "
            + "All integer shifts preserve the rule. The bundled object is Mathlib FullShift.Subshift; ReturnPoint is its carrier subtype. "
            + "Mathlib PiCountable.metricSpace supplies a metric with the product uniformity, and closedness in the compact finite-alphabet product gives compactness.")),
        Thm("closed-return-configurations", "return_legal_closed", "A closed condition on the actual product", St(
            All("D", SetZ), Call("IsClosed", Call("carrier", Call("returnDistanceSubshift", Id("D"))))),
            "Every forbidden consecutive-pair condition depends only on the finite integer interval between its endpoints. "
            + "The complement of each such cylinder is closed, and the legal set is their intersection."),
        Paragraph(Text("ReturnWordOccurs(w,x,t) means x(t+j)=w[j] for every j smaller than the length of w. "
            + "ReturnLanguage(D,w) means that w occurs at some integer coordinate of an actual ReturnPoint(D), with no bound or one-sided restriction on that point. "
            + "ReturnQuasiFiniteType(D) is the original Definition 3.5: one M works for every n at least M and every pair of language words u,v; "
            + "if there is a language word w of length exactly n with uw and wv in the language, there is a language word z of length exactly n with uzv in the language. "
            + "This definition does not use a bounded-length replacement or another quasi-finite-type convention.")),
        Thm("forbidden-interval-obstruction", "forbidden_intervals_not_quasi_finite_type", "Long forbidden intervals rule out exact-length QFT", St(
            All("D", SetZ),
            Hyp(Seq(Open, All("n", Nat), Exists, Sp, Id("H"), Colon, Sp, Nat, Comma,
                All("d", Nat), Hyp(Seq(Id("H"), Sp, Lt, Sp, Id("d"))),
                Hyp(Seq(Id("d"), Sp, Le, Sp, Id("H"), Plus, Id("n"), Plus, D(1))),
                Neg, Sp, Open, Call("int", Id("d")), Sp, InMacro, Sp, Id("D"), Close, Close)),
            Seq(Neg, Sp, Call("ReturnQuasiFiniteType", Id("D")))),
            "For a proposed threshold M choose n=max(M,1) and an interval (H,H+n+1] containing no allowed return. "
            + "Take u to be one followed by H zeros, w to be n zeros, and v to be one. Singleton-support configurations prove actual occurrence of u,v,w,uw,wv. "
            + "In any putative occurrence of uzv with length(z)=n, the terminal v guarantees a next one after the initial one. "
            + "The least positive return lies strictly above H and at most H+n+1. Its consecutive-pair legality contradicts the forbidden interval. "
            + "The first-return argument uses the least natural positive index, preserving all intervening coordinates." )
        )));

}
