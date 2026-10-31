using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class KBonacciFixedPaidRecordDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.";
    private static Formula Call(string name, params Formula[] args)
    {
        var xs = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int n = 0; n < args.Length; n++)
        {
            if (n > 0) xs.AddRange([Comma, Sp]);
            xs.Add(args[n]);
        }
        xs.Add(Close);
        return Seq([.. xs]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula K => F.Id("k");
    private static Formula Fin => Call("Fin",K);
    private static Formula Vec => new Formula.TypeArrow(Fin,R);
    private static Formula Matrix => Call("Matrix",Fin,Fin,R);
    private static Formula World => Call("World",K);
    private static Formula Arr => Call("Arrangement",K);
    private static Formula Rec => Seq(Arr,Sp,Times,Sp,Call("List",Seq(R,Sp,Times,Sp,Call("List",R))));
    private static Formula Bound(Formula body) => All("k",N,Seq(D(2),Sp,Leq,Sp,K,Sp,Implies,Sp,body));
    private static ScribeNode Def(string name, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("kbonacci-paid-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Root + name), H(name), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create()
    {
        Formula a = F.Id("A"), w = F.Id("w"), u = F.Id("u"), s = F.Id("s"), i = F.Id("i");
        Formula ell = F.Id("l"), x = F.Id("x"), run = F.Id("h"), decode = F.Id("f");
        Formula bits = Call("List",Call("Bool"));
        Formula win = Call("Window",K);
        Formula record = Call("paidRecord",a,w);
        Formula reads = Call("terminalReads",ell,x,run);
        Formula budget = Seq(K,Open,K,Minus,D(1),Close);
        Formula decoding = Seq(Exists,Sp,decode,Colon,Sp,new Formula.TypeArrow(Rec,Matrix),Comma,Sp,
            All("w",World,Eqn(Call("apply",decode,record),Call("target",w))));
        Formula statement = All("k",N,Seq(D(3),Sp,Leq,Sp,K,Sp,Implies,Sp,
            All("A",Arr,Seq(Call("windows",a),Sp,Eq,Sp,budget,Sp,Implies,Sp,
                Open,Open,decoding,Close,Sp,Iff,Sp,
                Eqn(Call("surviving",a),Call("offDiagonal",K)),Close))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Complete minimal-window endpoint-pattern classification for actual fixed acquisition and all paid readings.",
            H("KBonacci Fixed Paid Records"),Blocks(
            Paragraph(Text("For every k at least two, Fin k indexes the actual tail states. A preparation supplies the same unknown strictly positive real vector c, and all runs use the same unknown nonzero nonnegative reader l. The world and initial outer-product target are those of KBonacci Prefix Completion.")),
            Def("base",Bound(Seq(Eqn(Call("start",Call("base",K)),D(0)),Sp,Land,Sp,
                All("s",Fin,Seq(Eqn(Call("step",Call("base",K),s,Call("false")),Call("some",D(0))),
                    Sp,Land,Sp,Eqn(Call("step",Call("base",K),s,Call("true")),
                        Call("ite",Seq(s,Plus,D(1),Sp,Lt,Sp,K),Call("some",Seq(s,Plus,D(1))),Call("none"))))))),
                "A zero bit resets a live tail to zero. A one bit increases a tail s to s + 1 when that value is smaller than k and rejects otherwise. The initial tail is zero. Rejection is absorbing under word execution."),
            Def("live",Bound(All("u",bits,All("i",Fin,All("s",Fin,
                Eqn(Call("live",u,i,s),Call("ite",Eqn(Call("evalFrom",Call("base",K),s,u),Call("some",i)),D(1),D(0))))))),
                "The actual word transfer has entry one exactly when the automaton takes source tail s to target tail i; otherwise its entry is zero. A reader returning zero is unrelated to this automaton rejection test."),
            Def("Window",Bound(Eqn(win,Seq(OpenBrace,u,Colon,Sp,bits,Sp,Vert,Sp,
                Call("length",u),Sp,Eq,Sp,K,Plus,D(1),Sp,Land,Sp,
                Call("evalFrom",Call("base",K),D(0),u),Sp,Neq,Sp,Call("none"),CloseBrace))),
                "Every action is a literal binary word of length k + 1 that avoids the forbidden internal run of k ones. Legality is checked from tail zero and does not require that the word preserve the current object at a seam."),
            Def("Arrangement",Bound(Eqn(Arr,Call("List",Call("List",win)))),
                "The outer list is the finite ordered preparation sequence. Each inner list is the fixed finite sequence of actual windows on that object, followed by stopping and abandoning it. Empty and repeated runs are retained. There is no upper bound on the number of preparations and no dependence on read values."),
            Def("windows",Bound(All("A",Arr,Eqn(Call("windows",a),
                Seq(Sum,Underscore,Grp(Seq(run,Sp,InMacro,Sp,a)),Call("length",run))))),
                "Each window is counted once, even if it repeats a value, kills the object or acts on an already zero object. The preparation count is the outer-list length, and the total paid-reading count is that length plus windows(A)."),
            Def("terminalReads",Bound(All("l",Vec,All("x",Vec,All("h",Call("List",win),
                Seq(Eqn(Call("terminalReads",ell,x,Call("nil")),Call("nil")),Sp,Land,Sp,
                    All("u",win,Eqn(Call("terminalReads",ell,x,Call("cons",u,run)),
                        Call("cons",Call("dot",ell,Call("mulVec",Call("live",u),x)),
                            Call("terminalReads",ell,Call("mulVec",Call("live",u),x),run))))))))),
                "On each next window u, form y = live(u) x, append the compulsory scalar l dot y, and continue from y. The empty window sequence has no terminal readings. This recursion retains the killing-window reading and every subsequent paid zero."),
            Def("paidRecord",Bound(All("A",Arr,All("w",World,Eqn(record,
                Seq(Open,a,Comma,Sp,Call("map",Seq(run,Sp,Mapsto,Sp,Open,Call("initial",w),Comma,Sp,
                    Call("terminalReads",Call("ell",w),Call("c",w),run),Close),a),Close))))),
                "PaidRun(w) consists of the compulsory initial value sum c_i l_i and the terminalReads list starting from c. The literal arrangement is also part of the record, so the full ordered action and read history is retained. Each repeated initial value is still present and paid."),
            Def("label",Bound(All("u",bits,All("r",Fin,All("t",Fin,
                Seq(Eqn(Call("label",u),Call("some",Seq(Open,F.Id("r"),Comma,F.Id("t"),Close))),Sp,Iff,Sp,
                    Eqn(Call("live",u),Call("endpoint",Seq(K,Minus,D(1),Minus,F.Id("r")),F.Id("t")))))))),
                "When the actual cumulative word operator is a nonzero endpoint E(p,t), its label is (k - 1 - p,t), representing source prefix length j = k - p. Otherwise the label is none. Only nonempty window prefixes are used; their operator is either zero or such an endpoint by the actual endpoint theorem."),
            Def("surviving",Bound(All("A",Arr,All("q",Seq(Fin,Sp,Times,Sp,Fin),
                Seq(F.Id("q"),Sp,InMacro,Sp,Call("surviving",a),Sp,Iff,Sp,
                    Exists,Sp,u,Colon,Sp,bits,Comma,Sp,u,Sp,InMacro,Sp,
                    Call("flatMap",Call("wordPrefixes"),a),Sp,Land,Sp,
                    Eqn(Call("label",u),Call("some",F.Id("q"))))))),
                "Take every nonempty cumulative window prefix in every run in order, extract its actual endpoint label, discard none and then remove repetitions. A surviving object has the form C_j e_t with C_j strictly positive. Thus its label survives even when l_t = 0. Label selection depends only on the literal arrangement and object survival."),
            Describe.Lean(DescribeId.Create("kbonacci-complete-source-twelve-two"),
                DeclarationHandle.Create(Root + "complete_source_12_2"),
                H("The exact classification for every legal fixed arrangement"),
                StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The source set S0 consists of (j,t) with 1 <= j <= k, 0 <= t < k and j different from t + 1. The Lean row index is r = j - 1, so S0 is exactly offDiagonal(k). The theorem quantifies over every finite arrangement with exactly k(k - 1) windows, without assuming a correct decoder in the arrangement type.")),
                    Paragraph(Text("Actual sequential readings equal the readings of the literal cumulative words: word concatenation composes the actual transfer matrices in chronological order. Every long cumulative word either rejects every source tail or equals an endpoint. Consequently every terminal value is its surviving C_j l_t or a constant zero, and equality of full ordered records is equivalent to equality of the initial reading and the selected distinct prefix products.")),
                    Paragraph(Text("The number of distinct surviving labels is at most the number of paid windows. Necessity applies the whole-domain prefix-pattern classification to that set, including singleton and adjacent two-column support collisions. Sufficiency applies off-diagonal completion after extracting the already paid entries from their fixed record positions. Reordering only occurs inside final decoding.")),
                    Paragraph(Text("The factorization theorem extends a fiber-constant target to an arbitrary function on all record values, including values outside the attainable range. No continuity, measurability or computability condition is imposed. Positive objects and nonzero nonnegative readers inhabit the world type for every k in scope.")),
                    Paragraph(Text("The result identifies the initial outer product, not the absolute factors or the cumulative action operator. It does not classify a unique action order, run grouping or preparation count, and asserts no adaptive, noisy, finite-precision, physical-preparation or dimension-two extension."))),DescribeRole.Theorem))));
    }
}
