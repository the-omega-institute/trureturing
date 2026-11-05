using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class ConnectedExclusionCalibrationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurements/ConnectedExclusionCalibration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One zero seed calibrates the same response on every finite connected exclusion graph.",
        H("Connected exclusion response calibration"),
        Blocks(
            Entry("record-family", "IsRecordFamily", "Original configuration family", FamilyFormula(),
                "The finite vertex type and finite family retain the empty configuration and every singleton. Every allowed output is independent in the same graph.", DescribeRole.Definition),
            Entry("original-marginal", "marginal", "Original bit marginal", MarginalFormula(),
                "Both arguments of T range over the same original family S. The first argument is the reported output and the second is the source; the sum never renames either configuration.", DescribeRole.Definition),
            Entry("response-laws", "ResponseLaws", "Same-response hypotheses", LawsFormula(),
                "The columns are nonnegative and sum to one. A bit marginal depends only on whether that same bit occurs in the source. Support compatibility is the one-sided implication from a zero off-source marginal to a unit on-source marginal.", DescribeRole.Definition),
            Entry("connected-response-calibration", "connected_response_calibration", "Whole original R5-002 Theorem 5.1", TheoremFormula(),
                "The statement is Theorem 5.1 of AURIC_R5_002_THREE_PHASE_COMPARISON_INTERNAL_RECORDS_AND_QUANTUM_AXIOMS, with the finite independent-set family represented by a Finset of Finsets. Connected includes a nonempty vertex type. No nontriviality, extra neighbor or per-vertex seed is assumed; a connected singleton is included.", DescribeRole.Theorem),
            Paragraph(Text("For adjacent vertices i and j, independence of every output gives p(i,s)+p(j,s) at most one for the original column s. In the singleton source {i}, a(i)=0 and support compatibility force p(i,{i})=1. The other marginal is a(j), while the empty source proves its nonnegativity. Hence a(j)=0. A walk from the one seed propagates this calibration to every vertex.")),
            Paragraph(Text("A positive transition must preserve every bit: if an output has a bit absent from its source, its mass is bounded by the now-zero marginal; if it lacks a source bit, its mass is bounded by the now-zero complementary marginal. Extensionality of the original finite configurations eliminates every wrong outcome. Normalization gives mass one to the unchanged source name.")),
            Paragraph(Text("Mathlib supplies SimpleGraph.IsIndepSet, connected reachability, walk elimination and finite nonnegative-sum bounds. The graph-wide calibration and support-rigidity argument supplies the additional relation. This unit asserts no supply of physical zero seeds or gate orbits, no disconnected-graph conclusion, and no Hilbert reconstruction or Theorem 5.2/5.3 endpoint.")))));

    private static DocumentBlock.Describe Entry(string id, string declaration, string title, Formula formula,
        string text, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static Formula V => F.Id("V");
    private static Formula G => F.Id("G");
    private static Formula S => F.Id("S");
    private static Formula T => F.Id("T");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula K => F.Id("k");
    private static Formula Source => F.Id("s");
    private static Formula Output => F.Id("t");
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Family => Call("Finset", Call("Finset", V));
    private static Formula Zero => D(0);
    private static Formula One => D(1);
    private static Formula BaseBinders => Seq(Forall, Sp, Typed(V, Op("Type")), Comma, Sp,
        Instance("Fintype", V), Comma, Sp, Instance("DecidableEq", V), Comma, Sp);
    private static Formula ResponseBinders => Seq(BaseBinders,
        Typed(S, Family), Comma, Sp, Typed(T, Arrow(S, Arrow(S, Reals))), Comma, Sp,
        Typed(A, Arrow(V, Reals)), Comma, Sp, Typed(B, Arrow(V, Reals)), Comma, Sp);
    private static Formula Mass => Apply(T, Output, Source);
    private static Formula Marginal => Call("marginal", S, T, K, Source);
    private static Formula HasBit(Formula record) => Seq(K, Sp, InMacro, Sp, record);
    private static Formula Quantified(Formula vars, Formula body) => Seq(Forall, Sp, vars, Comma, Sp, body);
    private static Formula PairVariables => Seq(Typed(Output, S), Comma, Sp, Typed(Source, S));
    private static Formula Binary => Seq(Marginal, Sp, Eq, Sp,
        Choice(HasBit(Source), Apply(B, K), Apply(A, K)));
    private static Formula Compatible => Quantified(Typed(K, V),
        Seq(Apply(A, K), Sp, Eq, Sp, Zero, Sp, Rightarrow, Sp, Apply(B, K), Sp, Eq, Sp, One));

    private static Formula FamilyFormula() => Disp(Seq(BaseBinders,
        Typed(G, Call("SimpleGraph", V)), Comma, Sp, Typed(S, Family), Comma, Sp,
        Call("IsRecordFamily", G, S), Sp, Iff, Sp,
        Open, Emptyset, Sp, InMacro, Sp, S, Sp, Land, Sp,
        Open, Quantified(Typed(K, V), Seq(OpenBrace, K, CloseBrace, Sp, InMacro, Sp, S)), Close,
        Sp, Land, Sp, Open,
        Quantified(Typed(Output, Call("Finset", V)), Seq(Output, Sp, InMacro, Sp, S, Sp, Rightarrow, Sp,
            Call("IsIndepSet", G, Output))), Close, Close, Dot));

    private static Formula MarginalFormula() => Disp(Seq(BaseBinders,
        Typed(S, Family), Comma, Sp, Typed(T, Arrow(S, Arrow(S, Reals))), Comma, Sp,
        Typed(K, V), Comma, Sp, Typed(Source, S), Comma, Sp,
        Marginal, Sp, Eq, Sp, Sum, Underscore, Grp(Typed(Output, S)), Sp,
        Choice(HasBit(Output), Mass, Zero), Dot));

    private static Formula LawsFormula() => Disp(Seq(ResponseBinders,
        Call("ResponseLaws", S, T, A, B), Sp, Iff, Sp,
        Open, Quantified(PairVariables, Seq(Zero, Sp, Leq, Sp, Mass)), Close, Sp, Land, Sp,
        Open, Quantified(Typed(Source, S), Seq(Sum, Underscore, Grp(Typed(Output, S)), Sp, Mass,
            Sp, Eq, Sp, One)), Close, Sp, Land, Sp,
        Open, Quantified(Seq(Typed(K, V), Comma, Sp, Typed(Source, S)), Binary), Close,
        Sp, Land, Sp, Open, Compatible, Close, Dot));

    private static Formula TheoremFormula() => Disp(Seq(BaseBinders,
        Typed(G, Call("SimpleGraph", V)), Comma, Sp, Typed(S, Family), Comma, Sp,
        Typed(T, Arrow(S, Arrow(S, Reals))), Comma, Sp,
        Typed(A, Arrow(V, Reals)), Comma, Sp, Typed(B, Arrow(V, Reals)), Comma, Sp,
        Open, Call("IsRecordFamily", G, S), Sp, Land, Sp, Call("ResponseLaws", S, T, A, B),
        Sp, Land, Sp, Call("Connected", G), Sp, Land, Sp,
        Open, Exists, Sp, Typed(K, V), Comma, Sp, Apply(A, K), Sp, Eq, Sp, Zero, Close, Close,
        Sp, Rightarrow, Sp,
        Open, Quantified(Typed(K, V), Seq(Apply(A, K), Sp, Eq, Sp, Zero, Sp, Land, Sp,
            Apply(B, K), Sp, Eq, Sp, One)), Close,
        Sp, Land, Sp, Open, Quantified(PairVariables, Seq(Mass, Sp, Eq, Sp,
            Choice(Seq(Output, Sp, Eq, Sp, Source), One, Zero))), Close, Dot));

    private static Formula Choice(Formula condition, Formula yes, Formula no) => Seq(
        Op("if"), Sp, condition, Sp, Op("then"), Sp, yes, Sp, Op("else"), Sp, no);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Arrow(Formula source, Formula target) => Seq(source, Sp, To, Sp, target);
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Instance(string name, Formula value) => Seq(OpenBracket, Call(name, value), CloseBracket);
    private static Formula Apply(Formula function, params Formula[] args)
    {
        var items = new List<Formula> { function, Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Call(string name, params Formula[] args) => Apply(Op(name), args);
}
