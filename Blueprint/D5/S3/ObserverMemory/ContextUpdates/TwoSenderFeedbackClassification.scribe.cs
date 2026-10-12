using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.ContextUpdates;

internal sealed class TwoSenderFeedbackClassificationDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/ObserverMemory/ContextUpdates/TwoSenderFeedbackClassification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One binary broadcast classifies two simultaneous binary replies on the complete modulo-four source.",
        H("Two-Sender Feedback Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-source-correspondence"),
                DeclarationHandle.Create(Module + "sourceEquiv"),
                H("The original source and its kernel-valued clock offset"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write Z4 = ZMod 4 and Z2 = ZMod 2. The characteristic chi is reduction modulo two. "
                    + "The source (a,u,v,h) in Z4 cubed times Z2 corresponds bijectively to "
                    + "((a,[u,v]),2h) in the generic Source with two labelled senders and offset in ker chi. "
                    + "The inverse reads the two sender coordinates and returns h=0 for offset zero, "
                    + "h=1 for offset two. The generic target is Y=a+u+v and its clock is t=Y+2h."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("two-sender-feedback-classification"),
                DeclarationHandle.Create(Module + "result"),
                H("All exact protocols have one shared affine parameter family"),
                StatementSource.FromAuthor(ClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "P has an arbitrary deterministic query q(a,t) and two arbitrary deterministic "
                        + "binary reply maps e(u,t,b) and f(v,t,b), indexed zero and one in Protocol. "
                        + "Const(Bool) is the constant Boolean reply-type family. The receiver broadcasts "
                        + "b=q(a,t) before the two replies are sent simultaneously. Each reply depends only "
                        + "on its sender coordinate, the clock and the broadcast. D is any deterministic "
                        + "decoder on (a,t,b,r,s). Source coordinates remain fixed during this exchange.")),
                    Paragraph(Text(
                        "L(x) and H(x) are the low and high bits of the standard representative of x. "
                        + "xor denotes Boolean exclusive-or, mul denotes Boolean multiplication, and bit "
                        + "embeds false as zero and true as one in Z4. All additions in the decoder formula "
                        + "take place in Z4. Correct(P,D) requires D to return Y for every original source. "
                        + "Actual(P,a,t,b,r,s) means some source has receiver a, clock t, broadcast b "
                        + "and the two indicated replies.")),
                    Paragraph(Text(
                        "The displayed existential binds one c and one family A,B,cTwo,cThree for all "
                        + "inputs at once. The two reply equations hold for every local input, including "
                        + "both broadcasts. The decoder equation is imposed only when Actual holds. "
                        + "Both broadcast labels occur at every clock, and all four reply pairs occur "
                        + "at every receiver and clock. Consequently the actual image consists exactly "
                        + "of b=q(a,t) with arbitrary r and s; the decoder is unrestricted elsewhere.")),
                    Paragraph(
                        Text("Exact recovery on the reachable parity fibre and separation within "
                            + "each characteristic fibre follow from "),
                        Ref("D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification."
                            + "branch_exact_of_decoder"),
                        Text(" and "),
                        Ref("D5/S3/ObserverMemory/ContextUpdates/ExactSnapshotCollisionClassification."
                            + "fiber_separated_of_branch_exact"),
                        Text(". Boolean separation gives the affine forms of the local replies.")),
                    Paragraph(Text(
                        "For each prescribed reply pair, choose the high bits separately at both low-bit "
                        + "assignments. These two sources have the same observation. Their decoded totals "
                        + "must agree, forcing the coefficient relation. One broadcast branch therefore "
                        + "cannot serve different parities of t-a. Both parities exist and there are only "
                        + "two broadcast labels, so q(a,t)=xor(L(t-a),q(t,t)). Set c(t)=q(t,t) and read "
                        + "the reply constants and slopes at inputs zero and one in branch xor(p,c(t)). "
                        + "This same choice gives all the displayed equations and reachability claims.")),
                    Paragraph(Text(
                        "Conversely the coefficient relation cancels the low-bit term in the sum of "
                        + "the two reconstructed coordinates. The imposed decoder value then equals "
                        + "a+u+v for each source. This argument uses no restriction on the decoder "
                        + "outside the actual image."))),
                DescribeRole.Theorem))));

    private static Formula ClassificationFormula()
    {
        Formula z = Call("ZMod", D(4));
        Formula boolean = F.Id("Bool");
        Formula protocol = Call("Protocol", z, Call("Fin", D(2)), boolean, Call("Const", boolean));
        Formula decoder = Arrow(z, Arrow(z, Arrow(boolean, Arrow(boolean, Arrow(boolean, z)))));
        Formula family = Arrow(z, Arrow(boolean, boolean));
        Formula P = F.Id("P");
        Formula Dvalue = F.Id("D");
        Formula c = F.Id("c");
        Formula A = F.Id("A");
        Formula B = F.Id("B");
        Formula cTwo = F.Id("cTwo");
        Formula cThree = F.Id("cThree");
        Formula a = F.Id("a");
        Formula t = F.Id("t");
        Formula p = F.Id("p");
        Formula b = F.Id("b");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula r = F.Id("r");
        Formula s = F.Id("s");
        Formula parity = Call("xor", b, Apply(c, t));
        Formula query = Call("query", P, a, t);
        Formula actual = Call("Actual", P, a, t, b, r, s);
        Formula queryClause = All([Bound("a", z), Bound("t", z)],
            Equal(query, Call("xor", Call("low", Seq(t, Sp, Minus, Sp, a)), Apply(c, t))));
        Formula coefficientClause = All([Bound("t", z), Bound("p", boolean)],
            Equal(Call("xor", Apply(A, t, p), Apply(B, t, p)), Call("xor", F.Id("true"), p)));
        Formula firstReply = All([Bound("t", z), Bound("b", boolean), Bound("u", z)],
            Equal(Call("reply", P, D(0), u, t, b),
                Call("xor", Call("xor", Call("high", u),
                    Call("mul", Apply(A, t, parity), Call("low", u))), Apply(cTwo, t, parity))));
        Formula secondReply = All([Bound("t", z), Bound("b", boolean), Bound("v", z)],
            Equal(Call("reply", P, D(1), v, t, b),
                Call("xor", Call("xor", Call("high", v),
                    Call("mul", Apply(B, t, parity), Call("low", v))), Apply(cThree, t, parity))));
        Formula decodedBit = Call("xor",
            Call("xor", Call("xor", Call("xor", r, s), Apply(cTwo, t, parity)),
                Apply(cThree, t, parity)), Call("mul", Apply(B, t, parity), parity));
        Formula decoderValue = Seq(a, Sp, Plus, Sp, Call("bit", parity), Sp, Plus, Sp,
            D(2), Sp, Cdot, Sp, Call("bit", decodedBit));
        Formula decoderClause = All(
            [Bound("a", z), Bound("t", z), Bound("b", boolean), Bound("r", boolean), Bound("s", boolean)],
            new Formula.Logic(actual, FormulaLogicOperator.Implies,
                Equal(Apply(Dvalue, a, t, b, r, s), decoderValue)));
        Formula broadcastClause = All([Bound("t", z), Bound("b", boolean)],
            Some([Bound("a", z), Bound("r", boolean), Bound("s", boolean)], actual));
        Formula replyClause = All(
            [Bound("a", z), Bound("t", z), Bound("r", boolean), Bound("s", boolean)],
            Call("Actual", P, a, t, query, r, s));
        Formula normal = And(queryClause, coefficientClause, firstReply, secondReply, decoderClause);
        Formula classified = Some(
            [Bound("c", Arrow(z, boolean)), Bound("A", family), Bound("B", family),
                Bound("cTwo", family), Bound("cThree", family)],
            And(normal, broadcastClause, replyClause));
        return Disp(All([Bound("P", protocol), Bound("D", decoder)],
            new Formula.Logic(Call("Correct", P, Dvalue), FormulaLogicOperator.Iff, classified)));
    }

    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(params Formula[] clauses) => clauses.Aggregate(
        (left, right) => new Formula.Logic(left, FormulaLogicOperator.And, right));
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(IReadOnlyList<Formula.BoundVariable> variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Some(IReadOnlyList<Formula.BoundVariable> variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
