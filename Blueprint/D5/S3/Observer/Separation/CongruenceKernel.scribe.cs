using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class CongruenceKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-iterate pullback of an equivalence is its maximal forward congruence.",
        H("Congruence Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tau-congruence"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/CongruenceKernel.TauCongruence"),
                H("A tau-congruence is preserved by one forward update"),
                StatementSource.FromAuthor(TauCongruenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A state relation S is a congruence for tau exactly when membership of an "
                        + "ordered pair (y,y') in S implies membership of the updated pair "
                        + "(tau(y),tau(y'))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("congruence-kernel"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/CongruenceKernel.congruenceKernel"),
                H("The congruence kernel pulls a relation back along every iterate"),
                StatementSource.FromAuthor(CongruenceKernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The congruence kernel of R under tau consists exactly of those state "
                        + "pairs whose two coordinates remain R-related after every natural "
                        + "iterate of tau, including the zeroth iterate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("all-iterate-pullback-is-maximal-forward-congruence"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/CongruenceKernel."
                        + "congruence_kernel_laws"),
                H("Maximal forward congruence inside an equivalence"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an update tau and an equivalence R, define C_tau(R) by requiring "
                            + "that every iterate of tau sends a pair into R. The first six "
                            + "conjuncts establish equivalence, forward congruence, contraction, "
                            + "monotonicity, idempotence, and maximality.")),
                    Paragraph(Text(
                        "The final conjunct gives the equivalent universal characterization: "
                            + "a forward-congruent relation lies inside R exactly when it lies "
                            + "inside the all-iterate kernel."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TauCongruenceFormula()
    {
        Formula state = F.Id("Y");
        Formula update = Tau;
        Formula relation = F.Id("S");
        Formula left = F.Id("y");
        Formula right = F.Id("yprime");
        Formula relationType = Call("StateRelation", state);
        Formula pair = Call("pair", left, right);
        Formula updatedPair = Call("pair", Apply(update, left), Apply(update, right));

        return Disp(Seq(
            Forall, Sp, state, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            update, Colon, Sp, new Formula.TypeArrow(state, state), Comma, Sp,
            relation, Colon, Sp, relationType, Comma, RowBreak, Grp(),
            Call("TauCongruence", update, relation), Sp, Iff, Sp,
            Forall, Sp, left, Comma, Sp, right, Colon, Sp, state, Comma, Sp,
            pair, Sp, InMacro, Sp, relation, Sp, Rightarrow, Sp,
            updatedPair, Sp, InMacro, Sp, relation, Dot));
    }

    private static Formula CongruenceKernelFormula()
    {
        Formula state = F.Id("Y");
        Formula update = Tau;
        Formula relation = F.Id("R");
        Formula pair = F.Id("pair");
        Formula time = F.Id("k");
        Formula relationType = Call("StateRelation", state);
        Formula left = Call("fst", pair);
        Formula right = Call("snd", pair);
        Formula iteratedPair = Call(
            "pair",
            Call("iterate", update, time, left),
            Call("iterate", update, time, right));
        Formula set = Seq(
            OpenBrace, pair, Colon, Sp, Seq(state, Sp, Times, Sp, state), Sp, Mid, Sp,
            Forall, Sp, time, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            iteratedPair, Sp, InMacro, Sp, relation, CloseBrace);

        return Disp(Seq(
            Forall, Sp, state, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            update, Colon, Sp, new Formula.TypeArrow(state, state), Comma, Sp,
            relation, Colon, Sp, relationType, Comma, RowBreak, Grp(),
            Call("congruenceKernel", update, relation), Sp, Eq, Sp, set, Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("Y");
        Formula relation = F.Id("R");
        Formula update = Tau;
        Formula other = F.Id("S");
        Formula relationType = Call("StateRelation", state);
        Formula kernel = Seq(F.Id("C"), Underscore, Grp(update));
        Formula kernelAt = Apply(kernel, relation);
        Formula kernelAtOther = Apply(kernel, other);

        Formula equivalence = Call("Equivalence", kernelAt);
        Formula congruence = Call("TauCongruence", update, kernelAt);
        Formula contraction = Seq(kernelAt, Sp, Subseteq, Sp, relation);
        Formula monotone = Seq(
            Forall, Sp, other, Colon, Sp, relationType, Comma, Sp,
            other, Sp, Subseteq, Sp, relation, Sp, Rightarrow, Sp,
            kernelAtOther, Sp, Subseteq, Sp, kernelAt);
        Formula idempotent = Seq(Apply(kernel, kernelAt), Sp, Eq, Sp, kernelAt);
        Formula maximal = Seq(
            Forall, Sp, other, Colon, Sp, relationType, Comma, Sp,
            Call("TauCongruence", update, other), Sp, Rightarrow, Sp,
            other, Sp, Subseteq, Sp, relation, Sp, Rightarrow, Sp,
            other, Sp, Subseteq, Sp, kernelAt);
        Formula iff = Seq(
            Forall, Sp, other, Colon, Sp, relationType, Comma, Sp,
            Call("TauCongruence", update, other), Sp, Rightarrow, Sp,
            Open,
            Open, other, Sp, Subseteq, Sp, relation, Close, Sp, Iff, Sp,
            Open, other, Sp, Subseteq, Sp, kernelAt, Close,
            Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            update, Colon, Sp, state, Sp, To, Sp, state, Comma, RowBreak,
            relation, Colon, Sp, relationType, Comma, Sp,
            Call("Equivalence", relation), Sp, Rightarrow, RowBreak,
            equivalence, Sp, Land, Sp, congruence, Sp, Land, Sp,
            contraction, Sp, Land, RowBreak,
            Open, monotone, Close, Sp, Land, Sp,
            idempotent, Sp, Land, RowBreak,
            Open, maximal, Close, Sp, Land, RowBreak,
            Open, iff, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }
}
