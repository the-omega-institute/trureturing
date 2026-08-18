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

    private static Formula PairIn(Formula left, Formula right, Formula relation) =>
        Seq(Open, left, Comma, Sp, right, Close, Sp, InMacro, Sp, relation);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("Y");
        Formula relation = F.Id("R");
        Formula kernel = F.Id("C");
        Formula update = F.Id("tau");
        Formula left = F.Id("y");
        Formula right = F.Id("yPrime");
        Formula other = F.Id("S");
        Formula kernelAt = Apply(kernel, relation);
        Formula pairKernel = PairIn(left, right, kernelAt);
        Formula pairRelation = PairIn(left, right, relation);
        Formula pairOther = PairIn(left, right, other);
        Formula shiftedKernel = PairIn(Apply(update, left), Apply(update, right), kernelAt);
        Formula shiftedOther = PairIn(Apply(update, left), Apply(update, right), other);

        Formula equivalence = Call("Equivalence", kernelAt);
        Formula congruence = Seq(
            Forall, Sp, left, Comma, Sp, right, Comma, Sp, pairKernel,
            Sp, Rightarrow, Sp, shiftedKernel);
        Formula contraction = Seq(kernelAt, Sp, Subseteq, Sp, relation);
        Formula monotone = Seq(
            Forall, Sp, other, Comma, Sp, other, Sp, Subseteq, Sp, relation,
            Sp, Rightarrow, Sp, Apply(kernel, other), Sp, Subseteq, Sp, kernelAt);
        Formula idempotent = Seq(Apply(kernel, kernelAt), Sp, Eq, Sp, kernelAt);
        Formula maximal = Seq(
            Forall, Sp, other, Comma, Sp, other, Sp, Subseteq, Sp, relation, Sp,
            Land, Sp, shiftedOther, Sp, Rightarrow, Sp,
            Apply(kernel, other), Sp, Subseteq, Sp, kernelAt);
        Formula iff = Seq(
            Forall, Sp, other, Comma, Sp,
            Open, shiftedOther, Sp, Rightarrow, Sp, relation, Sp, Subseteq, Sp,
            kernelAt, Close, Sp, Rightarrow, Sp,
            Open, other, Sp, Subseteq, Sp, relation, Close, Sp, Iff, Sp,
            Open, other, Sp, Subseteq, Sp, kernelAt, Close);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, relation, Comma, RowBreak,
            equivalence, Sp, Land, Sp, congruence, Sp, Land, Sp,
            contraction, Sp, Land, Sp, monotone, Sp, Land, Sp,
            idempotent, Sp, Land, Sp, maximal, Sp, Land, Sp, iff, Dot));
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
