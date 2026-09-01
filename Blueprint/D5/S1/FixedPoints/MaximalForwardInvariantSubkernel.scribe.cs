using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class MaximalForwardInvariantSubkernelDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/FixedPoints/MaximalForwardInvariantSubkernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every equivalence relation has a greatest forward-invariant subrelation.",
        H("Maximal Forward-Invariant Subkernel"),
        Blocks(Describe.Lean(
            DescribeId.Create("maximal-forward-invariant-subkernel"),
            DeclarationHandle.Create(Prefix + "maximal_forward_invariant_subkernel"),
            H("The forward-orbit kernel is the greatest invariant subkernel"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let Kq be an equivalence relation on X and let F be a self-map of X. "
                        + "The relation K-infinity consists of the pairs whose complete forward "
                        + "orbits remain related by Kq.")),
                Paragraph(Text(
                    "K-infinity is itself an equivalence relation contained in Kq and is "
                        + "preserved by applying F to both coordinates. Every relation contained "
                        + "in Kq with the same forward-invariance property is contained in "
                        + "K-infinity, which proves both existence and maximality.")),
                Paragraph(Text(
                    "The module also identifies K-infinity with the greatest fixed point of "
                        + "the monotone one-step refinement operator. The repository's general "
                        + "Knaster-Tarski wrapper supplies the extremal fixed-point facts; pinned "
                        + "Mathlib supplies OrderHom.gfp and the complete lattice of relations."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula Member(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula Iterate(Formula function, Formula count, Formula argument) =>
        Apply(Seq(function, Caret, Grp(count)), argument);

    private static Formula Invariance(
        Formula relation, Formula function, Formula left, Formula right) =>
        Seq(
            Forall, Sp, left, Comma, Sp, right, Comma, Sp,
            Member(Pair(left, right), relation), Sp, Rightarrow, Sp,
            Member(Pair(Apply(function, left), Apply(function, right)), relation));

    private static Formula Statement()
    {
        Formula carrier = F.Id("X");
        Formula function = F.Id("F");
        Formula ambient = Seq(F.Id("K"), Underscore, Grp(F.Id("q")));
        Formula kernel = Seq(F.Id("K"), Underscore, Grp(F.Id("infinity")));
        Formula relation = F.Id("R");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula count = F.Id("n");
        Formula relationType = Seq(
            Operatorname, Grp(F.Id("Set")), Open,
            carrier, Sp, Times, Sp, carrier, Close);
        Formula orbitKernel = Seq(
            OpenBrace, Pair(left, right), Sp, Mid, Sp,
            Forall, Sp, count, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Member(
                Pair(
                    Iterate(function, count, left),
                    Iterate(function, count, right)),
                ambient),
            CloseBrace);

        return Disp(Seq(
            Forall, Sp, carrier, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            function, Colon, Sp, carrier, Sp, To, Sp, carrier, Comma, RowBreak,
            ambient, Colon, Sp, relationType, Comma, Sp,
            Call("Equivalence", ambient), Sp, Rightarrow, RowBreak,
            kernel, Sp, Eq, Sp, orbitKernel, Sp, Land, RowBreak,
            Call("Equivalence", kernel), Sp, Land, Sp,
            kernel, Sp, Subseteq, Sp, ambient, Sp, Land, RowBreak,
            Open, Invariance(kernel, function, left, right), Close, Sp, Land, RowBreak,
            Forall, Sp, relation, Colon, Sp, relationType, Comma, Sp,
            Open, relation, Sp, Subseteq, Sp, ambient, Sp, Land, Sp,
            Invariance(relation, function, left, right), Close, Sp,
            Rightarrow, Sp, relation, Sp, Subseteq, Sp, kernel, Dot));
    }
}
