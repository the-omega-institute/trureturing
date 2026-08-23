using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Reversibility;

internal sealed class LeftInvertibleRecoversAllTargetsDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Reversibility/LeftInvertibleRecoversAllTargets.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A left-invertible process recovers every target, while a nonconstant target can "
            + "survive without left invertibility.",
        H("Left-Invertible Processes Recover All Targets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("identity-erasure-preserves-nontrivial-value"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "identity_erasure_preserves_nontrivial_value"),
                H("Identity erasure preserves a nontrivial value"),
                StatementSource.FromAuthor(IdentityErasureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Projecting a pair of Booleans to its first coordinate cannot have "
                            + "a left inverse: the two states with first coordinate false "
                            + "and different identity coordinates have the same image.")),
                    Paragraph(Text(
                        "Nevertheless, the numerical target that assigns zero or one from "
                            + "the retained first coordinate factors through this projection. "
                            + "It distinguishes a false-valued state from a true-valued state, "
                            + "so the preserved target is genuinely nonconstant."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("left-invertible-recovers-all-targets"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "left_invertible_recovers_all_targets"),
                H("A left inverse recovers every target"),
                StatementSource.FromAuthor(LeftInvertibleRecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If R is a left inverse of a process U, every target T is recovered "
                            + "by applying T after R to the process output. Consequently the "
                            + "canonical readout of T factors through U, so it refines U.")),
                    Paragraph(Text(
                        "This conclusion covers every target codomain and also the empty-state "
                            + "case. The accompanying finite witness shows the converse fails "
                            + "for preservation of a particular target: erasing identity is not "
                            + "left-invertible even though it preserves a nonconstant value.")),
                    Paragraph(Text(
                        "The refinement conclusion uses the repository's universal sufficiency "
                            + "factorization theorem. The finite obstruction uses the fact that "
                            + "a map with a left inverse is injective."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Pair(Formula first, Formula second) =>
        Seq(Open, first, Comma, Sp, second, Close);

    private static Formula Compose(Formula outer, Formula inner) =>
        Seq(outer, Sp, Circ, Sp, inner);

    private static Formula LeftInverse(Formula recovery, Formula process) =>
        Call("LeftInverse", recovery, process);

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula CanonicalTarget(Formula target) =>
        Call("canonicalTargetReadout", target);

    private static Formula IdentityErasureClaim()
    {
        Formula boolean = F.Id("Bool");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula recovery = F.Id("R");
        Formula factor = F.Id("recover");
        Formula erasure = F.Id("eraseIdentity");
        Formula retained = F.Id("retainedValue");
        Formula falseValue = F.Id("false");
        Formula trueValue = F.Id("true");
        Formula state = Seq(boolean, Sp, Times, Sp, boolean);
        Formula noLeftInverse = Seq(
            Neg, Sp, Exists, Sp,
            Typed(recovery, Arrow(boolean, state)), Comma, Sp,
            LeftInverse(recovery, erasure));
        Formula factorization = Seq(
            retained, Sp, Eq, Sp, Compose(factor, erasure));
        Formula distinction = Seq(
            Apply(retained, Pair(falseValue, falseValue)), Sp, Neq, Sp,
            Apply(retained, Pair(trueValue, falseValue)));

        return Seq(
            Open, noLeftInverse, Close, Sp, Land, RowBreak, Grp(),
            Exists, Sp, Typed(factor, Arrow(boolean, natural)), Comma, RowBreak, Grp(),
            factorization, Sp, Land, RowBreak, Grp(),
            distinction);
    }

    private static Formula IdentityErasureFormula() =>
        Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            IdentityErasureClaim(), Dot,
            End, Grp(F.Id("gathered"))));

    private static Formula LeftInvertibleRecoveryFormula()
    {
        Formula state = F.Id("X");
        Formula processOutput = F.Id("B");
        Formula targetOutput = F.Id("Y");
        Formula process = F.Id("U");
        Formula recovery = F.Id("R");
        Formula target = F.Id("T");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula targetRecovery = Seq(
            target, Sp, Eq, Sp,
            Open, Compose(target, recovery), Close, Sp, Circ, Sp, process);
        Formula targetRefinement = Refines(CanonicalTarget(target), process);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(state, Comma, Sp, processOutput), type), Comma, RowBreak,
            Grp(),
            Typed(process, Arrow(state, processOutput)), Comma, Sp,
            Typed(recovery, Arrow(processOutput, state)), Comma, RowBreak, Grp(),
            LeftInverse(recovery, process), Sp, Rightarrow, RowBreak, Grp(),
            Open,
            Forall, Sp, Typed(targetOutput, type), Comma, Sp,
            Typed(target, Arrow(state, targetOutput)), Comma, RowBreak, Grp(),
            targetRecovery, Sp, Land, Sp, targetRefinement,
            Close, Sp, Land, RowBreak, Grp(),
            Open, IdentityErasureClaim(), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
