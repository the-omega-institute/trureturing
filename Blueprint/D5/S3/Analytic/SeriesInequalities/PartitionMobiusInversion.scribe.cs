using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class PartitionMobiusInversionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/SeriesInequalities/PartitionMobiusInversion."
            + "partition_mobius_moment_cumulant_inversion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Incidence-algebra inversion gives both finite partition moment-cumulant formulas.",
        H("Partition-Lattice Mobius Inversion"),
        Blocks(Describe.Lean(
            DescribeId.Create("partition-lattice-moment-cumulant-inversion"),
            DeclarationHandle.Create(Declaration),
            H("Moments and cumulants invert over finite set partitions"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let A be a nonempty finite set and let M and kappa assign values in a "
                        + "commutative ring to finite subsets. For a partition pi, P_w(pi) "
                        + "denotes the product of the block weights w(B).")),
                Paragraph(Text(
                    "Assume on every coarse partition that its moment product is the sum of "
                        + "the cumulant products over all refinements. Also assume the displayed "
                        + "classical closed formula for the partition-lattice Mobius function.")),
                Paragraph(Text(
                    "Mathlib's general incidence-algebra Mobius inversion then gives the "
                        + "cumulant formula at the top partition. Evaluating the assumed forward "
                        + "relation at that same top partition gives the reverse moment formula.")),
                Paragraph(Text(
                    "The source omitted the nonempty case split implicit in |pi|-1. The theorem "
                        + "requires A to be nonempty, ensuring every partition has at least one "
                        + "block and preventing truncated natural subtraction at zero."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("X"), ring = F.Id("R"), set = F.Id("A");
        Formula moment = F.Id("M"), cumulant = F.Id("kappa");
        Formula finiteSet = Call("Finset", carrier);
        Formula valueFamily = Seq(finiteSet, Sp, To, Sp, ring);
        Formula partitions = Call("Finpartition", set);
        Formula partition = F.Id("pi"), refinement = F.Id("sigma");
        Formula blockCount = Call("card", Call("parts", partition));
        Formula predecessor = Seq(blockCount, Sp, Minus, Sp, D(1));
        Formula coefficient = Seq(
            Grp(Minus, D(1)), Caret, Grp(predecessor), Sp, Cdot, Sp,
            Call("factorial", predecessor));
        Formula forward = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("pi", partitions)],
            EqualTo(
                Call("partitionProduct", moment, partition),
                Seq(
                    Sum, Underscore, Grp(refinement, Sp, Leq, Sp, partition), Sp,
                    Call("partitionProduct", cumulant, refinement))));
        Formula mobius = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("pi", partitions)],
            EqualTo(
                Call("mu", ring, partition, F.Id("top")),
                coefficient));
        Formula inverseFormula = EqualTo(
            Apply(cumulant, set),
            Seq(
                Sum, Underscore, Grp(partition, Sp, InMacro, Sp, partitions), Sp,
                coefficient, Sp, Cdot, Sp,
                Call("partitionProduct", moment, partition)));
        Formula forwardFormula = EqualTo(
            Apply(moment, set),
            Seq(
                Sum, Underscore, Grp(partition, Sp, InMacro, Sp, partitions), Sp,
                Call("partitionProduct", cumulant, partition)));
        Formula premises = And(
            NotEqualTo(set, Emptyset),
            And(forward, mobius));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("R", F.Id("CommRing")),
                Bound("A", finiteSet),
                Bound("M", valueFamily),
                Bound("kappa", valueFamily),
            ],
            Implies(premises, And(inverseFormula, forwardFormula))));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Not(EqualTo(left, right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
