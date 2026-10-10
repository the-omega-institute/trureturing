using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class PartitionMobiusCoefficientDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/SeriesInequalities/PartitionMobiusCoefficient.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/rota1964mobius");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The partition-lattice Mobius coefficient is a signed factorial in every commutative ring.",
        H("Partition Mobius Coefficients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partition-mobius-coefficient"),
                DeclarationHandle.Create(Prefix + "partition_mobius_coefficient"),
                H("The coefficient depends only on the number of blocks"),
                StatementSource.FromAuthor(CoefficientFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let A be a nonempty finite set. Partitions are ordered by "
                        + "refinement, so the top partition has the single block A. For any "
                        + "commutative ring R, the incidence-algebra coefficient from P to the "
                        + "top is the signed factorial of one less than the number of blocks.")),
                    Paragraph(Text("A partition of the actual blocks of P determines a coarsening "
                        + "by taking the union of each group of blocks. Grouping the old blocks "
                        + "inside each coarse block gives the inverse, and these maps preserve "
                        + "the number of blocks.")),
                    Paragraph(Text("Inserting a fresh point either creates a singleton block or "
                        + "joins one old block. If w(k)=(-1)^(k-1)(k-1)!, the two contributions "
                        + "cancel because w(k+1)+k*w(k)=0 for k>0. The total weighted sum is "
                        + "one on a singleton and zero on larger nonempty sets. Applying this "
                        + "to the blocks of P gives the top delta function; incidence-algebra "
                        + "inversion identifies w with the Mobius coefficient.")),
                    Paragraph(Text("This is the classical partition-lattice formula in Rota, "
                        + "Section 7, Example 1, Proposition 3, pp. 359-360. Natural factorials "
                        + "are cast into R; no characteristic or nontriviality assumption is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partition-moment-cumulant-without-mu"),
                DeclarationHandle.Create(Prefix + "moment_cumulant_without_mu_assumption"),
                H("Moment and cumulant sums with the computed coefficient"),
                StatementSource.FromAuthor(InversionFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Write partitionProduct(w,P) for the product of w(B) over "
                        + "the blocks B of P. Suppose every moment product equals the sum of "
                        + "cumulant products over its refinements. The computed coefficient "
                        + "and partition_mobius_moment_cumulant_inversion then give the two "
                        + "displayed formulas.")),
                    Paragraph(Text("The refinement relation is the only relation assumed between "
                        + "M and kappa. The Mobius coefficient is proved above. Identifying these "
                        + "abstract weights with coefficients of a particular finite-source "
                        + "logarithm or exponential requires a separate argument."))),
                DescribeRole.Theorem))));

    private static Formula Coefficient(Formula partition) => Seq(
        Grp(Minus, D(1)), Caret,
        Grp(Call("card", Call("parts", partition)), Sp, Minus, Sp, D(1)),
        Sp, Cdot, Sp,
        Call("factorial", Seq(Call("card", Call("parts", partition)), Sp, Minus, Sp, D(1))));

    private static Formula CoefficientFormula()
    {
        Formula set = F.Id("A"), partition = F.Id("P"), ring = F.Id("R");
        return WithCarriers(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("A", Call("Finset", F.Id("X"))), Bound("P", Call("Finpartition", set))],
            Implies(NotEqualTo(set, Emptyset),
                EqualTo(Call("mu", ring, partition, F.Id("top")), Coefficient(partition)))));
    }

    private static Formula InversionFormula()
    {
        Formula set = F.Id("A"), ring = F.Id("R"), partition = F.Id("P");
        Formula refinement = F.Id("Q"), moment = F.Id("M"), cumulant = F.Id("kappa");
        Formula finiteSet = Call("Finset", F.Id("X"));
        Formula partitions = Call("Finpartition", set);
        Formula family = Seq(finiteSet, Sp, To, Sp, ring);
        Formula relation = new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("P", partitions)], EqualTo(Call("partitionProduct", moment, partition),
                Seq(Sum, Underscore, Grp(refinement, Sp, Leq, Sp, partition), Sp,
                    Call("partitionProduct", cumulant, refinement))));
        Formula inverse = EqualTo(new Formula.Apply(cumulant, [set]),
            Seq(Sum, Underscore, Grp(partition, Sp, InMacro, Sp, partitions), Sp,
                Coefficient(partition), Sp, Cdot, Sp, Call("partitionProduct", moment, partition)));
        Formula forward = EqualTo(new Formula.Apply(moment, [set]),
            Seq(Sum, Underscore, Grp(partition, Sp, InMacro, Sp, partitions), Sp,
                Call("partitionProduct", cumulant, partition)));
        return WithCarriers(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("A", finiteSet), Bound("M", family), Bound("kappa", family)],
            Implies(And(NotEqualTo(set, Emptyset), relation), And(inverse, forward))));
    }

    private static Formula WithCarriers(Formula body) => Disp(
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("X", F.Id("Type")), Bound("R", F.Id("Type"))],
            Seq(OpenBracket, Call("DecidableEq", F.Id("X")), CloseBracket, Sp,
                OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Comma, Sp, body)));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqualTo(Formula left, Formula right) => new Formula.Not(EqualTo(left, right));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
