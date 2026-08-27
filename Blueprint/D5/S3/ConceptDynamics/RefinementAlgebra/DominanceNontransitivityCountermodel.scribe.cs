using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementAlgebra;

internal sealed class DominanceNontransitivityCountermodelDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementAlgebra/DominanceNontransitivityCountermodel."
            + "complete_dominance_not_transitive";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A real phenotype on three unordered diploid genotypes makes complete dominance cyclic and nontransitive.",
        H("Dominance Nontransitivity Countermodel"),
        Blocks(Describe.Lean(
            DescribeId.Create("complete-dominance-not-transitive"),
            DeclarationHandle.Create(Declaration),
            H("Complete dominance need not be transitive"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The displayed real phenotype is defined on the canonical symmetric square "
                        + "of three alleles. Each dominance edge is displayed using the source "
                        + "kernel condition, including the closing edge of the directed cycle."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Pair(Formula first, Formula second) =>
        Apply(F.Id("s"), first, second);

    private static Formula Kernel(Formula readout, Formula first, Formula second) =>
        Apply(Seq(Operatorname, Grp(F.Id("ker"))), readout, first, second);

    private static Formula Dominates(
        Formula phenotype,
        Formula dominant,
        Formula recessive) => Seq(
            Open,
            Kernel(phenotype, Pair(dominant, dominant), Pair(dominant, recessive)),
            Sp, Land, Sp, Neg, Sp,
            Kernel(phenotype, Pair(dominant, recessive), Pair(recessive, recessive)),
            Close);

    private static Formula Value(
        Formula phenotype,
        Formula first,
        Formula second,
        Formula value) => Seq(
            Apply(phenotype, Pair(first, second)), Sp, Eq, Sp, value);

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula d = F.Id("d");
        Formula phenotype = F.Id("P");
        Formula finThree = Apply(F.Id("Fin"), D(3));
        Formula genotype = Apply(F.Id("Sym2"), finThree);
        Formula phenotypeType = Seq(genotype, Sp, Rightarrow, Sp, Mathbb, Grp(F.Id("R")));

        return Disp(Seq(
            Exists, Sp, a, Comma, Sp, b, Comma, Sp, d, InMacro, Sp, finThree,
            Comma, Sp, Exists, Sp, phenotype, Colon, Sp, phenotypeType, Comma,
            RowBreak, Grp(),
            a, Sp, Neq, Sp, b, Sp, Land, Sp,
            b, Sp, Neq, Sp, d, Sp, Land, Sp,
            a, Sp, Neq, Sp, d, Sp, Land,
            RowBreak, Grp(),
            Value(phenotype, a, a, D(0)), Sp, Land, Sp,
            Value(phenotype, a, b, D(0)), Sp, Land, Sp,
            Value(phenotype, b, b, D(1)), Sp, Land,
            RowBreak, Grp(),
            Value(phenotype, b, d, D(1)), Sp, Land, Sp,
            Value(phenotype, d, d, D(2)), Sp, Land, Sp,
            Value(phenotype, a, d, D(2)), Sp, Land,
            RowBreak, Grp(),
            Dominates(phenotype, a, b), Sp, Land, Sp,
            Dominates(phenotype, b, d), Sp, Land,
            RowBreak, Grp(),
            Neg, Sp, Dominates(phenotype, a, d), Sp, Land, Sp,
            Dominates(phenotype, d, a), Dot));
    }
}
