using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class CountableSingularPartitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula alpha = Alpha;
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula probability = F.Id("P");
        Formula weight = F.Id("a");
        Formula lambda = LambdaLower;
        Formula density = F.Id("f");
        Formula support = F.Id("A");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula nonnegativeExtended =
            Seq(Operatorname, Grp(F.Id("ENNReal")));
        Formula measure = Call("Measure", alpha);
        Formula probabilityAt = Seq(probability, Underscore, Grp(n));
        Formula probabilityAtM = Seq(probability, Underscore, Grp(m));
        Formula weightAt = Seq(weight, Underscore, Grp(n));
        Formula densityAt = Seq(density, Underscore, Grp(n));
        Formula densityAtM = Seq(density, Underscore, Grp(m));
        Formula supportAt = Seq(support, Underscore, Grp(n));
        Formula mixture = Seq(
            Sum, Underscore, Grp(n, Sp, InMacro, Sp, naturals), Sp,
            weightAt, Sp, probabilityAt);
        Formula derivative = Seq(
            Frac, Grp(Mathrm, Grp(F.Id("d")), probabilityAt),
            Grp(Mathrm, Grp(F.Id("d")), lambda));
        Formula statement = Disp(Seq(
            Forall, Sp, alpha, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma,
            Sp, OpenBracket, Call("MeasurableSpace", alpha), CloseBracket, Comma,
            RowBreak, Grp(), probability, Colon, Sp, naturals, Sp, To, Sp, measure,
            Comma, Sp, weight, Colon, Sp, naturals, Sp, To, Sp, nonnegativeExtended,
            Comma, RowBreak, Grp(),
            Open, Forall, Sp, n, Comma, Sp,
            Call("ProbabilityMeasure", probabilityAt), Close, Sp, Land, Sp,
            Open, Forall, Sp, n, Comma, Sp, D(0), Sp, Lt, Sp, weightAt, Close,
            Sp, Land, Sp,
            Sum, Underscore, Grp(n, Sp, InMacro, Sp, naturals), Sp,
            weightAt, Sp, Eq, Sp, D(1), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, n, Comma, Sp, m, Comma, Sp, n, Sp, Neq, Sp, m,
            Sp, Rightarrow, Sp,
            Call("MutuallySingular", probabilityAt, probabilityAtM), Close,
            RowBreak, Grp(), Rightarrow, Sp,
            Operatorname, Grp(F.Id("let")), Sp, lambda, Sp, Eq, Sp, mixture,
            Comma, Sp, density, Sp, Eq, Sp,
            Open, n, Sp, Mapsto, Sp, derivative, Close, SemiSpace,
            RowBreak, Grp(),
            Open, Forall, Sp, n, Comma, Sp, m, Comma, Sp, n, Sp, Neq, Sp, m,
            Sp, Rightarrow, Sp, densityAt, Sp, densityAtM, Sp, Eq, Sp, D(0),
            Sp, lambda, F.Text, Grp(Sp, F.Id("almost"), Sp, F.Id("everywhere")),
            Close, Sp, Land, RowBreak, Grp(),
            Exists, Sp, support, Colon, Sp, naturals, Sp, To, Sp, Call("Set", alpha),
            Comma, Sp,
            Open, Forall, Sp, n, Comma, Sp, Call("Measurable", supportAt), Close,
            Sp, Land, Sp, Call("PairwiseDisjoint", support), Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, n, Comma, Sp, probabilityAt, Open, supportAt, Close,
            Sp, Eq, Sp, D(1), Close, Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Pairwise singular probability laws have a common measurable partition into full-measure supports.",
            H("Countable Pairwise Singular Common Partition"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("countable-pairwise-singular-common-partition"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/MeasureSeparation/CountableSingularPartition."
                            + "countable_pairwise_singular_common_partition"),
                    H("Pairwise singular laws have disjoint full-measure supports"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let P_n be countably many probability laws on one measurable "
                                + "transcript space. Positive normalized weights construct "
                                + "their mixture lambda, and f_n is the Radon--Nikodym "
                                + "derivative of P_n with respect to that mixture.")),
                        Paragraph(Text(
                            "Pairwise mutual singularity forces f_n f_m to vanish lambda-almost "
                                + "everywhere whenever n and m differ. This is the density form "
                                + "of the separation claim in the source.")),
                        Paragraph(Text(
                            "The nonzero density supports are measurable and pairwise disjoint "
                                + "up to lambda-null sets. The countable measurable refinement "
                                + "theorem removes those overlaps simultaneously, producing "
                                + "genuinely pairwise disjoint measurable sets A_n. Absolute "
                                + "continuity transfers the refinement equality back to every "
                                + "P_n, so each law assigns its own set mass one."))),
                    DescribeRole.Theorem))));
    }
}
