using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class MultifactorCorrelationSectorDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/MultifactorCorrelationSectorDecomposition."
            + "multifactor_correlation_sector_decomposition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Hermitian tensor products split into subset-indexed correlation sectors.",
        H("Multifactor Correlation Sector Decomposition"),
        Blocks(Describe.Lean(
            DescribeId.Create("multifactor-correlation-sector-decomposition"),
            DeclarationHandle.Create(Declaration),
            H("Correlation order decomposes the global traceless carrier"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a finite family of positive local dimensions, split each real "
                        + "Hermitian space into its scalar identity line and trace-zero "
                        + "subspace. Distributing the tensor product over these local "
                        + "splittings produces one sector for every subset of factors.")),
                Paragraph(Text(
                    "The sectors form an internal direct sum. The nonempty sectors are "
                        + "exactly the global trace-zero carrier, and the sector indexed by "
                        + "S has dimension equal to the product of d_i squared minus one "
                        + "over the indices in S.")),
                Paragraph(Text(
                    "Consequently, readouts retaining sectors of order at most k leave a "
                        + "residual whose dimension is the sum of those products over subsets "
                        + "of cardinality greater than k. This dimension statement does not "
                        + "assert that a nonzero high-order component is entangled.")),
                Paragraph(Text(
                    "The source statement omitted positivity of the local dimensions. The "
                        + "formal theorem assumes every d_i is nonzero: in dimension zero the "
                        + "identity is zero, so the scalar identity sector is not one-dimensional "
                        + "and the stated formulas fail."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Rank(Formula space) => Call("finrankR", space);

    private static Formula SquareMinusOne(Formula value) =>
        Seq(new Formula.Power(value, D(2)), Sp, Minus, Sp, D(1));

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula d = F.Id("d");
        Formula i = F.Id("i");
        Formula subset = F.Id("S");
        Formula k = F.Id("k");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula dimensionAt = Call("d", i);
        Formula sector = Call("correlationSector", d, subset);
        Formula sectorWeight = Seq(
            Prod, Underscore, Grp(Seq(i, InMacro, Sp, subset)), Sp,
            Grp(SquareMinusOne(dimensionAt)));
        Formula globalProduct = Seq(
            Prod, Underscore, Grp(Seq(i, InMacro, Sp, indexType)), Sp,
            dimensionAt);
        Formula highOrderRank = Seq(
            Sum, Underscore,
            Grp(Seq(subset, Colon, Sp, Call("Finset", indexType), Comma, Sp,
                Call("card", subset), Sp, Gt, Sp, k)), Sp,
            sectorWeight);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, indexType, Colon, Sp, type, Comma, Sp,
            Call("Fintype", indexType), Comma, RowBreak, Grp(),
            d, Colon, Sp, indexType, Sp, To, Sp, naturals, Comma, Sp,
            Open, Forall, Sp, i, Colon, Sp, indexType, Comma, Sp,
            dimensionAt, Sp, Geq, Sp, D(1), Close, Sp, Rightarrow, RowBreak, Grp(),
            Call("InternalDirectSum", Call("correlationSector", d)), Sp, Land,
            RowBreak, Grp(),
            Call("iSupNonempty", Call("correlationSector", d)), Sp, Eq, Sp,
            Call("traceZeroGlobal", d), Sp, Land, RowBreak, Grp(),
            Rank(Call("traceZeroGlobal", d)), Sp, Eq, Sp,
            SquareMinusOne(Grp(globalProduct)), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, subset, Colon, Sp, Call("Finset", indexType), Comma,
            Sp, Rank(sector), Sp, Eq, Sp, sectorWeight, Close, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, k, InMacro, Sp, naturals, Comma, Sp,
            Rank(Call("unobservedHighOrder", d, k)), Sp, Eq, Sp,
            highOrderRank, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
