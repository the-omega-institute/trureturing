using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class SinglePrimeVisibleSpaceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Entanglement/SinglePrimeVisibleSpace."
            + "single_prime_visible_space";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Single-prime Hermitian effects see exactly the scalar and singleton sectors.",
        H("Single-Prime Visible Space"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("single-prime-visible-space"),
                DeclarationHandle.Create(Declaration),
                H("Single-prime readout leaves exactly the cross-prime sectors invisible"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite family of local Hilbert dimensions, primeSector is the "
                            + "repository's canonical tensor sector: factors in S are traceless "
                            + "Hermitian and factors outside S are scalar Hermitian.")),
                    Paragraph(Text(
                        "The standing internal-decomposition and sector-rank hypotheses are the "
                            + "formal counterparts of the orthogonal sector expansion immediately "
                            + "preceding theorem 119.1 in the source.")),
                    Paragraph(Text(
                        "The four conclusion clauses identify the visible space, compute its real "
                            + "dimension, compute the invisible trace-zero residual dimension, and "
                            + "identify that residual with exactly the sectors supported on at "
                            + "least two factors."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula iota = Iota;
        Formula index = F.Id("i");
        Formula support = F.Id("S");
        Formula localIndex = F.Id("j");
        Formula dimensions = F.Id("d");
        Formula nat = Call("Nat");
        Formula finset = Call("Finset", iota);
        Formula dimensionFamily = new Formula.TypeArrow(iota, nat);
        Formula dimensionAtIndex = Apply(dimensions, index);
        Formula dimensionAtLocalIndex = Apply(dimensions, localIndex);
        Formula singleton = Seq(OpenBrace, index, CloseBrace);
        Formula Sector(Formula set) => Call("primeSector", dimensions, set);
        Formula residual = Call("invisibleTraceZeroResidual", dimensions);
        Formula visible = Call("singlePrimeVisibleSpace", dimensions);
        Formula sectorTerm = Seq(
            dimensionAtLocalIndex, Caret, Grp(D(2)), Sp, Minus, Sp, D(1));
        Formula sectorRank = Seq(
            Prod, Underscore,
            Grp(localIndex, Sp, InMacro, Sp, support), Sp, Grp(sectorTerm));
        Formula localCorrection = Seq(
            Sum, Underscore, Grp(index, Sp, InMacro, Sp, iota), Sp,
            Grp(dimensionAtIndex, Caret, Grp(D(2)), Sp, Minus, Sp, D(1)));
        Formula totalDimension = Seq(
            Prod, Underscore, Grp(index, Sp, InMacro, Sp, iota), Sp,
            dimensionAtIndex);
        Formula singletonSup = Call(
            "iSup", index, Seq(index, Sp, Mapsto, Sp, Sector(singleton)));
        Formula highSupport = Call(
            "iSup",
            Seq(OpenBrace, support, Colon, Sp, finset, Sp, Mid, Sp,
                D(2), Sp, Leq, Sp, Call("card", support), CloseBrace),
            Seq(support, Sp, Mapsto, Sp, Sector(support)));
        Formula internalPremise = Call(
            "IsInternal", Seq(support, Sp, Mapsto, Sp, Sector(support)));
        Formula rankPremise = Seq(
            Forall, Sp, support, Colon, Sp, finset, Comma, Sp,
            Call("finrankR", Sector(support)), Sp, Eq, Sp, sectorRank);
        Formula visibleRank = Seq(
            D(1), Sp, Plus, Sp, localCorrection);
        Formula residualRank = Seq(
            Grp(totalDimension), Caret, Grp(D(2)), Sp, Minus, Sp, D(1),
            Sp, Minus, Sp, localCorrection);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, iota, Colon, Sp, Call("Type"), Comma, Sp,
            Call("Fintype", iota), Comma, Sp, Call("DecidableEq", iota),
            Comma, RowBreak, Grp(),
            dimensions, Colon, Sp, dimensionFamily, Comma, RowBreak, Grp(),
            internalPremise, Sp, Land, RowBreak, Grp(),
            Open, rankPremise, Close, Sp, Rightarrow, RowBreak, Grp(),
            visible, Sp, Eq, Sp, Call("Sup", Sector(Emptyset), singletonSup),
            Sp, Land, RowBreak, Grp(),
            Call("finrankR", visible), Sp, Eq, Sp, visibleRank,
            Sp, Land, RowBreak, Grp(),
            Call("finrankR", residual), Sp, Eq, Sp, residualRank,
            Sp, Land, RowBreak, Grp(),
            residual, Sp, Eq, Sp, highSupport, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
