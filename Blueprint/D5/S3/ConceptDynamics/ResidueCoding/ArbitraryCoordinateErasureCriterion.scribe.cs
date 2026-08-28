using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ResidueCoding;

internal sealed class ArbitraryCoordinateErasureCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ResidueCoding/ArbitraryCoordinateErasureCriterion."
            + "arbitrary_coordinate_erasure_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Worst-case residue erasure capacity is the product of the smallest survivors.",
        H("Arbitrary Coordinate Erasure Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("arbitrary-coordinate-erasure-criterion"),
                DeclarationHandle.Create(Declaration),
                H("Every coordinate erasure pattern is faithful at prefix capacity"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The readout on each retained coordinate set is the canonical joint "
                            + "readout of the corresponding residue channels.")),
                    Paragraph(Text(
                        "The retained-set recovery criterion reduces injectivity to product "
                            + "capacity. Sortedness then proves that the first surviving "
                            + "prefix has no larger product than any equally sized set."))),
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

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula TheoremFormula()
    {
        Formula modulus = F.Id("m");
        Formula length = F.Id("n");
        Formula erased = F.Id("s");
        Formula capacity = F.Id("K");
        Formula firstIndex = F.Id("i");
        Formula secondIndex = F.Id("j");
        Formula retained = F.Id("R");
        Formula message = F.Id("x");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula indexType = Call("Fin", length);
        Formula erasedType = Call("Fin", Seq(length, Sp, Plus, Sp, D(1)));
        Formula retainedType = Call("Finset", indexType);
        Formula retainedCount = Seq(length, Sp, Minus, Sp, erased);
        Formula modulusAt(Formula index) => Apply(modulus, index);
        Formula boundedModuli = Seq(
            Forall, Sp, firstIndex, Lt, length, Comma, Sp,
            D(2), Sp, Le, Sp, modulusAt(firstIndex));
        Formula sortedModuli = Seq(
            Forall, Sp, firstIndex, Comma, Sp, secondIndex, Lt, length,
            Comma, Sp, firstIndex, Sp, Lt, Sp, secondIndex,
            Sp, Rightarrow, Sp,
            modulusAt(firstIndex), Sp, Lt, Sp, modulusAt(secondIndex));
        Formula coprimeModuli = Seq(
            Forall, Sp, firstIndex, Comma, Sp, secondIndex, Lt, length,
            Comma, Sp, firstIndex, Sp, Neq, Sp, secondIndex,
            Sp, Rightarrow, Sp,
            Call("Coprime", modulusAt(firstIndex), modulusAt(secondIndex)));
        Formula retainedCard = Seq(
            Call("card", retained), Sp, Eq, Sp, retainedCount);
        Formula residueChannel = Seq(
            Lambda, Sp, firstIndex, Colon, Sp, retained, Comma, Sp,
            Lambda, Sp, message, Colon, Sp, Call("Fin", capacity), Comma, Sp,
            Call("castZMod", Call("val", message),
                modulusAt(Call("val", firstIndex))));
        Formula retainedFaithful = Call("Injective",
            Call("jointReadout", residueChannel));
        Formula allErasuresFaithful = Seq(
            Forall, Sp, retained, Colon, Sp, retainedType, Comma, Sp,
            retainedCard, Sp, Rightarrow, Sp, retainedFaithful);
        Formula prefixProduct = Seq(
            Prod, Underscore,
            Grp(firstIndex, Colon, Sp, Call("Fin", retainedCount)), Sp,
            modulusAt(firstIndex));
        Formula retainedProduct = Seq(
            Prod, Underscore,
            Grp(firstIndex, InMacro, Sp, retained), Sp,
            modulusAt(Call("val", firstIndex)));
        Formula capacityCriterion = Seq(
            Grp(allErasuresFaithful), Sp, Iff, Sp,
            capacity, Sp, Le, Sp, prefixProduct);
        Formula minimumSurvivor = Seq(
            Forall, Sp, retained, Colon, Sp, retainedType, Comma, Sp,
            retainedCard, Sp, Rightarrow, Sp,
            prefixProduct, Sp, Le, Sp, retainedProduct);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, modulus, Colon, Sp, naturals, Sp, To, Sp, naturals,
            Comma, Sp, length, Comma, Sp, capacity, Colon, Sp, naturals,
            Comma, RowBreak, Grp(),
            erased, Colon, Sp, erasedType, Comma, RowBreak, Grp(),
            boundedModuli, Sp, Land, RowBreak, Grp(),
            sortedModuli, Sp, Land, RowBreak, Grp(),
            coprimeModuli, Sp, Rightarrow, RowBreak, Grp(),
            Grp(capacityCriterion), Sp, Land, RowBreak, Grp(),
            minimumSurvivor, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
