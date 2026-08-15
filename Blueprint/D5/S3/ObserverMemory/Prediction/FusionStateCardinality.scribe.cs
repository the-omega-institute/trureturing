using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class FusionStateCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjective component maps and an injective product map bound the number of fused states.",
        H("Fusion State Cardinality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fusion-state-cardinality-has-component-and-product-bounds"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/FusionStateCardinality."
                        + "fusion_state_cardinality_bounds"),
                H("Fusion state cardinality has component and product bounds"),
                StatementSource.FromAuthor(FusionBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y, Z1, Z2, and Z12 be finite state types. Suppose Y maps "
                            + "surjectively onto the fused type Z12, Z12 maps surjectively "
                            + "onto each component type, and Z12 maps injectively into the "
                            + "product Z1 times Z2. Then the fused cardinality is at least "
                            + "both component cardinalities and at most both the original "
                            + "cardinality and the product cardinality.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the exact four ingredients: "
                            + "Nat.card_le_card_of_surjective for the two lower comparisons "
                            + "and the original-state upper comparison, "
                            + "Nat.card_le_card_of_injective for the product upper comparison, "
                            + "and Nat.card_prod to evaluate the product type. Loogle and "
                            + "LeanSearch returned those component results and nearby range "
                            + "lemmas, but no theorem packaging the complete maximum/minimum "
                            + "bound.")),
                    Paragraph(Text(
                        "The theorem records exactly the finite cardinal consequence of the "
                            + "canonical quotient and product maps. It makes no independence, "
                            + "product-surjectivity, entropy, metric, or asymptotic claim."))),
                DescribeRole.Theorem))));

    private static Formula IndexedZ(params byte[] digits) =>
        Seq(F.Id("Z"), Underscore, Grp(D(digits)));

    private static Formula Card(Formula type) =>
        Seq(Operatorname, Grp(F.Id("card")), Open, type, Close);

    private static Formula FusionBoundFormula()
    {
        Formula zOne = IndexedZ(1);
        Formula zTwo = IndexedZ(2);
        Formula zTwelve = IndexedZ(1, 2);
        Formula pi = F.Id("pi");
        Formula first = F.Id("toFirst");
        Formula second = F.Id("toSecond");
        Formula product = F.Id("intoProduct");

        return Disp(Seq(
            Forall, Sp, F.Id("Y"), Comma, Sp, zOne, Comma, Sp, zTwo, Comma, Sp,
            zTwelve, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, F.Id("Y"), CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, zOne, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, zTwo, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, zTwelve, CloseBracket, Comma, Esc,
            pi, Colon, Sp, F.Id("Y"), Sp, To, Sp, zTwelve, Comma, Sp,
            first, Colon, Sp, zTwelve, Sp, To, Sp, zOne, Comma, Sp,
            second, Colon, Sp, zTwelve, Sp, To, Sp, zTwo, Comma, Sp,
            product, Colon, Sp, zTwelve, Sp, To, Sp, zOne, Sp, Times, Sp, zTwo, Comma, Esc,
            Call("Surjective", pi), Sp, Rightarrow, Sp,
            Call("Surjective", first), Sp, Rightarrow, Sp,
            Call("Surjective", second), Sp, Rightarrow, Sp,
            Call("Injective", product), Sp, Rightarrow, Esc,
            Open,
            Max, Open, Card(zOne), Comma, Sp, Card(zTwo), Close,
            Sp, Leq, Sp, Card(zTwelve),
            Sp, Land, Sp,
            Card(zTwelve), Sp, Leq, Sp,
            Min, Open, Card(F.Id("Y")), Comma, Sp,
            Card(zOne), Sp, Times, Sp, Card(zTwo), Close,
            Close, Dot));
    }
}
