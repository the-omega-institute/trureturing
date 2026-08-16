using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Fusion;

internal sealed class JointPredictionProductFullnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint prediction fills the product exactly when every pair of prediction fibers meets.",
        H("Joint Prediction Product Fullness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-prediction-product-fullness-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Fusion/JointPredictionProductFullness."
                        + "joint_prediction_product_fullness_criterion"),
                H("Joint prediction product fullness criterion"),
                StatementSource.FromAuthor(FullnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a finite realized state type map surjectively onto a fused state "
                            + "type, and let an injective joint prediction map send each fused "
                            + "state to its two component predictions. The joint map is "
                            + "surjective exactly when every pair of component prediction "
                            + "fibers has a common realizing state.")),
                    Paragraph(Text(
                        "For finite state spaces, injectivity turns product fullness into an "
                            + "exact cardinality test: the fused state count equals the product "
                            + "of the component state counts. Pinned Mathlib supplies the exact "
                            + "cardinality bridge Nat.bijective_iff_injective_and_card and the "
                            + "product identity Nat.card_prod. Direct local source search found "
                            + "these declarations; local smart-search returned no declarations, "
                            + "Loogle returned zero shaped matches, and LeanSearch's API endpoint "
                            + "returned HTTP 404.")),
                    Paragraph(Text(
                        "The theorem proves compatibility fullness for two finite prediction "
                            + "coordinates. It does not assert probabilistic independence, an "
                            + "entropy identity, or a decomposition for more than two factors."))),
                DescribeRole.Theorem))));

    private static Formula IndexedZ(params byte[] digits) =>
        Seq(F.Id("Z"), Underscore, Grp(D(digits)));

    private static Formula Card(Formula type) =>
        Seq(Operatorname, Grp(F.Id("card")), Open, type, Close);

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula FullnessFormula()
    {
        Formula y = F.Id("Y");
        Formula zOne = IndexedZ(1);
        Formula zTwo = IndexedZ(2);
        Formula zTwelve = IndexedZ(1, 2);
        Formula realize = F.Id("realize");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula joint = F.Id("joint");
        Formula state = F.Id("state");
        Formula firstValue = F.Id("z1");
        Formula secondValue = F.Id("z2");

        Formula realizesPair = Seq(
            Forall, Sp, state, Comma, Sp,
            At(joint, At(realize, state)), Sp, Eq, Sp,
            Open, At(first, state), Comma, Sp, At(second, state), Close);

        Formula everyFiberPairMeets = Seq(
            Forall, Sp, firstValue, Comma, Sp, secondValue, Comma, Esc,
            Exists, Sp, state, Comma, Sp,
            At(first, state), Sp, Eq, Sp, firstValue, Sp, Land, Sp,
            At(second, state), Sp, Eq, Sp, secondValue);

        return Disp(Seq(
            Forall, Sp, y, Comma, Sp, zOne, Comma, Sp, zTwo, Comma, Sp,
            zTwelve, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, y, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, zOne, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, zTwo, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, zTwelve, CloseBracket,
            Comma, Esc,
            realize, Colon, Sp, y, Sp, To, Sp, zTwelve, Comma, Sp,
            first, Colon, Sp, y, Sp, To, Sp, zOne, Comma, Sp,
            second, Colon, Sp, y, Sp, To, Sp, zTwo, Comma, Sp,
            joint, Colon, Sp, zTwelve, Sp, To, Sp, zOne, Sp, Times, Sp, zTwo,
            Comma, Esc,
            Call("Surjective", realize), Sp, Rightarrow, Sp,
            Call("Injective", joint), Sp, Rightarrow, Sp,
            Open, realizesPair, Close, Sp, Rightarrow, Esc,
            Open,
            Open, Call("Surjective", joint), Sp, Iff, Sp, everyFiberPairMeets, Close,
            Sp, Land, Esc,
            Open, Call("Surjective", joint), Sp, Iff, Sp,
            Card(zTwelve), Sp, Eq, Sp, Card(zOne), Sp, Times, Sp, Card(zTwo), Close,
            Close, Dot));
    }
}
