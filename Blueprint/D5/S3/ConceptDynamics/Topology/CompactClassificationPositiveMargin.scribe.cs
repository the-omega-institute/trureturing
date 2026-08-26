using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Topology;

internal sealed class CompactClassificationPositiveMarginDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Topology/CompactClassificationPositiveMargin."
            + "compact_classification_positive_margin_and_closure_obstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compact continuous discrete classifier has a positive attained class margin, "
            + "while intersecting distinct fiber closures obstruct continuity.",
        H("Compact Classification Positive Margin"),
        Blocks(Describe.Lean(
            DescribeId.Create("compact-classification-positive-margin"),
            DeclarationHandle.Create(Declaration),
            H("Cross-class distance has a positive attained minimum"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The public construction first selects pairs whose classifier values differ, "
                        + "then maps those pairs to their metric distances, and finally takes the "
                        + "infimum of that distance image. Compactness and discreteness make the "
                        + "pair set compact, so its distance image is compact and the infimum is "
                        + "attained.")),
                Paragraph(Text(
                    "The nonconstant premise supplies a cross-class pair. At an attained minimum, "
                        + "the two points remain distinct, hence the margin is positive. Any closer "
                        + "pair with different labels would contradict minimality.")),
                Paragraph(Text(
                    "The obstruction clause has its own premise and does not assume continuity. "
                        + "Under continuity, discrete singleton fibers are closed, so a point in "
                        + "both closures would receive two distinct labels.")),
                Paragraph(Text(
                    "The source's displayed minimum has an empty index set for a constant "
                        + "classifier. The positive-margin implication therefore states "
                        + "nonconstancy explicitly; the closure obstruction remains unconditional."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula objectType = F.Id("X");
        Formula labelType = F.Id("Y");
        Formula classifier = F.Id("T");
        Formula pair = F.Id("p");
        Formula first = F.Id("x");
        Formula second = F.Id("xPrime");
        Formula firstLabel = F.Id("y");
        Formula secondLabel = F.Id("z");
        Formula separatedPairs = F.Id("P");
        Formula crossClassDistances = F.Id("D");
        Formula margin = F.Id("delta");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula productType = Call("Product", objectType, objectType);
        Formula pairFirst = Call("fst", pair);
        Formula pairSecond = Call("snd", pair);
        Formula pairDistance = Call("dist", pairFirst, pairSecond);
        Formula separatedPairSet = Seq(
            OpenBrace, pair, Colon, Sp, productType, Sp, Bar, Sp,
            Apply(classifier, pairFirst), Sp, Neq, Sp,
            Apply(classifier, pairSecond), CloseBrace);
        Formula distanceImage = Seq(
            OpenBrace, pairDistance, Sp, Bar, Sp,
            pair, InMacro, Sp, separatedPairs, CloseBrace);
        Formula firstFiber = Call("preimage", classifier,
            Seq(OpenBrace, firstLabel, CloseBrace));
        Formula secondFiber = Call("preimage", classifier,
            Seq(OpenBrace, secondLabel, CloseBrace));
        Formula intersectingClosures = Call(
            "Nonempty",
            Call("inter", Call("closure", firstFiber), Call("closure", secondFiber)));
        Formula nonconstant = Seq(
            Exists, Sp, first, Comma, Sp, second, Colon, Sp, objectType, Comma, Sp,
            Apply(classifier, first), Sp, Neq, Sp, Apply(classifier, second));
        Formula robust = Seq(
            Forall, Sp, first, Comma, Sp, second, Colon, Sp, objectType, Comma, Sp,
            Call("dist", first, second), Sp, Lt, Sp, margin, Sp, Rightarrow, Sp,
            Apply(classifier, first), Sp, Eq, Sp, Apply(classifier, second));
        Formula positiveMargin = Seq(
            Open, Call("Continuous", classifier), Sp, Land, Sp, nonconstant, Close,
            Sp, Rightarrow, Sp,
            Operatorname, Grp(F.Id("let")), Sp,
            Define(separatedPairs, Call("Set", productType), separatedPairSet), Comma,
            Define(crossClassDistances, Call("Set", real), distanceImage), Comma,
            Define(margin, real,
                Seq(Operatorname, Grp(F.Id("sInf")), Sp, crossClassDistances)),
            Operatorname, Grp(F.Id("in")), Sp,
            Open, D(0), Sp, Lt, Sp, margin, Sp, Land, Sp,
            margin, InMacro, Sp, crossClassDistances, Sp, Land, Sp, robust, Close);
        Formula closureObstruction = Seq(
            Open, Exists, Sp, firstLabel, Comma, Sp, secondLabel, Colon, Sp, labelType,
            Comma, Sp, firstLabel, Sp, Neq, Sp, secondLabel, Sp, Land, Sp,
            intersectingClosures, Close, Sp, Rightarrow, Sp,
            Neg, Sp, Call("Continuous", classifier));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, objectType, Comma, Sp, labelType, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            Open, Call("MetricSpace", objectType), Sp, Land, Sp,
            Call("CompactSpace", objectType), Sp, Land, Sp,
            Call("TopologicalSpace", labelType), Sp, Land, Sp,
            Call("DiscreteTopology", labelType), Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, classifier, Colon, Sp, objectType, Sp, To, Sp, labelType, Comma,
            RowBreak, Grp(),
            Open, positiveMargin, Close, Sp, Land,
            RowBreak, Grp(),
            Open, closureObstruction, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

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

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Define(Formula name, Formula type, Formula value) =>
        Seq(Typed(name, type), Sp, Colon, Eq, Sp, value);
}
