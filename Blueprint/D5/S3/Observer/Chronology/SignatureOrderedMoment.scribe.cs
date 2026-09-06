using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class SignatureOrderedMomentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Chronology/SignatureOrderedMoment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every finite word, doubled degree two is its event-square sum plus twice its ordered-pair moment.",
        H("Signature and Ordered-Moment Semantics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signature-ordered-moment-stored-coordinate"),
                DeclarationHandle.Create(Prefix + "chronological_signature_doubledDegreeTwo_eq"),
                H("The stored coordinate for all finite words"),
                StatementSource.FromAuthor(StoredFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A and E are arbitrary types, A is a possibly noncommutative semiring, o maps E to A, and w is a finite list over E. The diagonal term sums o(e)o(e) over the occurrences in w; M2 is the existing orderedPairMoment on the value list. The formula accounts for both repeated events and ordered cross terms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signature-ordered-moment-magnus-coordinate"),
                DeclarationHandle.Create(Prefix + "doubledMagnusDegreeTwo_eq_orderedPairMoment_sub_reverse"),
                H("Magnus is the difference between the two orientations"),
                StatementSource.FromAuthor(MagnusFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary types A and E, a ring A, o : E to A, and w : List E, the corrected coordinate is the forward ordered-pair moment minus the moment of the reversed value list. The proof uses the all-word square decomposition, which separates event squares from both ordered orientations without assuming commutativity or dividing by two."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Hypotheses(string algebra) => Seq(
        Forall, Sp, F.Id("A"), Comma, Sp, F.Id("E"), Comma, Sp,
        Call(algebra, F.Id("A")), Comma, Sp,
        F.Id("o"), Colon, F.Id("E"), To, Sp, F.Id("A"), Comma, Sp,
        F.Id("w"), Colon, Call("List", F.Id("E")), Comma, Sp);

    private static Formula Values() => Call("map", F.Id("o"), F.Id("w"));

    private static Formula StoredFormula() => Disp(Seq(
        Hypotheses("Semiring"),
        Call("doubledDegreeTwo", Call("chronologicalSignature", F.Id("o"), F.Id("w"))),
        Eq, Call("sum", Call("map", Seq(F.Id("e"), Mapsto,
            Call("o", F.Id("e")), Cdot, Sp, Call("o", F.Id("e"))), F.Id("w"))),
        Plus, D(2), Cdot, Sp, Call("orderedPairMoment", Values())));

    private static Formula MagnusFormula() => Disp(Seq(
        Hypotheses("Ring"),
        Call("doubledMagnusDegreeTwo", Call("chronologicalSignature", F.Id("o"), F.Id("w"))),
        Eq, Call("orderedPairMoment", Values()), Minus,
        Call("orderedPairMoment", Call("reverse", Values()))));
}
