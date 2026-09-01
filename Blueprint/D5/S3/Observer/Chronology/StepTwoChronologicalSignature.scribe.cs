using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class StepTwoChronologicalSignatureDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/StepTwoChronologicalSignature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Step-two signatures obey Chen concatenation and the degree-two BCH "
            + "law.",
        H("Step-Two Chronological Signature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("step-two-signature"),
                DeclarationHandle.Create(Prefix + "StepTwoSignature"),
                H("Step-two signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A step-two signature stores degree one together with twice degree two, "
                        + "so the construction requires no division by two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("event-signature"),
                DeclarationHandle.Create(Prefix + "eventSignature"),
                H("Single-event signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One event contributes its algebra value at degree one and its square "
                        + "to doubled degree two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chronological-signature"),
                DeclarationHandle.Create(Prefix + "chronologicalSignature"),
                H("Chronological word signature"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signature of a list composes single-event signatures from left to "
                        + "right in operational chronology."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chen-append"),
                DeclarationHandle.Create(Prefix + "chronological_signature_append"),
                H("Step-two Chen identity"),
                StatementSource.FromAuthor(AppendFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signature of an earlier word followed by a later word is their "
                        + "chronological signature product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("degree-one"),
                DeclarationHandle.Create(Prefix + "chronological_signature_degree_one"),
                H("Degree one forgets chronology"),
                StatementSource.FromAuthor(DegreeOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Degree one is the ordinary sum of all observed event values and is "
                        + "therefore insensitive to their order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("doubled-magnus"),
                DeclarationHandle.Create(Prefix + "doubledMagnusDegreeTwo"),
                H("Doubled degree-two Magnus coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Subtracting the square of degree one from doubled degree two extracts "
                        + "the doubled logarithmic coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bch-mul"),
                DeclarationHandle.Create(Prefix + "doubled_magnus_degree_two_mul"),
                H("Degree-two BCH law"),
                StatementSource.FromAuthor(BchMulFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The logarithmic coordinate of a product is the sum of the two "
                        + "coordinates plus the commutator of their degree-one parts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bch-append"),
                DeclarationHandle.Create(Prefix + "doubled_magnus_degree_two_append"),
                H("Chronological BCH append law"),
                StatementSource.FromAuthor(BchAppendFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Combining Chen concatenation with the logarithmic coordinate gives the "
                        + "step-two BCH formula for two event words."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-event-commutator"),
                DeclarationHandle.Create(
                    Prefix + "doubled_magnus_two_events_eq_commutator"),
                H("Two-event Magnus coordinate is the commutator"),
                StatementSource.FromAuthor(TwoEventsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a chronology containing exactly two events, the doubled "
                        + "degree-two logarithmic coordinate is their ring commutator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-event-swap"),
                DeclarationHandle.Create(Prefix + "doubled_magnus_two_events_swap"),
                H("Two-event orientation reversal"),
                StatementSource.FromAuthor(SwapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reversing two events negates the degree-two chronological defect."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("commuting-zero"),
                DeclarationHandle.Create(
                    Prefix + "doubled_magnus_two_events_eq_zero_of_commute"),
                H("Commuting events have zero defect"),
                StatementSource.FromAuthor(CommuteZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A commuting event pair has no degree-two chronological memory."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity")),
        ]));

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

    private static Formula Sig(Formula word) =>
        Call("chronologicalSignature", F.Id("f"), word);

    private static Formula Mag(Formula signature) =>
        Call("doubledMagnusDegreeTwo", signature);

    private static Formula PairWord(Formula first, Formula second) =>
        Seq(OpenBracket, first, Comma, Sp, second, CloseBracket);

    private static Formula Joined() =>
        Call("append", F.Id("P"), F.Id("S"));

    private static Formula AppendFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("P"), Comma, Sp, F.Id("S"),
        Comma, Sp,
        Sig(Joined()), Sp, Eq, Sp,
        Sig(F.Id("P")), Sp, Cdot, Sp, Sig(F.Id("S")), Dot));

    private static Formula DegreeOneFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("L"), Comma, Sp,
        Call("degreeOne", Sig(F.Id("L"))), Sp, Eq, Sp,
        Call("sum", Call("map", F.Id("f"), F.Id("L"))), Dot));

    private static Formula BchMulFormula() => Disp(Seq(
        Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp,
        Mag(Seq(F.Id("a"), Sp, Cdot, Sp, F.Id("b"))), Sp, Eq, Sp,
        Mag(F.Id("a")), Sp, Plus, Sp, Mag(F.Id("b")), Sp, Plus, Sp,
        Call("commutator",
            Call("degreeOne", F.Id("a")), Call("degreeOne", F.Id("b"))),
        Dot));

    private static Formula BchAppendFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("P"), Comma, Sp, F.Id("S"),
        Colon,
        RowBreak, Grp(),
        Mag(Sig(Joined())), Sp, Eq, Sp,
        Mag(Sig(F.Id("P"))), Sp, Plus, Sp, Mag(Sig(F.Id("S"))), Sp, Plus, Sp,
        Call("commutator",
            Call("degreeOne", Sig(F.Id("P"))),
            Call("degreeOne", Sig(F.Id("S")))), Dot,
        End, Grp(F.Id("gathered"))));

    private static Formula TwoEventsFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("p"), Comma, Sp, F.Id("q"),
        Comma, Sp,
        Mag(Sig(PairWord(F.Id("p"), F.Id("q")))), Sp, Eq, Sp,
        Call("commutator",
            Call("f", F.Id("p")), Call("f", F.Id("q"))), Dot));

    private static Formula SwapFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("p"), Comma, Sp, F.Id("q"),
        Comma, Sp,
        Mag(Sig(PairWord(F.Id("q"), F.Id("p")))), Sp, Eq, Sp,
        Minus, Mag(Sig(PairWord(F.Id("p"), F.Id("q")))), Dot));

    private static Formula CommuteZeroFormula() => Disp(Seq(
        Forall, Sp, F.Id("f"), Comma, Sp, F.Id("p"), Comma, Sp, F.Id("q"),
        Comma, Sp,
        Call("f", F.Id("p")), Sp, Cdot, Sp, Call("f", F.Id("q")),
        Sp, Eq, Sp,
        Call("f", F.Id("q")), Sp, Cdot, Sp, Call("f", F.Id("p")),
        Sp, Rightarrow, Sp,
        Mag(Sig(PairWord(F.Id("p"), F.Id("q")))), Sp, Eq, Sp, D(0), Dot));
}
