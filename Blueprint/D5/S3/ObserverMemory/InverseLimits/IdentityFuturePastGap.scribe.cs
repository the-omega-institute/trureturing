using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimits;

internal sealed class IdentityFuturePastGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identity readout retains every finite state, while infinite backward orbits retain only periodic states.",
        H("Identity Future and Past Gap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("identity-future-completion-exceeds-the-past-core"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimits/IdentityFuturePastGap."
                        + "identity_future_completion_exceeds_past_core"),
                H("Identity future completion exceeds the past core"),
                StatementSource.FromAuthor(IdentityFuturePastFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite state type and tau a self-map that is not a "
                            + "permutation. Define R for a readout by equality of every future "
                            + "readout along the iterates of tau, and define Z as the quotient "
                            + "of Y by R.")),
                    Paragraph(Text(
                        "For the identity readout, coordinate zero already separates states. "
                            + "Thus R is equality and the quotient completion Z is equivalent "
                            + "to Y.")),
                    Paragraph(Text(
                        "An infinite backward orbit is a sequence whose next coordinate maps "
                            + "to the current coordinate. Coordinate-zero evaluation identifies "
                            + "these orbits with the positive-period points P. Since tau is not "
                            + "a permutation, P has strictly fewer elements than Y, yielding "
                            + "the strict cardinality gap between the past and future completions.")),
                    Paragraph(Text(
                        "The proof directly applies the repository's canonical backward-orbit "
                            + "bijection and Mathlib's kernel-range equivalence, finite "
                            + "periodic-point characterization, and cardinality transport. "
                            + "Repository and pinned-Mathlib searches found no theorem combining "
                            + "all five clauses. Neither Loogle nor LeanSearch was installed in "
                            + "the worker environment."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Card(Formula type) =>
        Apply(Seq(Operatorname, Grp(F.Id("card"))), type);

    private static Formula IdentityFuturePastFormula()
    {
        Formula carrier = F.Id("Y");
        Formula y = F.Id("y");
        Formula yPrime = F.Id("z");
        Formula identity = Seq(Operatorname, Grp(F.Id("id")));
        Formula relation = Subscript(F.Id("R"), identity);
        Formula futureCompletion = Subscript(F.Id("Z"), identity);
        Formula pastCompletion = Seq(
            Subscript(F.Id("X"), Tau), Caret, Grp(Minus));
        Formula periodicCore = Subscript(F.Id("P"), Tau);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, carrier, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, carrier,
            CloseBracket, Comma, RowBreak,
            Tau, Colon, Sp, carrier, Sp, To, Sp, carrier, Comma, Sp,
            Neg, Sp, Operatorname, Grp(F.Id("Bijective")), Open, Tau, Close,
            Sp, Rightarrow, RowBreak,
            Open, Forall, Sp, y, Comma, Sp, yPrime, InMacro, Sp, carrier,
            Comma, Sp, Apply(relation, y, yPrime), Sp, Leftrightarrow, Sp,
            y, Sp, Eq, Sp, yPrime, Close, Sp, Land, RowBreak,
            futureCompletion, Sp, Equiv, Sp, carrier, Sp, Land, RowBreak,
            pastCompletion, Sp, Equiv, Sp, periodicCore, Sp, Land, RowBreak,
            Card(periodicCore), Sp, Lt, Sp, Card(carrier), Sp, Land, RowBreak,
            Card(pastCompletion), Sp, Lt, Sp, Card(futureCompletion), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
