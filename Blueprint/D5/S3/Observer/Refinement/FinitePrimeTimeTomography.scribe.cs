using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Refinement;

internal sealed class FinitePrimeTimeTomographyDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/Refinement/FinitePrimeTimeTomography.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete prime-time separation on a finite state space has a finite witness.",
        H("Finite Prime-Time Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("separated-by-complete-observation"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "SeparatedByCompleteObservation"),
                H("Complete observation separates through the common finite-window kernel"),
                StatementSource.FromAuthor(CompleteObservationDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A readout family and transition separate states completely exactly when "
                        + "the intersection of the indistinguishability relations over every "
                        + "finite index set and every natural time horizon lies in the equality "
                        + "diagonal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("complete-separation-has-a-finite-window"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "finite_prime_time_tomography"),
                H("Complete separation has a finite window"),
                StatementSource.FromAuthor(FiniteTomographyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The relations arising from finite index sets and time horizons form "
                            + "a downward-directed family: the union of two index sets and "
                            + "the maximum of two horizons refine both original windows.")),
                    Paragraph(Text(
                        "When the state space is finite, its set of binary relations is "
                            + "finite. A minimal member of the directed family is contained "
                            + "in every member, hence in the complete intersection and the "
                            + "equality diagonal. No primality or finite-output hypothesis "
                            + "is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complete-separation-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "complete_separation_is_necessary"),
                H("Complete separation is necessary"),
                StatementSource.FromAuthor(CompleteSeparationNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the two Boolean states, let every indexed readout be constant "
                            + "and let the transition be the identity. The pair of distinct "
                            + "states remains in every finite-window kernel.")),
                    Paragraph(Text(
                        "It therefore remains in the complete intersection as well. Neither "
                            + "complete separation nor a separating finite window holds, "
                            + "showing that the separation premise cannot be removed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finiteness-is-necessary"),
                DeclarationHandle.Create(DeclarationPrefix + "finiteness_is_necessary"),
                H("Finiteness is necessary"),
                StatementSource.FromAuthor(FinitenessNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the natural numbers, the threshold readout at index i records "
                            + "whether x is below i. All indices together separate distinct "
                            + "states, even with identity dynamics.")),
                    Paragraph(Text(
                        "For any finite index set, its maximum and the next natural number "
                            + "give identical threshold values at every selected index. Thus "
                            + "no finite prime-time window separates the infinite carrier."))),
                DescribeRole.Theorem))));

    private static Formula Complete(Formula readout, Formula transition) =>
        Call("SeparatedByCompleteObservation", readout, transition);

    private static Formula Diagonal(Formula state) =>
        Call("diagonal", state);

    private static Formula Indist(
        Formula indices,
        Formula horizon,
        Formula readout,
        Formula transition) =>
        Call("Indist", indices, horizon, readout, transition);

    private static Formula CompleteObservationDefinitionFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula transition = F.Id("T");
        Formula indices = F.Id("J");
        Formula horizon = F.Id("m");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula commonKernel = Call(
            "iInter",
            Seq(indices, Colon, Sp, Call("Finset", naturals)),
            Seq(horizon, Colon, Sp, naturals),
            Indist(indices, horizon, readout, transition));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, type, Comma, RowBreak, Grp(),
            readout, Colon, Sp, new Formula.TypeArrow(
                naturals, new Formula.TypeArrow(state, output)), Comma, Sp,
            transition, Colon, Sp, new Formula.TypeArrow(state, state), Comma, RowBreak, Grp(),
            Complete(readout, transition), Sp, Iff, Sp,
            commonKernel, Sp, Subseteq, Sp, Diagonal(state), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FiniteTomographyFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula transition = F.Id("T");
        Formula indices = F.Id("J");
        Formula horizon = F.Id("m");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Open, state, Close,
            CloseBracket, Comma, Sp,
            readout, Colon, Sp, naturals, Sp, To, Sp, state, Sp, To, Sp, output,
            Comma, Sp, transition, Colon, Sp, state, Sp, To, Sp, state, Comma,
            RowBreak, Grp(),
            Complete(readout, transition), Sp, Rightarrow, Sp,
            Exists, Sp, indices, Colon, Sp, Call("Finset", naturals), Comma, Sp,
            horizon, Colon, Sp, naturals, Comma,
            RowBreak, Grp(),
            Indist(indices, horizon, readout, transition), Sp, Subseteq, Sp,
            Diagonal(state), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula CompleteSeparationNecessaryFormula()
    {
        Formula constant = F.Id("c");
        Formula identity = F.Id("id");
        Formula indices = F.Id("J");
        Formula horizon = F.Id("m");
        Formula booleans = Seq(Operatorname, Grp(F.Id("Bool")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));

        return Disp(Seq(
            Neg, Complete(constant, identity), Sp, Land, Sp,
            Neg, Exists, Sp, indices, Colon, Sp, Call("Finset", naturals),
            Comma, Sp, horizon, Colon, Sp, naturals, Comma, Sp,
            Indist(indices, horizon, constant, identity), Sp, Subseteq, Sp,
            Diagonal(booleans), Dot));
    }

    private static Formula FinitenessNecessaryFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula threshold = F.Id("theta");
        Formula identity = F.Id("id");
        Formula indices = F.Id("J");
        Formula horizon = F.Id("m");

        return Disp(Seq(
            Neg, Operatorname, Grp(F.Id("Finite")), Open, naturals, Close,
            Sp, Land, Sp, Complete(threshold, identity), Sp, Land, Sp,
            Neg, Exists, Sp, indices, Colon, Sp, Call("Finset", naturals),
            Comma, Sp, horizon, Colon, Sp, naturals, Comma, Sp,
            Indist(indices, horizon, threshold, identity), Sp, Subseteq, Sp,
            Diagonal(naturals), Dot));
    }
}
