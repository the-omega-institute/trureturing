using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Completion;

internal sealed class CommutingCompletionExchangeDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commuting predictive completions exchange order and equal completion by all words.",
        H("Commuting Completion Exchange"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-projection-kernel-is-the-congruence-kernel"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "predictive_projection_kernel"),
                H("The projection kernel is the congruence kernel"),
                StatementSource.FromAuthor(ProjectionKernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The completed readout is the canonical quotient projection from the "
                            + "original state type. Equality of two quotient classes is exactly "
                            + "membership in the predictive setoid relation.")),
                    Paragraph(Text(
                        "Quotient exactness and soundness therefore identify its readout kernel "
                            + "with the existing congruenceKernel construction. This bridge lets "
                            + "a completed interface be supplied to a second completion."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("canonical-normal-words-act-by-two-iterates"),
                DeclarationHandle.Create(DeclarationPrefix + "normal_word_action"),
                H("Canonical normal words act by two iterates"),
                StatementSource.FromAuthor(NormalWordFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A normal word consists of n first-generator letters followed by m "
                            + "second-generator letters. Direct induction evaluates its action "
                            + "as the composite of the corresponding iterates.")),
                    Paragraph(Text(
                        "No commutativity assumption is needed for this representability half, "
                            + "and the proof includes the empty word at n = m = 0."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("commuting-words-have-two-block-normal-forms"),
                DeclarationHandle.Create(DeclarationPrefix + "word_action_normal_form"),
                H("Commuting words have two-block normal forms"),
                StatementSource.FromAuthor(WordNormalizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The generated monoid is represented explicitly by List Bool, the free "
                            + "word carrier on two named generators. Thus the all-word readout "
                            + "does not assume a normal form in its definition.")),
                    Paragraph(Text(
                        "Induction on a word counts its two kinds of letters implicitly. A first "
                            + "letter extends the first iterate, while a second letter commutes "
                            + "past the current first iterate using Mathlib's iterate_left law."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("commuting-completions-exchange-and-equal-all-words"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "commuting_completion_exchange"),
                H("Commuting completions exchange and equal all words"),
                StatementSource.FromAuthor(ExchangeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "KernelEquivalent means literal equality of readout kernel relations. "
                            + "This is the source theorem's mutual-refinement meaning of the "
                            + "equivalence sign, without claiming equality of quotient types.")),
                    Paragraph(Text(
                        "The projection-kernel bridge expands the two completion orders into the "
                            + "two nested congruence kernels. Commuting iterates exchange their "
                            + "indices pointwise, proving equality of those kernels.")),
                    Paragraph(Text(
                        "Word normalization sends every generated word to a pair of iterates, "
                            + "while the canonical normal word realizes every pair. Hence the "
                            + "nested kernel is exactly the kernel of the all-word readout.")),
                    Paragraph(Text(
                        "No finiteness, inhabitedness, decidable equality, or output structure is "
                            + "assumed. Empty and singleton states, identity and constant maps, "
                            + "and the zero-iterate word are checked in the Lean module."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("commutativity-cannot-be-deleted"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "commutativity_hypothesis_is_necessary"),
                H("Commutativity cannot be deleted"),
                StatementSource.FromAuthor(NecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A concrete four-state system distinguishes the two orders. States a "
                            + "and b agree after every G-iterate following every F-iterate, but "
                            + "F after one G-step sends them to differently read states.")),
                    Paragraph(Text(
                        "The two completion kernels are therefore unequal. This proves that the "
                            + "commutativity premise is necessary for the theorem as a uniform "
                            + "statement, rather than merely recording a proof dependency."))),
                DescribeRole.Lemma))));

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

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula ProjectionKernelFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula projection = Apply(F.Id("predictiveProjection"), update, readout);

        return Disp(Seq(
            Forall, Sp, Typed(Seq(state, Comma, Sp, output), TypeUniverse()), Comma, Sp,
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(readout, Arrow(state, output)), Comma, RowBreak, Grp(),
            Apply(F.Id("readoutRelation"), projection), Sp, Eq, Sp,
            Apply(F.Id("congruenceKernel"), update,
                Apply(F.Id("readoutRelation"), readout)), Dot));
    }

    private static Formula NormalWordFormula()
    {
        Formula state = F.Id("X");
        Formula first = F.Id("F");
        Formula second = F.Id("G");
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula word = Apply(F.Id("normalWord"), n, m);

        return Disp(Seq(
            Forall, Sp, Typed(state, TypeUniverse()), Comma, Sp,
            Typed(Seq(first, Comma, Sp, second), Arrow(state, state)), Comma, Sp,
            Typed(Seq(n, Comma, Sp, m), F.Id("Nat")), Comma, RowBreak, Grp(),
            Apply(F.Id("wordAction"), first, second, word), Sp, Eq, Sp,
            Apply(F.Id("iterate"), first, n), Sp, Circ, Sp,
            Apply(F.Id("iterate"), second, m), Dot));
    }

    private static Formula WordNormalizationFormula()
    {
        Formula state = F.Id("X");
        Formula first = F.Id("F");
        Formula second = F.Id("G");
        Formula word = F.Id("w");
        Formula n = F.Id("n");
        Formula m = F.Id("m");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(state, TypeUniverse()), Comma, Sp,
            Typed(Seq(first, Comma, Sp, second), Arrow(state, state)), Comma,
            RowBreak, Grp(),
            Apply(F.Id("Commute"), first, second), Sp, Rightarrow, Sp,
            Forall, Sp, Typed(word, Apply(F.Id("List"), F.Id("Bool"))), Comma,
            RowBreak, Grp(),
            Exists, Sp, Typed(Seq(n, Comma, Sp, m), F.Id("Nat")), Comma, Sp,
            Apply(F.Id("wordAction"), first, second, word), Sp, Eq, Sp,
            Apply(F.Id("iterate"), first, n), Sp, Circ, Sp,
            Apply(F.Id("iterate"), second, m), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ExchangeFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula first = F.Id("F");
        Formula second = F.Id("G");
        Formula readout = F.Id("q");
        Formula firstThenSecond = Apply(
            F.Id("C"), first, Apply(F.Id("C"), second, readout));
        Formula secondThenFirst = Apply(
            F.Id("C"), second, Apply(F.Id("C"), first, readout));
        Formula generated = Apply(F.Id("Generated"), first, second);
        Formula allWords = Apply(F.Id("C"), generated, readout);

        Formula conclusion = new Formula.Logic(
            Apply(F.Id("KernelEquivalent"), firstThenSecond, secondThenFirst),
            FormulaLogicOperator.And,
            Apply(F.Id("KernelEquivalent"), secondThenFirst, allWords));
        Formula theorem = new Formula.Logic(
            Apply(F.Id("Commute"), first, second),
            FormulaLogicOperator.Implies,
            conclusion);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", TypeUniverse()),
                Bound("O", TypeUniverse()),
                Bound("F", Arrow(state, state)),
                Bound("G", Arrow(state, state)),
                Bound("q", Arrow(state, output)),
            ],
            theorem));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula NecessityFormula()
    {
        Formula first = F.Id("counterexampleF");
        Formula second = F.Id("counterexampleG");
        Formula readout = F.Id("counterexampleReadout");
        Formula firstThenSecond = Apply(
            F.Id("C"), first, Apply(F.Id("C"), second, readout));
        Formula secondThenFirst = Apply(
            F.Id("C"), second, Apply(F.Id("C"), first, readout));

        return Disp(Seq(
            Neg, Sp, Apply(F.Id("Commute"), first, second), Sp, Land, Sp,
            Neg, Sp,
            Apply(F.Id("KernelEquivalent"), firstThenSecond, secondThenFirst), Dot));
    }
}
