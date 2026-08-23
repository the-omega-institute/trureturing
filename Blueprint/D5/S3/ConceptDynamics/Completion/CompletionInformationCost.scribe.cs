using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Completion;

internal sealed class CompletionInformationCostDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Completion/CompletionInformationCost.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completion cost is conditional entropy on supported concept fibers, not a global "
            + "factorization criterion.",
        H("Information Cost of Concept Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-cost-is-conditional-entropy"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "completion_information_cost"),
                H("Completion cost is conditional entropy"),
                StatementSource.FromAuthor(CompletionCostFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a normalized nonnegative mass be given on a finite source, with a "
                            + "concept readout and a target readout. Their completion law is the "
                            + "joint distribution obtained by sending each source point to its "
                            + "pair of readout values.")),
                    Paragraph(Text(
                        "The first marginal of this joint law is exactly the distribution of the "
                            + "concept readout. The finite entropy chain rule therefore identifies "
                            + "the entropy gained by adjoining the target coordinate with the "
                            + "target's entropy conditional on the current concept.")),
                    Paragraph(Text(
                        "Only concept fibers carrying positive mass contribute to this cost. No "
                            + "strict positivity assumption is imposed on individual source "
                            + "points or concept fibers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-cost-does-not-force-global-factorization"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "zero_conditional_entropy_not_global_factorization"),
                H("Zero completion cost need not give a global target factor"),
                StatementSource.FromAuthor(NoGlobalFactorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On a three-point source, put all mass on the first point, use the constant "
                            + "false concept readout, and let the target be false on the first two "
                            + "points and true on the third. The only supported conditional slice "
                            + "is a point mass, so its conditional entropy is zero.")),
                    Paragraph(Text(
                        "The two zero-mass points have the same concept value but different target "
                            + "values. Consequently no Boolean function can recover the target from "
                            + "the concept on the whole source type. Zero completion cost therefore "
                            + "controls supported fibers only, not unsupported points."))),
                DescribeRole.Lemma))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula FiniteThree() =>
        Call("Fin", D(3));

    private static Formula RealNumbers() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula CompletionLaw(
        Formula mass,
        Formula concept,
        Formula target) =>
        Call("completionLaw", mass, concept, target);

    private static Formula ShannonEntropy(Formula law) =>
        Seq(Operatorname, Grp(F.Id("shannonEntropy")), Open, law, Close);

    private static Formula ConditionalEntropy(Formula law) =>
        Seq(Operatorname, Grp(F.Id("conditionalEntropy")), Open, law, Close);

    private static Formula CompletionCostFormula()
    {
        Formula source = F.Id("X");
        Formula conceptType = F.Id("C");
        Formula targetType = F.Id("K");
        Formula mass = F.Id("mass");
        Formula concept = F.Id("concept");
        Formula target = F.Id("target");
        Formula x = F.Id("x");
        Formula joint = CompletionLaw(mass, concept, target);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, source, Comma, Sp, conceptType, Comma, Sp, targetType, Esc,
            OpenBracket,
            Operatorname, Grp(F.Id("Fintype")), Open, source, Close,
            CloseBracket, Sp,
            OpenBracket,
            Operatorname, Grp(F.Id("Fintype")), Open, conceptType, Close,
            CloseBracket, Sp,
            OpenBracket,
            Operatorname, Grp(F.Id("Fintype")), Open, targetType, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            Typed(mass, Arrow(source, RealNumbers())), Comma, Sp,
            Typed(concept, Arrow(source, conceptType)), Comma, Sp,
            Typed(target, Arrow(source, targetType)), Comma, RowBreak, Grp(),
            Open,
            Forall, Sp, x, Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(mass, x),
            Close, Sp, Land, Sp,
            Sum, Underscore, Grp(x), Apply(mass, x), Sp, Eq, Sp, D(1),
            Sp, Rightarrow, Sp, RowBreak, Grp(),
            ShannonEntropy(joint), Sp, Minus, Sp,
            ShannonEntropy(Call("pushforward", concept, mass)), Sp, Eq, Sp,
            ConditionalEntropy(joint), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula NoGlobalFactorFormula()
    {
        Formula source = FiniteThree();
        Formula mass = F.Id("mass");
        Formula concept = F.Id("concept");
        Formula target = F.Id("target");
        Formula factor = F.Id("factor");
        Formula x = F.Id("x");
        Formula y = F.Id("y");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp,
            Typed(mass, Arrow(source, RealNumbers())), Comma, Sp,
            Typed(
                Seq(concept, Comma, Sp, target),
                Arrow(source, F.Id("Bool"))),
            Comma, RowBreak, Grp(),
            Open,
            Forall, Sp, x, Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(mass, x),
            Close, Sp, Land, Sp,
            Sum, Underscore, Grp(x), Apply(mass, x), Sp, Eq, Sp, D(1),
            Sp, Land, Sp, RowBreak, Grp(),
            ConditionalEntropy(CompletionLaw(mass, concept, target)),
            Sp, Eq, Sp, D(0), Sp, Land, Sp, RowBreak, Grp(),
            Open, Neg, Sp, Exists, Sp,
            Typed(factor, Arrow(F.Id("Bool"), F.Id("Bool"))), Comma, Sp,
            target, Sp, Eq, Sp, factor, Sp, Circ, Sp, concept,
            Close, Sp, Land, Sp, RowBreak, Grp(),
            Exists, Sp, Typed(Seq(x, Comma, Sp, y), source), Comma, Sp,
            Apply(mass, x), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Apply(mass, y), Sp, Eq, Sp, D(0), Sp, Land, Sp, RowBreak, Grp(),
            Apply(concept, x), Sp, Eq, Sp, Apply(concept, y), Sp, Land, Sp,
            Apply(target, x), Sp, Neq, Sp, Apply(target, y), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
