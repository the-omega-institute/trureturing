using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Aggregation;

internal sealed class SymmetricTieImpossibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Anonymous and candidate-neutral deterministic choice cannot resolve a two-voter tie.",
        H("Symmetric Tie Impossibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symmetric-tie-impossibility"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Aggregation/SymmetricTieImpossibility."
                        + "symmetric_tie_impossibility"),
                H("No anonymous neutral deterministic tie rule"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Candidates are the exact two-element Boolean carrier and profiles are "
                            + "ordered pairs of two voter choices. A rule of type Bool times Bool "
                            + "to Bool is publicly total, single-valued, and always selects one "
                            + "of the two candidates, which is deterministic completeness.")),
                    Paragraph(Text(
                        "Anonymity says exchanging the two profile coordinates leaves the result "
                            + "unchanged. Candidate neutrality says complementing both choices "
                            + "complements the selected candidate.")),
                    Paragraph(Text(
                        "At the tied profile (false, true), candidate exchange produces exactly "
                            + "the voter-exchanged profile (true, false). The two symmetry laws "
                            + "therefore force the selected Boolean value to equal its own "
                            + "complement, contradicting Mathlib's exact Bool.not_ne_self lemma.")),
                    Paragraph(Text(
                        "The carrier and both exchanges occur directly in the public statement; "
                            + "no source object is defined from the desired contradiction. "
                            + "Separate compiling witnesses show that each symmetry law alone is "
                            + "satisfiable by a total deterministic rule."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Pair(Formula first, Formula second) =>
        Seq(Open, first, Comma, Sp, second, Close);

    private static Formula Component(Formula pair, byte index) =>
        new Formula.Subscript(pair, D(index));

    private static Formula TheoremFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula profileType = Call("Prod", boolean, boolean);
        Formula rule = F.Id("F");
        Formula profile = F.Id("p");
        Formula first = Component(profile, 1);
        Formula second = Component(profile, 2);
        Formula voterSwap = Pair(second, first);
        Formula candidateSwap = Pair(Call("not", first), Call("not", second));
        Formula anonymity = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("p"),
            profileType,
            Equal(Apply(rule, voterSwap), Apply(rule, profile)));
        Formula neutrality = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("p"),
            profileType,
            Equal(
                Apply(rule, candidateSwap),
                Call("not", Apply(rule, profile))));
        Formula ruleType = Arrow(profileType, boolean);
        Formula simultaneousRule = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("F"),
            ruleType,
            And(anonymity, neutrality));

        return Disp(new Formula.Not(simultaneousRule));
    }
}
