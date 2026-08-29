using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationOrder;

internal sealed class TypedPrimeLanguageHierarchyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/ObservationOrder/TypedPrimeLanguageHierarchy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-observation languages have strict comparisons only on "
            + "shared state types.",
        H("Typed Prime-Language Hierarchy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("support-multiplicity-witness"),
                DeclarationHandle.Create(Prefix + "support_multiplicity_witness"),
                H("Equal radical and support do not determine multiplicity"),
                StatementSource.FromAuthor(SupportWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The positive naturals two and four have the same radical and the same "
                            + "prime support, while their exponent tables differ at two.")),
                    Paragraph(Text(
                        "This is the named witness used to refute recovery of valuations from "
                            + "support alone."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("support-strictly-coarser-than-valuation"),
                DeclarationHandle.Create(
                    Prefix + "support_strictly_coarser_than_valuation"),
                H("Support is strictly coarser than valuation"),
                StatementSource.FromAuthor(SupportStrictFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Finite support factors through the canonical prime-exponent language. "
                            + "The reverse factor would identify the exponent tables of two and "
                            + "four, contradicting the named witness.")),
                    Paragraph(Text(
                        "Both readouts have the common state type of positive naturals; no "
                            + "cross-type comparison is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("relative-phase-density-witness"),
                DeclarationHandle.Create(Prefix + "relative_phase_density_witness"),
                H("Equal prime diagonals do not determine relative phase"),
                StatementSource.FromAuthor(PhaseWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The equal-superposition density operator and its Pauli-Z phase flip are "
                            + "positive trace-one matrices with equal diagonal entries.")),
                    Paragraph(Text(
                        "Canonical prime dephasing therefore gives the same matrix, while the "
                            + "full operator readout distinguishes their off-diagonal entries."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-diagonal-strictly-coarser-than-operator"),
                DeclarationHandle.Create(
                    Prefix + "prime_diagonal_strictly_coarser_than_operator"),
                H("Prime-diagonal readout is strictly coarser than operators"),
                StatementSource.FromAuthor(OperatorStrictFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Prime dephasing factors through the full density-operator readout. The "
                            + "reverse factor is impossible because the named phase pair has one "
                            + "dephased output and two distinct operator outputs.")),
                    Paragraph(Text(
                        "This theorem compares readouts only on qubit density states. The source's "
                            + "warning against a transport-free global order remains a metalevel "
                            + "typing statement and is intentionally not encoded."))),
                DescribeRole.Theorem))));

    private static Formula SupportWitnessFormula()
    {
        Formula radical = F.Id("rad");
        Formula support = F.Id("supp");
        Formula valuation = Nu;
        Formula two = D(2);
        Formula four = D(4);
        Formula radicalsEqual = Equal(Call(radical, two), Call(radical, four));
        Formula supportsEqual = Equal(
            Call(support, Call(valuation, two)),
            Call(support, Call(valuation, four)));
        Formula valuationsDiffer = NotEqual(
            Call(valuation, two), Call(valuation, four));

        return Disp(And(radicalsEqual, And(supportsEqual, valuationsDiffer)));
    }

    private static Formula SupportStrictFormula()
    {
        Formula refines = F.Id("Refines");
        Formula support = F.Id("primeSupportLanguage");
        Formula valuation = F.Id("primeExponentLanguage");

        return Disp(And(
            Call(refines, support, valuation),
            Negate(Call(refines, valuation, support))));
    }

    private static Formula PhaseWitnessFormula()
    {
        Formula plus = F.Id("rhoPlus");
        Formula minus = F.Id("rhoMinus");
        Formula diagonal = F.Id("qubitPrimeDiagonalLanguage");
        Formula full = F.Id("qubitOperatorLanguage");
        Formula statesDiffer = NotEqual(plus, minus);
        Formula diagonalsEqual = Equal(Call(diagonal, plus), Call(diagonal, minus));
        Formula operatorsDiffer = NotEqual(Call(full, plus), Call(full, minus));

        return Disp(And(statesDiffer, And(diagonalsEqual, operatorsDiffer)));
    }

    private static Formula OperatorStrictFormula()
    {
        Formula refines = F.Id("Refines");
        Formula diagonal = F.Id("qubitPrimeDiagonalLanguage");
        Formula full = F.Id("qubitOperatorLanguage");

        return Disp(And(
            Call(refines, diagonal, full),
            Negate(Call(refines, full, diagonal))));
    }

    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        Seq(left, Sp, Neq, Sp, right);

    private static Formula Negate(Formula value) =>
        Seq(Neg, Grp(value));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
