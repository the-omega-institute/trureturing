using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;

internal sealed class MinimumSafeObservationAlphabetDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Agency/MinimumSafeObservationAlphabet."
            + "minimum_safe_observation_alphabet";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Safe-compatible partitions determine the exact minimum safe observation alphabet.",
        H("Minimum Safe Observation Alphabet"),
        Blocks(Describe.Lean(
            DescribeId.Create("minimum-safe-observation-alphabet"),
            DeclarationHandle.Create(Declaration),
            H("Safe partitions and deterministic safe observers have the same minimum size"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A safe-compatible partition is represented by a surjective readout into "
                        + "Fin k. Surjectivity ensures that all k observation values occur, and "
                        + "each effective fiber must admit one action legal at every state in "
                        + "that fiber.")),
                Paragraph(Text(
                    "The repository's deterministic safe-policy existence theorem identifies "
                        + "this fiber condition with a policy on the effective observation "
                        + "values, for each fixed k.")),
                Paragraph(Text(
                    "Transporting that equivalence through IsLeast proves both required halves: "
                        + "the minimum partition size is attained by a safe observer, and every "
                        + "safe observer uses at least that many realized values."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula fullStateType = F.Id("X");
        Formula actionType = F.Id("A");
        Formula legal = F.Id("Legal");
        Formula alphabetSize = F.Id("k");
        Formula chiSafe = Seq(F.Id("chi"), Underscore, Grp(F.Id("safe")));
        Formula naturalNumbers = Seq(Mathbb, Grp(F.Id("N")));
        Formula safePartitionSizes = Seq(
            OpenBrace,
            alphabetSize, Sp, InMacro, Sp, naturalNumbers, Sp, Mid, Sp,
            Call("SafeCompatiblePartition", legal, alphabetSize),
            CloseBrace);
        Formula safeObserverSizes = Seq(
            OpenBrace,
            alphabetSize, Sp, InMacro, Sp, naturalNumbers, Sp, Mid, Sp,
            Call("SupportsDeterministicSafePolicy", legal, alphabetSize),
            CloseBrace);

        return Disp(Seq(
            Forall, Sp,
            fullStateType, Comma, Sp, actionType, Sp, InMacro, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            legal, Colon, Sp,
            Arrow(fullStateType, Call("Set", actionType)), Comma, Sp,
            chiSafe, Sp, InMacro, Sp, naturalNumbers, Comma, RowBreak, Grp(),
            Call("IsLeast", safePartitionSizes, chiSafe), Sp, Iff, Sp,
            Call("IsLeast", safeObserverSizes, chiSafe), Dot));
    }
}
