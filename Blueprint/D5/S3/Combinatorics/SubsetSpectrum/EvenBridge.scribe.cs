using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubsetSpectrum;

internal sealed class EvenBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first moment and complementation recover the full spectrum from its even part in odd length.",
        H("Even and full subset spectra"),
        Blocks(
            Definition("even-subsets", "evenSubsets", "Even index subsets",
                "For a finite index set s, evenSubsets s consists of its subsets with even cardinality."),
            Definition("odd-subsets", "oddSubsets", "Odd index subsets",
                "For a finite index set s, oddSubsets s consists of its subsets with odd cardinality."),
            Definition("even-spectrum", "evenSubsetSums", "The even occurrence spectrum",
                "For b indexed by s, each even index subset contributes one occurrence of its coefficient sum. "
                + "Equal numerical sums from different subsets remain separate occurrences; zero coefficients "
                + "and repeated coefficients are allowed."),
            Definition("odd-spectrum", "oddSubsetSums", "The odd occurrence spectrum",
                "Each odd index subset contributes one occurrence of its coefficient sum."),
            Definition("full-spectrum", "fullSubsetSums", "The full occurrence spectrum",
                "Each index subset, including the empty set exactly once, contributes one occurrence of its sum."),
            Describe.Lean(DescribeId.Create("parity-counts"), DeclarationHandle.Create(Prefix + "parity_counts"),
                H("Both parity classes have half the subsets"), StatementSource.FromAuthor(Disp(ParityCountsFormula())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Every nonempty finite index set has equally many even and odd subsets, each contributing one to its real-valued count."))),
                DescribeRole.Theorem),
            Theorem("even-first-moment", "even_first_moment", "The even incidence first moment",
                "If s has at least two indices, summing the even spectrum gives "
                + "2^(|s|-2) times the sum of the coefficients. Inserting one index splits "
                + "subsets into those containing it and those avoiding it, interchanges the two "
                + "parities in the containing part, and gives the cardinal and weighted recurrences."),
            Theorem("odd-reflection", "odd_spectrum_reflection", "Complementation reflects the even spectrum",
                "For an odd finite index universe and total coefficient sum B, the odd spectrum "
                + "is the multiset image of the even spectrum under x ↦ B-x. Complementation "
                + "is a bijection on index subsets, so this equality preserves multiplicities "
                + "even when several subsets have the same sum."),
            Theorem("even-determines-full", "even_spectrum_determines_full", "Even equality determines full equality",
                "Let m be odd and at least three, and let b,c be arbitrary real coefficient families "
                + "on Fin m. Equality of their even occurrence spectra implies equality of their "
                + "total coefficient sums and equality of their full occurrence spectra. The "
                + "positive first-moment factor determines the common total; reflection then "
                + "recovers both odd spectra, and adjoining the even and odd parts recovers the full spectra.")),
        []));

    private static DocumentBlock Definition(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula ParityCountsFormula()
    {
        var a = F.Id("A"); var s = F.Id("s");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        Formula Op(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
        Formula Parenthesized(Formula value) => Seq(Open, value, Close);
        Formula Count(string name) => Seq(new Formula.Subscript(Sum, Seq(F.Id("t"), InMacro, Op(name, s))), Parenthesized(Seq(D(1), Colon, real)));
        var exponent = new Formula.Binary(new Formula.Apply(Seq(Operatorname, Grp(F.Id("Finset"), Dot, F.Id("card"))), [s]), FormulaBinaryOperator.Subtract, D(1));
        var half = new Formula.Power(Parenthesized(Seq(D(2), Colon, real)), exponent);
        var statement = new Formula.Logic(Parenthesized(Equal(Count("evenSubsets"), half)), FormulaLogicOperator.And, Parenthesized(Equal(Count("oddSubsets"), half)));
        var implication = new Formula.Logic(new Formula.Apply(Seq(Operatorname, Grp(F.Id("Finset"), Dot, F.Id("Nonempty"))), [s]), FormulaLogicOperator.Implies, Parenthesized(statement));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("A"), Seq(F.Id("Type"), Star),
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("s"), Op("Finset", a), implication));
    }

}
