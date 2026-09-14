using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class FlatPhaseConjugationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entrywise unit modulus reduces the diagonal of normalized phase conjugation to a conjugate sum.",
        H("Flat Phase Conjugation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("flat-phase-conjugation"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/FlatPhaseConjugation.flatPhaseConjugation"),
                H("The normalized entrywise kernel"),
                StatementSource.FromAuthor(Inputs(Seq(
                    Forall, Sp, F.Id("i"), Comma, F.Id("l"), Colon, Iota, Comma, Sp,
                    Entry(F.Id("i"), F.Id("l")), Eq, Normalization(),
                    Sum, Underscore, Grp(F.Id("j"), Colon, Kappa),
                    Apply("H", F.Id("i"), F.Id("j")),
                    Conjugate(Apply("d", F.Id("j"))),
                    Conjugate(Apply("H", F.Id("l"), F.Id("j")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary index types iota and kappa with Fintype kappa, the kernel is defined entrywise for a complex matrix H and complex profiles c and d. The inverse cardinality is the complex field inverse, including when kappa is empty."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("flat-phase-conjugation-diagonal"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/FlatPhaseConjugation.flatPhaseConjugation_diagonal"),
                H("Unit modulus simplifies each diagonal entry"),
                StatementSource.FromAuthor(Inputs(Seq(
                    UnitEntries(), Implies, Sp, Forall, Sp, F.Id("i"), Colon, Iota, Comma, Sp,
                    Entry(F.Id("i"), F.Id("i")), Eq, Normalization(),
                    Sum, Underscore, Grp(F.Id("j"), Colon, Kappa),
                    Conjugate(Apply("d", F.Id("j")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If every entry of H has squared modulus one, each diagonal entry equals the inverse cardinality times c at that index times the sum of the conjugates of d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("flat-phase-conjugation-diagonal-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/FlatPhaseConjugation.flatPhaseConjugation_diagonal_zero"),
                H("A zero-sum profile cancels a chosen diagonal entry"),
                StatementSource.FromAuthor(Inputs(Seq(
                    UnitEntries(), Land, Sp, ZeroSum(), Implies, Sp,
                    Forall, Sp, F.Id("i"), Colon, Iota, Comma, Sp,
                    Entry(F.Id("i"), F.Id("i")), Eq, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under entrywise squared modulus one for H and a zero sum for d, the diagonal entry at any supplied index i is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("flat-phase-conjugation-zero-diagonal"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/FlatPhaseConjugation.flatPhaseConjugation_zero_diagonal"),
                H("The whole diagonal vanishes pointwise"),
                StatementSource.FromAuthor(Inputs(Seq(
                    UnitEntries(), Land, Sp, ZeroSum(), Implies, Sp,
                    Forall, Sp, F.Id("i"), Colon, Iota, Comma, Sp,
                    Entry(F.Id("i"), F.Id("i")), Eq, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same hypotheses give the universally quantified zero-diagonal statement by applying the single-entry theorem at each index."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var parts = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) { parts.Add(Comma); parts.Add(Sp); }
            parts.Add(arguments[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }

    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Conjugate(Formula value) => Seq(Overline, Grp(value));
    private static Formula Entry(Formula i, Formula l) =>
        Apply("flatPhaseConjugation", F.Id("H"), F.Id("c"), F.Id("d"), i, l);
    private static Formula Normalization() => Seq(
        Apply("card", Kappa), Caret, Grp(Minus, D(1)), Apply("c", F.Id("i")));
    private static Formula UnitEntries() => Seq(
        Open, Forall, Sp, F.Id("a"), Colon, Iota, Comma,
        Forall, Sp, F.Id("j"), Colon, Kappa, Comma,
        Apply("normSq", Apply("H", F.Id("a"), F.Id("j"))), Eq, D(1), Close);
    private static Formula ZeroSum() => Seq(
        Open, Sum, Underscore, Grp(F.Id("j"), Colon, Kappa),
        Apply("d", F.Id("j")), Eq, D(0), Close);
    private static Formula Inputs(Formula conclusion) => Disp(Seq(
        Forall, Sp, Iota, Comma, Kappa, Colon, F.Id("Type"), Comma,
        Apply("Fintype", Kappa), Implies, Sp,
        Forall, Sp, F.Id("H"), Colon, Apply("Matrix", Iota, Kappa, ComplexType()), Comma,
        Forall, Sp, F.Id("c"), Colon, Iota, To, Sp, ComplexType(), Comma,
        Forall, Sp, F.Id("d"), Colon, Kappa, To, Sp, ComplexType(), Comma, Sp,
        conclusion, Dot));
}
