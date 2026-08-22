using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting.Quotients;

internal sealed class SplitSurjectionFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fiber-constant map factors uniquely through a split surjection.",
        H("Split Surjection Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("split-surjection-factorization"),
                DeclarationHandle.Create(
                    "D5/S0/Rewriting/Quotients/SplitSurjectionFactorization."
                        + "split_surjection_factorization"),
                H("Fiber constancy and a section give unique factorization"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let qPrime map X to BPrime, let q map X to B, and let s be a "
                            + "section of qPrime. Fiber constancy says that q takes equal "
                            + "values whenever qPrime does.")),
                    Paragraph(Text(
                        "The unique factor sends bPrime to q(s(bPrime)). The section equation "
                            + "and fiber constancy prove that composing this factor with "
                            + "qPrime recovers q.")),
                    Paragraph(Text(
                        "Repository search found only self-map and continuous variants. Pinned "
                            + "Mathlib supplies RightInverse.surjective and "
                            + "Surjective.injective_comp_right; the proof applies both directly.")),
                    Paragraph(Text(
                        "The module compiles the identity section on Bool with Boolean negation "
                            + "as a simultaneous witness for the hypotheses and conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula quotient = Seq(F.Id("B"), Apos);
        Formula target = F.Id("B");
        Formula quotientMap = Seq(F.Id("q"), Apos);
        Formula targetMap = F.Id("q");
        Formula section = F.Id("s");
        Formula factor = F.Id("p");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula fiberConstancy = Seq(
            Open, Forall, Sp, x, Comma, Sp, y, Comma, Esc,
            Apply(quotientMap, x), Sp, Eq, Sp, Apply(quotientMap, y),
            Sp, Rightarrow, Sp,
            Apply(targetMap, x), Sp, Eq, Sp, Apply(targetMap, y), Close);

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, quotient, Comma, Sp, target, Comma, Esc,
            Forall, Sp, quotientMap, Colon, Sp, source, Sp, To, Sp, quotient,
            Comma, Sp, targetMap, Colon, Sp, source, Sp, To, Sp, target,
            Comma, Sp, section, Colon, Sp, quotient, Sp, To, Sp, source,
            Comma, Esc, fiberConstancy, Sp, Rightarrow, Sp,
            Call("RightInverse", section, quotientMap), Sp, Rightarrow, Sp,
            Exists, Bang, Sp, factor, Colon, Sp, quotient, Sp, To, Sp, target,
            Comma, Esc, targetMap, Sp, Eq, Sp, factor, Sp, Circ, Sp,
            quotientMap, Dot));
    }
}
