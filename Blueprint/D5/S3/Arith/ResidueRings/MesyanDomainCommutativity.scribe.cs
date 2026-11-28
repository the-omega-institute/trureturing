using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ResidueRings;

internal sealed class MesyanDomainCommutativityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ResidueRings/MesyanDomainCommutativity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/mesyan2026quantales");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A domain in Mesyan's sense can be noncommutative while its additive-submonoid quantale is commutative.",
        H("The domain equivalence in Mesyan's Question 34"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("domain-commutativity-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The domain clause of Question 34"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("On page 24 of the first arXiv revision, Mesyan asks, "
                        + "“For a domain R, is R being commutative equivalent to "
                        + "ℳ(R) being commutative?” Remark 14 uses domain for a nonzero semiring in which "
                        + "a product of two nonzero elements is nonzero. The semiring convention allows "
                        + "multiplication without an identity.")),
                    Paragraph(Text("Both submonoids range over all additive submonoids of R. "
                        + "Mathlib's pointwise product is the least additive submonoid containing all "
                        + "pairwise products. This is the product in Definition 4. Each generator "
                        + "is a one-term sum, sums of positive length are closed under addition, and "
                        + "the zero has a one-term representation as the product of two zero elements."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("domain-commutativity-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A noncommutative domain with commuting submonoids"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Use the basis x, y, xy of Mesyan's Example 6 over the field of "
                        + "three elements. In coordinates the product of (a, b, c) and (d, e, f) "
                        + "is (0, 0, ae − bd). Both bracketings of a triple product give the zero "
                        + "of this algebra.")),
                    Paragraph(Text("Adjoin a fresh additive identity that absorbs multiplication. "
                        + "Keep both operations on pairs of original elements. The original zero "
                        + "is distinct from the new zero, and two original elements always multiply "
                        + "to another original element. The generators (1, 0, 0) and (0, 1, 0) "
                        + "give (0, 0, 1) and (0, 0, 2) in opposite orders.")),
                    Paragraph(Text("In the extension, reversing any pairwise product gives its double. "
                        + "For any additive submonoids A and B, every generator of A times B "
                        + "is the double of a generator of B times A. Closure under addition gives "
                        + "one containment, and exchanging A and B gives the other."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);

    private static Formula Binder(Formula names, Formula type) =>
        Parenthesized(Seq(names, Sp, Colon, Sp, type));

    private static Formula Instance(string name, Formula carrier) =>
        Seq(OpenBracket, F.Id(name), Sp, carrier, CloseBracket);

    private static Formula Commutativity(string leftName, string rightName, Formula type)
    {
        Formula left = F.Id(leftName);
        Formula right = F.Id(rightName);
        return Parenthesized(Seq(Forall, Sp, Binder(Seq(left, Sp, right), type), Comma, Sp,
            left, Sp, Cdot, Sp, right, Sp, Eq, Sp, right, Sp, Cdot, Sp, left));
    }

    private static Formula ClaimBody()
    {
        Formula carrier = F.Id("R");
        Formula submonoid = Seq(F.Id("AddSubmonoid"), Sp, carrier);
        return Seq(Forall, Sp, Binder(carrier, F.Id("Type")), Sp,
            Instance("NonUnitalSemiring", carrier), Sp, Instance("Nontrivial", carrier), Sp,
            Instance("NoZeroDivisors", carrier), Comma, Sp,
            Commutativity("x", "y", carrier), Sp, Leftrightarrow, Sp,
            Commutativity("A", "B", submonoid));
    }
}
