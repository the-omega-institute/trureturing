using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ResidueRings;

internal sealed class MesyanQuantaleUnitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A ring without a multiplicative identity whose additive-submonoid quantale is unital.",
        H("A quantale unit from prime residue rings"),
        Blocks(Describe.Lean(
            DescribeId.Create("mesyan-question-36-existence"),
            DeclarationHandle.Create("D5/S3/Arith/ResidueRings/MesyanQuantaleUnit.question36_exists"),
            H("Existence in Mesyan's Question 36"),
            StatementSource.FromAuthor(ExistenceStatement()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Arith/mesyan2026quantales")),
            Blocks(
                Paragraph(Text("There is a nonzero associative ring A with no two-sided multiplicative identity "
                    + "and an additive submonoid E that is a two-sided unit for multiplication with every additive "
                    + "submonoid M of A. The ring structure on the carrier A is denoted by s. In the displayed "
                    + "statement, multiplication of submonoids takes all sums of a positive finite number of "
                    + "pairwise products, with the first factor from the left submonoid and the second from the right. "
                    + "The proof identifies this product from Definition 4 with Mathlib's multiplication.")),
                Paragraph(Text("Take A to be the ring of finitely supported tuples of residues modulo the primes, "
                    + "with coordinatewise operations. The tuple supported at 2 with value one there is nonzero. "
                    + "For each candidate identity e, a prime outside its support gives a singleton-supported tuple "
                    + "on which left multiplication by e vanishes.")),
                Paragraph(Text("Take E to be the whole ring as an additive submonoid. For any r in the ring and "
                    + "a in M, the Chinese remainder theorem gives one natural number agreeing with the residues "
                    + "of r at all primes in the support of a. Multiplication by r on a therefore agrees with repeated "
                    + "addition, so every product summand lies in M. In the other direction the tuple equal to one "
                    + "on the support of a and zero elsewhere gives a one-term product for a. Commutativity supplies "
                    + "the right unit law. This settles the existence clause of Question 36. The classification clause "
                    + "is a separate question."))),
            DescribeRole.Theorem))));

    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Open, F.Id(name), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Parens(Formula body) => Seq(Open, body, Close);

    private static Formula ExistenceStatement()
    {
        Formula carrier = F.Id("A");
        Formula a = F.Id("a");
        Formula e = F.Id("e");
        Formula unit = F.Id("E");
        Formula submonoid = F.Id("M");
        Formula submonoidType = Seq(F.Id("AddSubmonoid"), Sp, carrier);
        Formula nonzero = Ex("a", carrier, Seq(a, Sp, Neq, Sp, D(0)));
        Formula failure = Seq(e, Sp, Cdot, Sp, a, Sp, Neq, Sp, a, Sp, Lor, Sp,
            a, Sp, Cdot, Sp, e, Sp, Neq, Sp, a);
        Formula noIdentity = Seq(Forall, Sp, Open, e, Colon, Sp, carrier, Close, Comma, Sp,
            Ex("a", carrier, failure));
        Formula laws = Seq(unit, Sp, Cdot, Sp, submonoid, Sp, Eq, Sp, submonoid, Sp, Land, Sp,
            submonoid, Sp, Cdot, Sp, unit, Sp, Eq, Sp, submonoid);
        Formula hasUnit = Ex("E", submonoidType,
            Seq(Forall, Sp, Open, submonoid, Colon, Sp, submonoidType, Close, Comma, Sp, laws));
        return Disp(Ex("A", F.Id("Type"), Ex("s", Seq(F.Id("NonUnitalRing"), Sp, carrier),
            Seq(Parens(nonzero), Sp, Land, Sp, Parens(Seq(Parens(noIdentity), Sp, Land, Sp, Parens(hasUnit)))))));
    }
}
