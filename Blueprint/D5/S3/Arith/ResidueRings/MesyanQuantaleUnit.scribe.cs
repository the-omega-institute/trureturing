using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ResidueRings;

internal sealed class MesyanQuantaleUnitDocument : IScribeDocumentDefinition
{
    private const string FiniteSupportSubring =
        "D5/S3/Arith/ResidueRings/MesyanQuantaleUnit.finiteSupportSubring";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A ring without a multiplicative identity whose additive-submonoid quantale is unital.",
        H("A quantale unit from prime residue rings"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-residue-direct-sum"),
                DeclarationHandle.Create(FiniteSupportSubring),
                H("The prime-residue direct sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The declaration `finiteSupportSubring` has type "
                    + "`NonUnitalSubring ((p : Nat.Primes) → ZMod (p : ℕ))`. Its carrier consists of tuples "
                    + "with only finitely many nonzero coordinates. Zero, addition, negation, and multiplication "
                    + "are inherited coordinatewise."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-residue-direct-sum-properties"),
                DeclarationHandle.Create("D5/S3/Arith/ResidueRings/MesyanQuantaleUnit.finiteSupportSubring_properties"),
                H("Identity laws for the prime-residue direct sum"),
                StatementSource.FromAuthor(DirectSumStatement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/ArithUnits/mesyan2026quantales")),
                Blocks(
                    Paragraph(Text("R is the carrier of "), Ref(FiniteSupportSubring),
                        Text(". The tuple supported at 2 with value one there is nonzero. "
                            + "For each candidate identity e, a prime outside its support gives a singleton-supported "
                            + "tuple on which left multiplication by e vanishes.")),
                    Paragraph(Text("The proof identifies Mathlib's additive-submonoid product with Definition 4 in "
                        + "Mesyan's paper. The product takes all sums of a positive finite number of pairwise products, "
                        + "with the first factor from the left submonoid and the second from the right.")),
                    Paragraph(Text("T denotes the top additive submonoid, which is the whole ring. For any r in the ring and "
                        + "a in M, the Chinese remainder theorem gives one natural number agreeing with the residues "
                        + "of r at all primes in the support of a. Multiplication by r on a therefore agrees with repeated "
                        + "addition, so every product summand lies in M. In the other direction the tuple equal to one "
                        + "on the support of a and zero elsewhere gives a one-term product for a. Commutativity supplies "
                        + "the right unit law."))),
                DescribeRole.Theorem))));

    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Open, F.Id(name), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Parens(Formula body) => Seq(Open, body, Close);

    private static Formula DirectSumStatement()
    {
        Formula carrier = F.Id("R");
        Formula a = F.Id("a");
        Formula e = F.Id("e");
        Formula unit = F.Id("T");
        Formula submonoid = F.Id("M");
        Formula submonoidType = Seq(F.Id("AddSubmonoid"), Sp, carrier);
        Formula nonzero = Ex("a", carrier, Seq(a, Sp, Neq, Sp, D(0)));
        Formula failure = Seq(e, Sp, Cdot, Sp, a, Sp, Neq, Sp, a, Sp, Lor, Sp,
            a, Sp, Cdot, Sp, e, Sp, Neq, Sp, a);
        Formula noIdentity = Seq(Forall, Sp, Open, e, Colon, Sp, carrier, Close, Comma, Sp,
            Ex("a", carrier, failure));
        Formula laws = Seq(unit, Sp, Cdot, Sp, submonoid, Sp, Eq, Sp, submonoid, Sp, Land, Sp,
            submonoid, Sp, Cdot, Sp, unit, Sp, Eq, Sp, submonoid);
        Formula topIsUnit = Seq(Forall, Sp, Open, submonoid, Colon, Sp, submonoidType, Close, Comma, Sp, laws);
        return Disp(Seq(Parens(nonzero), Sp, Land, Sp, Parens(noIdentity), Sp, Land, Sp, Parens(topIsUnit)));
    }
}
