using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class MultipleOfThreeCoincidenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/MultipleOfThreeCoincidence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/oeis2026a387319");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The modulo-three coincidence occurs exactly for composites other than 4, 8, 10, and 25.",
        H("Multiple-of-Three Residue Coincidences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a387319-coincides"),
                DeclarationHandle.Create(Prefix + "Coincides"), H("The coincidence predicate"),
                StatementSource.FromAuthor(PredicateFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural k, compare the fractions (2k mod m)/m "
                    + "at m=3 and another positive multiple of three no larger than k. "
                    + "The latter modulus is at least six. Cross multiplication is valid "
                    + "because both denominators are positive. Zero-valued coincidences "
                    + "are included, for example at k=6 and m=6."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a387319-classify"),
                DeclarationHandle.Create(Prefix + "classify"), H("The complete classification"),
                StatementSource.FromAuthor(ClassificationFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Write m=3t. Coincidence is equivalent to t dividing 2k "
                    + "and the quotient having the same residue modulo three as 2k, "
                    + "with 2<=t and 3t<=k. A divisor congruent to one modulo three "
                    + "satisfies the residue condition. Multiples of three use t=2; "
                    + "remaining even composites use t=4. For odd composites write k=pq "
                    + "with p the least prime factor. Then q>=p>=5, and take t=p "
                    + "or t=2p according to p modulo three. The latter bound fails only "
                    + "at p=q=5. For prime k the divisor criterion forces t=2 and 3|k, "
                    + "contradicting the modulus bound. The four exceptional composites "
                    + "are excluded directly. The theorem includes k=0 and k=1, for "
                    + "which both sides are false."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a387319-multiple-of-three-coincidence"),
                    ResolutionKind.Proved)))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(Formula body) =>
        Seq(Forall, Sp, V("k"), Colon, Sp, Nat(), Comma, Sp, body);
    private static Formula TwiceK() => Seq(D(2), Cdot, Sp, V("k"));
    private static Formula PredicateFormula() => Disp(All(Seq(
        Call("Coincides", V("k")), Sp, Iff, Sp,
        Par(Seq(Exists, Sp, V("m"), Colon, Sp, Nat(), Comma, Sp,
            D(6), Sp, Le, Sp, V("m"), Sp, Land, Sp,
            V("m"), Sp, Le, Sp, V("k"), Sp, Land, Sp,
            D(3), Sp, Mid, Sp, V("m"), Sp, Land, Sp,
            D(3), Cdot, Call("mod", TwiceK(), V("m")), Sp, Eq, Sp,
            V("m"), Cdot, Call("mod", TwiceK(), D(3)))))));
    private static Formula ClassificationFormula() => Disp(All(Seq(
        Call("Coincides", V("k")), Sp, Iff, Sp,
        Par(Seq(D(1), Sp, Lt, Sp, V("k"), Sp, Land, Sp,
            Neg, Call("Prime", V("k")), Sp, Land, Sp,
            Neg, Par(Seq(V("k"), Sp, InMacro, Sp, OpenBrace,
                D(4), Comma, D(8), Comma, D(1, 0), Comma, D(2, 5), CloseBrace)))))));
}
