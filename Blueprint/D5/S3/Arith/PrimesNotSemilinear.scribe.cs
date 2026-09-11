using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class PrimesNotSemilinearDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The natural primes together with one form a set that is not semilinear.",
        H("One Together with the Primes Is Not Semilinear"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("primes-union-one-not-semilinear"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimesNotSemilinear.primes_union_one_not_isSemilinearSet"),
                H("Nonsemilinearity of the prime set with one adjoined"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Neg,
                    F.Sp,
                    new Formula.Apply(F.Id("IsSemilinearSet"),
                    [F.Seq(F.OpenBrace, F.D(1), F.CloseBrace, F.Cup, F.Mathbb, F.Grp(F.Id("P")))])))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Arith/gilles2012unaryprimes")),
                Blocks(
                    Paragraph(Text(
                        "Here P denotes the set of prime natural numbers, and the ambient set is N. "
                        + "A semilinear subset of N has a positive period d beyond some threshold k.")),
                    Paragraph(Text(
                        "Choose a prime p greater than both k and d. Repeated translation by d "
                        + "keeps p + m*d in the set for every natural m. With m = p, this gives "
                        + "p + p*d = p*(1+d). Both factors exceed one, so this number is composite "
                        + "and exceeds one. It cannot belong to the set, contradicting periodicity."))),
                DescribeRole.Theorem))));
}
