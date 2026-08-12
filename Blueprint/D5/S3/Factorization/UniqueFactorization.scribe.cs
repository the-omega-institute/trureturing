using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class UniqueFactorizationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Apostol =
        LibraryNoteRef.Create("D5/L/apostol1976introduction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime factorization of a natural number is unique up to permutation.",
        H("Uniqueness of Prime Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-factorization-unique-up-to-permutation"),
                DeclarationHandle.Create("D5/S3/Factorization/UniqueFactorization.prime_factorization_unique"),
                H("Prime factorizations of the same number are permutations of each other"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Open, Forall, Sp, F.Id("p"), InMacro, Sp, F.Id("l"), Underscore, D(1),
                                    Comma, Esc, F.Id("p"), Esc, F.Text, Grp(F.Id("prime")), Close,
                                    Sp, Land, Sp,
                                    Open, Forall, Sp, F.Id("p"), InMacro, Sp, F.Id("l"), Underscore, D(2),
                                    Comma, Esc, F.Id("p"), Esc, F.Text, Grp(F.Id("prime")), Close,
                                    Sp, Land, Sp,
                                    Prod, Sp, F.Id("l"), Underscore, D(1), Sp, Eq, Sp,
                                    Prod, Sp, F.Id("l"), Underscore, D(2),
                                    Sp, Rightarrow, Sp,
                                    F.Id("l"), Underscore, D(1), Sp, Sim, Sp, F.Id("l"), Underscore, D(2)))),
                AssessedProvenance.FromLiterature(Apostol),
                Blocks(Paragraph(Text(
                                    "Prime factorization is unique up to rearrangement: any two finite "
                                    + "lists of prime numbers with the same product are permutations of "
                                    + "each other. This is the uniqueness half of the fundamental theorem "
                                    + "of arithmetic; the existence half is deposited separately. The "
                                    + "formal claim quantifies over two lists of naturals, requires every "
                                    + "entry of each to be prime and the two products to agree, and "
                                    + "concludes a genuine list permutation, so nothing is normalized "
                                    + "away before the comparison and the statement is not hollow. The "
                                    + "proof is a thin honest wrapper over pinned Mathlib: each list is "
                                    + "identified with the canonical prime-factor list of the common "
                                    + "product by Mathlib's canonical-list uniqueness lemma, and the two "
                                    + "identifications compose into the permutation; the deposited atom "
                                    + "asserts the truth of the statement, and this route differs from "
                                    + "the source's minimal-counterexample argument. Original "
                                    + "numerical-certificate disposition: the source theorem is a purely "
                                    + "universal uniqueness statement and contains no numerical "
                                    + "certificate."))),
                DescribeRole.Theorem
            ))));
}
