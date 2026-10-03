using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Collinear;

internal sealed class PrimeCollinearTripleCensusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-modulus census of admissible collinear triples.",
        H("Prime Collinear Triple Census"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-collinear-triple-census"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Collinear/PrimeCollinearTripleCensus.card_triples_prime"),
                H("Exact count over a prime residue field"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Prime", F.Id("p")), Sp, Implies, Sp,
                    Call("card", Call("Triple", F.Id("p"))), Sp, Eq, Sp,
                    F.Id("p"), Sp, Times, Sp, Open, F.Id("p"), Sp, Minus, Sp, D(1), Close,
                    Sp, Times, Sp, Call("choose", F.Id("p"), D(3))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An admissible triple is an unordered three-point set with distinct first and "
                    + "second coordinates and zero difference determinant. Over the field of residues "
                    + "modulo a prime p, two points determine a unique affine line. The determinant "
                    + "condition places the third point on it, and distinct second coordinates force "
                    + "a nonzero slope. Conversely, a nonzero slope, an intercept, and a three-element "
                    + "set of first coordinates determine exactly one admissible triple. Counting these "
                    + "choices gives the formula, including the empty case p=2 and the case p=3."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
}
