using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Mobius;

internal sealed class GranvikMobiusRealPartDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Mobius/GranvikMobiusRealPart.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/granvik2024a292273");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Granvik's real-part identity for the even-supported signed Mobius function.",
        H("Granvik's A292273 real-part identity"), Blocks(
            Paragraph(Text("Here N includes zero, Z denotes the integers, R the reals and C "
                + "the complex numbers. The function mu is the standard integer-valued Mobius "
                + "function ArithmeticFunction.moebius. The symbol i is Complex.I. The maps "
                + "intToReal and intToComplex are the usual coercions from Z to R and C. "
                + "The exponent n is a natural number and Re is the real part, valued in R.")),
            Entry("a", "The arithmetic definition", DefinitionFormula(),
                "The total function a has domain N and codomain Z. Its two exhaustive "
                + "clauses use the natural remainder modulo two; zero in these clauses is "
                + "an integer. At the positive indices of OEIS A292273, odd n gives zero "
                + "and even n gives minus mu(n). The extension used to define a at zero "
                + "does not add an index to the theorem's conclusion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Entry("result", "The positive-index real-part identity", ResultFormula(),
                "For every positive natural index, with no upper bound, the arithmetic "
                + "definition equals Re(mu(n) times i to the n). This is precisely Mats "
                + "Granvik's conjecture in revision 24 of A292273. Reduce the power of i "
                + "modulo four: residues one and three have zero real part, and residue "
                + "two gives minus one. In residue zero, four divides n, so n is not "
                + "squarefree and mu(n) vanishes. The proof directly uses Mathlib's "
                + "moebius_eq_zero_of_not_squarefree, squarefree_iff_prime_squarefree, "
                + "prime_two, dvd_of_mod_eq_zero, I_pow_eq_pow_mod, I_sq, I_pow_three "
                + "and mul_re, followed by arithmetic normalization. These four residue "
                + "classes partition an arbitrary input; they impose no finite cutoff. "
                + "The Collatz-trajectory interpretation elsewhere in the entry and "
                + "termination of Collatz trajectories are outside this statement.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("granvik-2024-a292273-real-part"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Entry(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("granvik-real-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Parens(Formula f) => Seq(Open, f, Close);
    private static Formula Eqn(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Implication(Formula x, Formula y) =>
        new Formula.Logic(Parens(x), FormulaLogicOperator.Implies, Parens(y));
    private static Formula AllNatural(Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
        Seq(Mathbb, Grp(F.Id("N"))), body);

    private static Formula DefinitionFormula()
    {
        Formula n = F.Id("n"), value = Call(F.Id("a"), n);
        Formula remainder = new Formula.Modulo(n, D(2));
        Formula odd = Implication(Eqn(remainder, D(1)), Eqn(value, D(0)));
        Formula even = Implication(new Formula.Relation(remainder,
            FormulaRelationOperator.NotEqual, D(1)),
            Eqn(value, new Formula.Negate(Call(Mu, n))));
        return Disp(AllNatural(new Formula.Logic(Parens(odd),
            FormulaLogicOperator.And, Parens(even))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula left = Call(Named("intToReal"), Call(F.Id("a"), n));
        Formula product = new Formula.Binary(Call(Named("intToComplex"), Call(Mu, n)),
            FormulaBinaryOperator.Multiply, new Formula.Power(F.Id("i"), n));
        return Disp(AllNatural(Implication(new Formula.Relation(D(0),
            FormulaRelationOperator.LessThan, n), Eqn(left, Call(Re, product)))));
    }
}
