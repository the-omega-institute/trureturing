using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class CyclotomicFiveResidueSumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CyclotomicFiveResidueSum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/oeis2024a290322");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Units whose fifth cyclotomic value is again a unit sum to something whose "
        + "five-adic valuation is one short of the modulus.",
        H("Cyclotomic Five Residue Sums"),
        Blocks(
            Paragraph(Text(
                "Indices and values are natural numbers; reduction is natural remainder. "
                + "A residue is admissible for a modulus when it is coprime to that modulus "
                + "and the fifth cyclotomic value at it is coprime as well. The sum below "
                + "runs over the admissible residues strictly between zero and the modulus.")),
            Node("phi5", "The fifth cyclotomic value", Phi5Formula(),
                "The quartic whose roots are the primitive fifth roots of unity. It is "
                + "written out rather than taken from a cyclotomic library so that the "
                + "arithmetic below stays elementary.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("goodUnits", "The admissible residues", GoodFormula(),
                "Both coprimality conditions are required. The companion counting sequence "
                + "in the source tracks the size of this set; the statement here concerns "
                + "its weighted first moment instead.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("phi5_mod_five_eq_zero_iff", "Where the value vanishes modulo five",
                VanishFormula(),
                "Modulo five the quartic takes the value one at every residue except one, "
                + "where it vanishes. So for a power of five the admissible residues are "
                + "exactly those congruent to two, three or four.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("sum_goodUnits_five_pow", "The sum over a power of five", ClosedFormFormula(),
                "The admissible representatives are the three surviving residues shifted by "
                + "multiples of five, so the sum splits into three arithmetic progressions "
                + "with a common step. This is an exact equality, not a congruence.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("residueCount_prime", "The count at a prime", CountFormula(),
                "Over a prime field the product of the quartic with one less than the "
                + "variable is the fifth power minus one, and away from characteristic five "
                + "the value one is not a root of the quartic. The excluded units are "
                + "therefore the nontrivial fifth roots of unity, and the unit group being "
                + "cyclic makes their number a greatest common divisor. Both possible values "
                + "leave a count prime to five.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("residueCount_not_dvd_five", "The count avoids five", NotDvdFormula(),
                "Both branches of the count at a prime are prime to five, and the count is "
                + "multiplicative, so the property survives to any modulus prime to five.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("sum_goodUnits_mul_cast", "Splitting the sum", SplitFormula(),
                "The remainder theorem makes the admissible set a product, and each "
                + "admissible residue of the first factor appears once for every admissible "
                + "residue of the second. The identity is one sided and lives in the residue "
                + "ring of the first factor, where the count of the second enters as a "
                + "scalar; that is all the argument downstream needs.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("residue_sum_ne_zero", "The conjecture", MainFormula(),
                "The three preceding results give the sum, modulo the power of five in the "
                + "modulus, as a count prime to five times something whose valuation is one "
                + "short. So the valuation of the sum is exactly one short of the modulus, "
                + "and in particular the modulus does not divide it. Nothing is claimed for "
                + "moduli not divisible by five, where the sum often is a multiple.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a290322-cyclotomic-five-residue-sum"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a290322-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Phi5Formula() => Disp(Seq(
        Bound("u"), Call("phi5", U()), Sp, Eq, Sp,
        Add(Add(Add(Add(Pow(U(), D(4)), Pow(U(), D(3))), Pow(U(), D(2))), U()), D(1))));

    private static Formula GoodFormula() => Disp(Seq(
        Bound("n"), Call("goodUnits", N()), Sp, Eq, Sp,
        OpenBrace, Sp, U(), Sp, Mid, Sp, D(1), Sp, Leq, Sp, U(), Sp, Lt, Sp, N(),
        Sp, Land, Sp, Call("gcd", U(), N()), Sp, Eq, Sp, D(1),
        Sp, Land, Sp, Call("gcd", Call("phi5", U()), N()), Sp, Eq, Sp, D(1), Sp, CloseBrace));

    private static Formula VanishFormula() => Disp(Seq(
        Bound("u"), Mod(Call("phi5", U()), D(5)), Sp, Eq, Sp, D(0),
        Sp, Iff, Sp, Mod(U(), D(5)), Sp, Eq, Sp, D(1)));

    private static Formula ClosedFormFormula() => Disp(Seq(
        Bound("a"), Sum(Call("goodUnits", Pow(D(5), Add(A(), D(1))))), Sp, Eq, Sp,
        Add(Mul(D(9), Pow(D(5), A())),
            Mul(D(1, 5), Divide(Mul(Pow(D(5), A()), Sub(Pow(D(5), A()), D(1))), D(2))))));

    private static Formula CountFormula() => Disp(Seq(
        Forall, Sp, F.Id("p"), Sp, Call("prime", F.Id("p")), Comma, Sp,
        F.Id("p"), Sp, Neq, Sp, D(5), Sp, Rightarrow, Sp,
        Call("residueCount", F.Id("p")), Sp, Eq, Sp,
        Sub(F.Id("p"), Call("gcd", Sub(F.Id("p"), D(1)), D(5)))));

    private static Formula NotDvdFormula() => Disp(Seq(
        Bound("m"), Neg, Open, D(5), Sp, Mid, Sp, M(), Close, Sp, Rightarrow, Sp,
        Neg, Open, D(5), Sp, Mid, Sp, Call("residueCount", M()), Close));

    private static Formula SplitFormula() => Disp(Seq(
        Forall, Sp, M(), Comma, Sp, N(), Comma, Sp, Call("gcd", M(), N()), Sp, Eq, Sp, D(1),
        Sp, Rightarrow, Sp,
        Cast(Sum(Call("goodUnits", Mul(M(), N())))), Sp, Eq, Sp,
        Mul(Call("residueCount", N()), Cast(Sum(Call("goodUnits", M())))),
        Sp, Mathrm, Grp(F.Id("in")), Sp, Call("ZMod", M())));

    private static Formula MainFormula() => Disp(Seq(
        Bound("n"), D(2), Sp, Leq, Sp, N(), Sp, Land, Sp, D(5), Sp, Mid, Sp, N(),
        Sp, Rightarrow, Sp, Mod(Sum(Call("goodUnits", N())), N()), Sp, Neq, Sp, D(0)));

    private static Formula U() => F.Id("u");
    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula A() => F.Id("a");
    private static Formula Sum(Formula s) =>
        Seq(new Formula.Subscript(F.Sum, Seq(U(), Sp, InMacro, Sp, s)), Sp, U());
    private static Formula Bound(string name) => Seq(Forall, Sp, F.Id(name), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Comma, Sp);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Mod(Formula a, Formula b) => new Formula.Modulo(a, b);
    private static Formula Cast(Formula a) => Seq(Open, a, Close);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula Divide(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
}
