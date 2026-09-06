using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class MinimalSymmetricRealizationUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal moments determine a minimal symmetric real realization up to an orthogonal intertwiner.",
        H("Minimal Symmetric Realization Uniqueness"),
        Blocks(Describe.Lean(
            DescribeId.Create("minimal-symmetric-realization-uniqueness"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Measurements/MinimalSymmetricRealizationUniqueness."
                + "minimal_symmetric_realization_uniqueness"),
            H("Orthogonal equivalence of minimal symmetric realizations"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/willems1976symmetry")),
            Blocks(
                Paragraph(Text(
                    "The spaces U, E, and W are arbitrary finite-dimensional real inner-product "
                    + "spaces. W represents the second state space. LinearMap denotes a real "
                    + "linear map, adjoint is the inner-product adjoint, and comp is composition. "
                    + "In orthonormal coordinates the adjoint is the transpose in the source formula.")),
                Paragraph(Text(
                    "IsSymmetric is imposed on both dynamics: the inner product of A x with y "
                    + "equals that of x with A y, and likewise for the second dynamics. "
                    + "The two reachableSubspace hypotheses use the frozen repository definition "
                    + "displayed below, with all nonnegative powers and all input vectors. "
                    + "LinearIsometryEquiv is a surjective linear inner-product isometry; "
                    + "toLinearMap retains its underlying linear map.")),
                new DocumentBlock.DisplayFormula(ReachableFormula()),
                Paragraph(Text(
                    "The proof sends each finite sum of iterated inputs to the same sum in "
                    + "the second realization. Symmetry and moment equality yield equality of "
                    + "the two Gram forms, hence equality of their kernels. The map descends "
                    + "through the quotient; minimality gives surjectivity on both sides. "
                    + "Increasing the generator power gives the dynamics identity, and power "
                    + "zero gives the input identity.")),
                Paragraph(Text(
                    "The literature attribution concerns minimal internally symmetric "
                    + "realizations and their invariant quadratic form. This formalization "
                    + "proves the real positive-metric case directly from moments."))),
            DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Comp(Formula left, Formula right) => Call("comp", left, right);
    private static Formula Linear(Formula source, Formula target) => Call("LinearMap", Real, source, target);
    private static Formula SpaceClasses(Formula space) => Seq(
        Call("NormedAddCommGroup", space), Comma, Sp,
        Call("InnerProductSpace", Real, space), Comma, Sp,
        Call("FiniteDimensional", Real, space));

    private static Formula TheoremFormula()
    {
        Formula u = F.Id("U"), e = F.Id("E"), w = F.Id("W");
        Formula a = F.Id("A"), b = F.Id("B"), q = F.Id("Q"), k = F.Id("k");
        Formula ap = Seq(Widetilde, Grp(a)), bp = Seq(Widetilde, Grp(b));
        Formula qmap = Call("toLinearMap", q);
        Formula moment = Parenthesized(Seq(
            Forall, Sp, Typed(k, Nat), Comma, Sp,
            Equal(Comp(Call("adjoint", b), Comp(Power(a, k), b)),
                Comp(Call("adjoint", bp), Comp(Power(ap, k), bp)))));
        Formula dynamics = Parenthesized(Equal(Comp(qmap, a), Comp(ap, qmap)));
        Formula input = Parenthesized(Equal(Comp(qmap, b), bp));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(u, Call("Type")), Comma, Sp,
                Typed(e, Call("Type")), Comma, Sp, Typed(w, Call("Type")), Comma),
            Seq(Grp(), OpenBracket, SpaceClasses(u), CloseBracket, Comma),
            Seq(Grp(), OpenBracket, SpaceClasses(e), CloseBracket, Comma),
            Seq(Grp(), OpenBracket, SpaceClasses(w), CloseBracket, Comma),
            Seq(Forall, Sp, Typed(a, Linear(e, e)), Comma, Sp,
                Typed(ap, Linear(w, w)), Comma),
            Seq(Typed(b, Linear(u, e)), Comma, Sp, Typed(bp, Linear(u, w)), Comma),
            Seq(Parenthesized(Call("IsSymmetric", a)), Sp, Implies, Sp),
            Seq(Parenthesized(Call("IsSymmetric", ap)), Sp, Implies, Sp),
            Seq(moment, Sp, Implies, Sp),
            Seq(Parenthesized(Equal(Call("reachableSubspace", a, b), Call("top"))), Sp, Implies, Sp),
            Seq(Parenthesized(Equal(Call("reachableSubspace", ap, bp), Call("top"))), Sp, Implies, Sp),
            Seq(Exists, Sp, Typed(q, Call("LinearIsometryEquiv", Real, e, w)), Comma),
            new Formula.Logic(dynamics, FormulaLogicOperator.And, input),
        ]));
    }

    private static Formula ReachableFormula()
    {
        Formula u = F.Id("U"), e = F.Id("E");
        Formula a = F.Id("A"), b = F.Id("B"), k = F.Id("k"), v = F.Id("v"), x = F.Id("x");
        Formula generator = new Formula.Apply(Power(a, k), [new Formula.Apply(b, [v])]);
        Formula directions = Seq(OpenBrace, Typed(x, e), Sp, Mid, Sp,
            Exists, Sp, Typed(k, Nat), Comma, Sp, Typed(v, u), Comma, Sp,
            Equal(x, generator), CloseBrace);
        return new Formula.Aligned([Seq(Forall, Sp, Typed(u, Call("Type")), Comma, Sp, Typed(e, Call("Type")), Comma), Seq(Grp(), OpenBracket, SpaceClasses(u), CloseBracket, Comma), Seq(Grp(), OpenBracket, SpaceClasses(e), CloseBracket, Comma), Seq(Forall, Sp, Typed(a, Linear(e, e)), Comma, Sp, Typed(b, Linear(u, e)), Comma), Equal(Call("reachableSubspace", a, b), Call("span", Real, directions))]);
    }
}
