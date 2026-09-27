using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class CompressedPowerDefectDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Dynamics/CompressedPowerDefect.compressed_power_defect";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coisometric compression has a quadratic power defect controlled by its two-step leakage.",
        H("Compressed Power Defect"),
        Blocks(Describe.Lean(
            DescribeId.Create("compressed-power-defect"),
            DeclarationHandle.Create(Declaration),
            H("Compressed powers have a binomial leakage bound"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let F be a coisometry between finite-dimensional real or complex inner-product "
                        + "spaces, and let S be a self-adjoint operator bounded in norm by b. The "
                        + "operator P = F*F is the visible projection and Q = I-P is its orthogonal "
                        + "complement.")),
                Paragraph(Text(
                    "The quadratic compression defect is exactly the path that leaves the visible "
                        + "subspace through Q and returns after the second application of S.")),
                Paragraph(Text(
                    "For every higher power, a commutator expansion controls hidden leakage at each "
                        + "possible crossing time. Iterating the resulting defect recursion sums these "
                        + "contributions to the binomial coefficient n choose 2."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typeclass(Formula proposition) =>
        Seq(OpenBracket, proposition, CloseBracket);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Clm(Formula scalar, Formula source, Formula target) =>
        Call("ContinuousLinearMap", scalar, source, target);

    private static Formula Compose(params Formula[] maps)
    {
        var items = new List<Formula>();
        for (var i = 0; i < maps.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, Circ, Sp]);
            items.Add(maps[i]);
        }

        return Seq([.. items]);
    }

    private static Formula Adjoint(Formula value) =>
        Seq(value, Caret, Grp(Star));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Norm(Formula value) => new Formula.Norm(value);

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K"), source = F.Id("R"), target = F.Id("E");
        Formula f = F.Id("F"), s = F.Id("S"), bound = F.Id("b");
        Formula p = F.Id("P"), q = F.Id("Q"), compressed = F.Id("A");
        Formula defect = F.Id("delta"), n = F.Id("n"), identity = F.Id("I");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nat = Seq(Operatorname, Grp(F.Id("Nat")));
        Formula fAdjoint = Adjoint(f);
        Formula compressedDefinition = Compose(f, s, fAdjoint);
        Formula pDefinition = Compose(fAdjoint, f);
        Formula qDefinition = Seq(identity, Sp, Minus, Sp, p);
        Formula defectOperator = Compose(f, s, q, s, fAdjoint);
        Formula secondDefect = Seq(
            Compose(f, Power(s, D(2)), fAdjoint), Sp, Minus, Sp,
            Power(compressed, D(2)));
        Formula nthDefect = Seq(
            Compose(f, Power(s, n), fAdjoint), Sp, Minus, Sp,
            Power(compressed, n));
        Formula coefficient = Call("choose", n, D(2));
        Formula exponent = Grp(n, Sp, Minus, Sp, D(2));
        Formula estimate = Seq(
            Norm(nthDefect), Sp, Leq, Sp,
            coefficient, Sp, Cdot, Sp, Power(bound, exponent), Sp, Cdot, Sp, defect);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, source, Comma, Sp, target,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            Typeclass(Call("RCLike", scalar)), Comma, Sp,
            Typeclass(Call("NormedAddCommGroup", source)), Comma, Sp,
            Typeclass(Call("InnerProductSpace", scalar, source)), Comma, Sp,
            Typeclass(Call("FiniteDimensional", scalar, source)), Comma, RowBreak, Grp(),
            Typeclass(Call("NormedAddCommGroup", target)), Comma, Sp,
            Typeclass(Call("InnerProductSpace", scalar, target)), Comma, Sp,
            Typeclass(Call("FiniteDimensional", scalar, target)), Comma, RowBreak, Grp(),
            Typed(f, Clm(scalar, source, target)), Comma, Sp,
            Typed(s, Clm(scalar, source, source)), Comma, Sp,
            Typed(bound, real), Comma, RowBreak, Grp(),
            Compose(f, fAdjoint), Sp, Eq, Sp, identity, Sp, Rightarrow, Sp,
            Call("IsSelfAdjoint", s), Sp, Rightarrow, Sp,
            Norm(s), Sp, Leq, Sp, bound, Sp, Rightarrow, RowBreak, Grp(),
            p, Sp, Colon, Eq, Sp, pDefinition, Comma, Quad, Sp,
            q, Sp, Colon, Eq, Sp, qDefinition, Comma, RowBreak, Grp(),
            compressed, Sp, Colon, Eq, Sp, compressedDefinition, Comma, Quad, Sp,
            defect, Sp, Colon, Eq, Sp, Norm(defectOperator), Comma, RowBreak, Grp(),
            Open,
            secondDefect, Sp, Eq, Sp, defectOperator,
            Close, Sp, Land, RowBreak, Grp(),
            Open,
            Forall, Sp, Typed(n, nat), Comma, Sp,
            D(2), Sp, Leq, Sp, n, Sp, Rightarrow, Sp, estimate,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
