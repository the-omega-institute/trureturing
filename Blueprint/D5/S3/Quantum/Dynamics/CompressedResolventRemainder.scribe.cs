using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class CompressedResolventRemainderDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Dynamics/CompressedResolventRemainder."
            + "compressed_resolvent_remainder";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coisometric compression has a positive second-order resolvent remainder with a cubic gap bound.",
        H("Compressed Resolvent Remainder"),
        Blocks(Describe.Lean(
            DescribeId.Create("compressed-resolvent-remainder"),
            DeclarationHandle.Create(Declaration),
            H("The compressed resolvent has a positive cubic remainder"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let F be a coisometry between finite-dimensional real or complex inner-product "
                        + "spaces. Let S be self-adjoint with spectral floor a, where a is positive, "
                        + "and let the resolvent parameter u be nonnegative.")),
                Paragraph(Text(
                    "The block-diagonal part S0 is formed with the visible projection P and its "
                        + "orthogonal complement Q. Substituting the two inverse-difference identities "
                        + "into one another isolates the displayed second-order term.")),
                Paragraph(Text(
                    "Compression removes the first-order cross-block term. The remaining expression "
                        + "is an adjoint sandwich of the positive resolvent, while the two leakage "
                        + "factors and three inverse factors give the stated cubic estimate."))),
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

    private static Formula Paren(Formula value) => Seq(Open, value, Close);

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

    private static Formula Inverse(Formula value) =>
        Seq(Paren(value), Caret, Grp(Minus, D(1)));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Norm(Formula value) => new Formula.Norm(value);

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K"), source = F.Id("R"), target = F.Id("E");
        Formula f = F.Id("F"), s = F.Id("S"), a = F.Id("a"), u = F.Id("u");
        Formula p = F.Id("P"), q = F.Id("Q"), compressed = F.Id("A");
        Formula delta = F.Id("delta"), block = Subscript(s, D(0)), v = F.Id("V");
        Formula resolvent = Subscript(F.Id("R"), u);
        Formula blockResolvent = Seq(Subscript(F.Id("R"), u), Caret, Grp(D(0)));
        Formula remainder = Subscript(F.Id("D"), u);
        Formula identityR = Subscript(F.Id("I"), source);
        Formula identityE = Subscript(F.Id("I"), target);
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula fAdjoint = Adjoint(f);
        Formula compressedShift = Seq(
            compressed, Sp, Plus, Sp, u, Sp, Cdot, Sp, identityE);
        Formula compressedInverse = Inverse(compressedShift);
        Formula sourceShift = Seq(s, Sp, Plus, Sp, u, Sp, Cdot, Sp, identityR);
        Formula blockShift = Seq(block, Sp, Plus, Sp, u, Sp, Cdot, Sp, identityR);
        Formula compressedResolvent = Compose(f, resolvent, fAdjoint);
        Formula compressedDifference = Seq(
            compressedResolvent, Sp, Minus, Sp, compressedInverse);
        Formula firstOrder = Paren(Compose(blockResolvent, v, blockResolvent));
        Formula secondOrder = Compose(
            blockResolvent, v, resolvent, v, blockResolvent);
        Formula hiddenRemainder = Compose(
            compressedInverse, f, s, q, resolvent, q, s, fAdjoint,
            compressedInverse);
        Formula gapCube = Power(Paren(Seq(a, Sp, Plus, Sp, u)), D(3));

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
            Typed(a, real), Comma, Sp, Typed(u, real), Comma, RowBreak, Grp(),
            Paren(Seq(Compose(f, fAdjoint), Sp, Eq, Sp, identityE)), Sp,
            Rightarrow, Sp,
            Paren(Call("IsSelfAdjoint", s)), Sp, Rightarrow, Sp,
            Paren(Seq(D(0), Sp, Lt, Sp, a)), Sp, Rightarrow, RowBreak, Grp(),
            Paren(Seq(a, Sp, Cdot, Sp, identityR, Sp, Leq, Sp, s)), Sp,
            Rightarrow, Sp,
            Paren(Seq(D(0), Sp, Leq, Sp, u)), Sp, Rightarrow, RowBreak, Grp(),
            p, Sp, Colon, Eq, Sp, Compose(fAdjoint, f), Comma, Quad, Sp,
            q, Sp, Colon, Eq, Sp, Seq(identityR, Sp, Minus, Sp, p), Comma, RowBreak, Grp(),
            compressed, Sp, Colon, Eq, Sp, Compose(f, s, fAdjoint), Comma, Quad, Sp,
            delta, Sp, Colon, Eq, Sp, Norm(Compose(f, s, q, s, fAdjoint)),
            Comma, RowBreak, Grp(),
            block, Sp, Colon, Eq, Sp,
            Seq(Compose(p, s, p), Sp, Plus, Sp, Compose(q, s, q)),
            Comma, Quad, Sp,
            v, Sp, Colon, Eq, Sp, Seq(s, Sp, Minus, Sp, block), Comma, RowBreak, Grp(),
            resolvent, Sp, Colon, Eq, Sp, Inverse(sourceShift), Comma, Quad, Sp,
            blockResolvent, Sp, Colon, Eq, Sp, Inverse(blockShift), Comma, RowBreak, Grp(),
            remainder, Sp, Colon, Eq, Sp, compressedDifference, Comma, RowBreak, Grp(),
            Open,
            Seq(resolvent, Sp, Minus, Sp, blockResolvent), Sp, Eq, Sp,
            Minus, Open, firstOrder, Close, Sp, Plus, Sp, secondOrder,
            Close, Sp, Land, RowBreak, Grp(),
            Open,
            remainder, Sp, Eq, Sp, hiddenRemainder,
            Close, Sp, Land, RowBreak, Grp(),
            Open,
            D(0), Sp, Leq, Sp, remainder,
            Close, Sp, Land, RowBreak, Grp(),
            Open,
            Norm(remainder), Sp, Leq, Sp,
            new Formula.Fraction(delta, gapCube),
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
