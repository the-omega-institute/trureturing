using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class FiniteStieltjesOperatorRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite positive atomic Stieltjes moments have positive Hankel truncations and an explicit positive diagonal operator realization.",
        H("Finite Stieltjes Operator Realization"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-stieltjes-hankel-and-positive-operator-realization"),
            DeclarationHandle.Create(
                "D5/S3/Constants/FiniteStieltjesOperatorRealization."
                    + "finite_stieltjes_operator_realization"),
            H("Positive atomic moments generate Hankel and operator positivity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let I be finite, and let x and w be nonnegative real node and weight "
                        + "families. Define mu at n as the finite sum of w(i) times x(i) to "
                        + "the n-th power, and define the order-k Hankel matrix by the moment "
                        + "at p+q. Every such truncation is positive semidefinite; its zero "
                        + "coefficient vector explicitly attains equality.")),
                Paragraph(Text(
                    "On the real Euclidean space indexed by I, multiplication by x is an "
                        + "explicit diagonal nonnegative operator U. The vector v has coordinates "
                        + "sqrt(w(i)). Every moment is the inner product of U to the n-th power "
                        + "applied to v with v, and the zero state attains equality in operator "
                        + "nonnegativity.")),
                Paragraph(Text(
                    "The proof identifies each Hankel truncation with the Gram matrix of the "
                        + "vectors sqrt(w(i)) x(i)^p and applies Mathlib's Gram positivity theorem. "
                        + "It formalizes the unconditional finite positive-atomic core only; no "
                        + "Riemann-hypothesis or square-folded-xi representation is assumed or claimed."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula index = F.Id("I");
        Formula node = F.Id("x");
        Formula weight = F.Id("w");
        Formula moment = new Formula.Subscript(Mu, F.Id("n"));
        Formula hankel = new Formula.Subscript(F.Id("H"), F.Id("k"));
        Formula space = Seq(
            Mathbb, Grp(F.Id("R")), Caret, Grp(index));
        Formula op = F.Id("U");
        Formula vector = F.Id("v");
        Formula state = F.Id("y");
        Formula pairing = Seq(
            Langle, Sp, Apply(op, state), Comma, Sp, state, Rangle);
        Formula momentPairing = Seq(
            Langle, Sp, Apply(new Formula.Power(op, F.Id("n")), vector),
            Comma, Sp, vector, Rangle);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, index, Comma, Sp,
            Call("Finite", index), Comma, Sp,
            node, Comma, Sp, weight, Colon, Sp,
            index, Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak, Grp(),
            Open, Forall, Sp, F.Id("i"), Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(node, F.Id("i")), Sp, Land, Sp,
            D(0), Sp, Leq, Sp, Apply(weight, F.Id("i")), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Open, moment, Sp, Eq, Sp,
            Call("sum", F.Id("i"), Seq(
                Apply(weight, F.Id("i")), Sp, Times, Sp,
                new Formula.Power(Apply(node, F.Id("i")), F.Id("n")))), Close,
            Comma, Sp,
            Open, hankel, Open, F.Id("p"), Comma, Sp, F.Id("q"), Close,
            Sp, Eq, Sp, new Formula.Subscript(Mu,
                Seq(F.Id("p"), Sp, Plus, Sp, F.Id("q"))), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Open, Forall, Sp, F.Id("k"), Comma, Sp,
            Call("PosSemidef", hankel), Sp, Land, Sp,
            Call("q", hankel, D(0)), Sp, Eq, Sp, D(0), Close,
            Sp, Land, RowBreak, Grp(),
            Exists, Sp, op, Colon, Sp, Call("End", space), Comma, Sp,
            vector, Colon, Sp, space, Comma, Sp,
            Open, Forall, Sp, state, Comma, Sp, D(0), Sp, Leq, Sp, pairing, Close,
            Sp, Land, Sp,
            Seq(Langle, Sp, Apply(op, D(0)), Comma, Sp, D(0), Rangle),
            Sp, Eq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, state, Comma, Sp, F.Id("i"), Comma, Sp,
            Apply(Apply(op, state), F.Id("i")), Sp, Eq, Sp,
            Apply(node, F.Id("i")), Apply(state, F.Id("i")), Close,
            Sp, Land, Sp,
            Open, Forall, Sp, F.Id("n"), Comma, Sp,
            moment, Sp, Eq, Sp, momentPairing, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
