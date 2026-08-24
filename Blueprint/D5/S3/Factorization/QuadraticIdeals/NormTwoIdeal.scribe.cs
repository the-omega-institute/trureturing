using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class NormTwoIdealDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Factorization/QuadraticIdeals/NormTwoIdeal.ideal_norm_two";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The standard two-generator ideal in the minus-five quadratic order has quotient norm two.",
        H("A Norm-Two Ideal in the Minus-Five Quadratic Order"),
        Blocks(Describe.Lean(
            DescribeId.Create("minus-five-quadratic-ideal-norm-two"),
            DeclarationHandle.Create(Declaration),
            H("The standard ideal has quotient norm two"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The carrier is exactly the quadratic order Z[sqrt(-5)]. The named ideal is "
                        + "constructed as the ideal span of 2 and 1 + sqrt(-5), matching the two "
                        + "source generators.")),
                Paragraph(Text(
                    "Evaluation at sqrt(-5) = 1 modulo two is a surjective ring homomorphism. "
                        + "Its kernel is the named ideal, so the first isomorphism theorem gives "
                        + "the displayed canonical quotient equivalence and computation rule.")),
                Paragraph(Text(
                    "Both generators therefore vanish in the quotient. Transporting cardinality "
                        + "through the equivalence to ZMod 2 proves that the quotient-cardinality "
                        + "definition of the ideal norm is two."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula ideal = F.Id("normTwoIdeal");
        Formula order = Seq(Operatorname, Grp(F.Id("QuadraticOrder")));
        Formula root = Seq(Sqrt, Grp(Minus, D(5)));
        Formula secondGenerator = Seq(D(1), Sp, Plus, Sp, root);
        Formula variable = F.Id("x");
        Formula quotientTwo = Call("IdealQuotientMk", ideal, D(2));
        Formula quotientGenerator = Call("IdealQuotientMk", ideal, secondGenerator);
        Formula quotientValue = Call("IdealQuotientMk", ideal, variable);
        Formula quotientType = Call("IdealQuotient", order, ideal);

        return Disp(Seq(
            quotientTwo, Sp, Eq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            quotientGenerator, Sp, Eq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, variable, Colon, Sp, order, Comma, Sp,
            Call("quotientEquivZModTwo", quotientValue), Sp, Eq, Sp,
            Call("residueHom", variable), Close, Sp, Land, RowBreak, Grp(),
            Call("NatCard", quotientType), Sp, Eq, Sp, D(2), Dot));
    }

}
