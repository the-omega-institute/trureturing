using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class ThreeWaySlotIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Fourier/ThreeWaySlotIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit eighteen-slot three-way encoder has an exact positive recovery readout.",
        H("Three-Way Eighteen-Slot Recovery Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("slot-weight"),
                DeclarationHandle.Create(Prefix + "slotWeight"),
                H("Positive slot weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two slot colors have weights 2/3 and 1/3, selected by the value of "
                        + "s in Fin 2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("slot-encode"),
                DeclarationHandle.Create(Prefix + "slotEncode"),
                H("The eighteen-slot encoder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For k and j in Fin 3 and s in Fin 2, the slot indexed by (k,j,s) is "
                        + "slotWeight(s) times u^(k*j+s) times x(j)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("slot-recover"),
                DeclarationHandle.Create(Prefix + "slotRecover"),
                H("The positive recovery readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The j-th recovered coordinate is one third of the sum over k and s of "
                        + "u^(-(k*j+s)) times the corresponding fine slot."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("slot-recovery"),
                DeclarationHandle.Create(Prefix + "slot_recovery"),
                H("Exact recovery of every input coordinate"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nonzero complex u and every vector x from Fin 3 to the complex "
                            + "numbers, the stated recovery readout applied to the stated encoder "
                            + "returns x at every coordinate.")),
                    Paragraph(Text(
                        "The proof cancels each inverse-power factor against its matching power, "
                            + "then sums the three copies of the two positive weights. This is the "
                            + "finite recovery identity from equations (16.11)-(16.12); it does not "
                            + "assert either slot-count lower bound or the aggregation identity CD=L."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula Arrow(Formula source, Formula target) =>
        Parenthesized(new Formula.TypeArrow(source, target));

    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Fin(byte n) => Call("Fin", D(n));

    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula TheoremFormula()
    {
        Formula u = F.Id("u");
        Formula x = F.Id("x");
        Formula j = F.Id("j");
        Formula vector = Arrow(Fin(3), Complexes);
        Formula encoded = Call("slotEncode", u, x);
        Formula recovered = Call("slotRecover", u, encoded, j);
        Formula conclusion = Eq(recovered, Apply(x, j));
        return Disp(All(u, Complexes,
            All(x, vector,
                Imp(Ne(u, Typed(D(0), Complexes)),
                    All(j, Fin(3), conclusion)))));
    }
}
